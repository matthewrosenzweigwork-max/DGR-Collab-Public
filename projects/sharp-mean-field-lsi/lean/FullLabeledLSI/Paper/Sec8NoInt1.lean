import FullLabeledLSI.Paper.Sec8Mollify
import FullLabeledLSI.Infra.HypercontrTorus3
import SharpSymmetricLSI.Paper.Defective13
import SharpSymmetricLSI.Paper.NBody2

/-!
# Section 8.5: the product logarithmic Sobolev inequality on `H^1(μ^{⊗N})`

If `P_N = μ^{⊗N}` and `μ ≪ m` has `a ≤ r_LS(μ)`, then `Ent_{P_N}(f²) ≤ (2/a) ℰ_N(f)` for every
`f ∈ H^1(P_N)`.  The `C¹` product inequality `torus_lsi_refEnergy` is extended to `H^1` by
mollification (`exists_smooth_seq_gen`) and the bounded regularization `regF`.
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal ContDiff

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem volume_le_smul_flat (hyp : Hyp V W KV KW) (N : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (volume : Measure (UnitAddTorus (Fin N × Fin d))) ≤ C • (gibbs V W N).map flat := by
  obtain ⟨C, hC, h⟩ := lintegral_haar_le_gibbs hyp N
  refine ⟨C, hC, Measure.le_iff.mpr fun s hs => ?_⟩
  have := h (s.indicator 1) (aemeasurable_const.indicator hs)
  simpa [lintegral_indicator_one hs] using this

theorem dirichlet_lt_top_gen {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Measure (UnitAddTorus ι)}
    [IsFiniteMeasure P] {f : UnitAddTorus ι → ℝ} (h : MemH1 P f) : dirichlet P f < ⊤ := by
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad f x))) P :=
    h.2.2.aestronglyMeasurable
  have := (memLp_two_iff_integrable_sq hm).1 h.2.2
  unfold dirichlet
  have h2 := this.2
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)] at h2
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [Real.sq_sqrt (sqNorm_nonneg _)]

theorem ent_regF_le_aux (hyp : Hyp V W KV KW) {N : ℕ} {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hgp : gibbs V W N = Measure.pi fun _ : Fin N => μ)
    (hac : μ ≪ volume) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS μ)
    {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) (m : ℕ) :
    ent (gibbs V W N) (fun X => regF m f X ^ 2) ≤
      ENNReal.ofReal (2 / a) * energy V W N f := by
  haveI hPp : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N with hP
  set Q : Measure (UnitAddTorus (Fin N × Fin d)) := P.map flat with hQ
  haveI : IsProbabilityMeasure Q := ⟨by
    rw [hQ, Measure.map_apply measurable_flat MeasurableSet.univ]; simp⟩
  have hQac : Q ≪ volume := (gibbs_map_flat_ac hyp N).1
  obtain ⟨C1, hC1, hle1⟩ := gibbs_map_flat_le hyp N
  obtain ⟨C2, hC2, hle2⟩ := volume_le_smul_flat hyp N
  obtain ⟨s, hs, -, hdir, hae⟩ := exists_smooth_seq_gen hC1 hC2 hle1 hle2 (h := f ∘ unflat) hf
  have hf2 := memLp_of_memH1C hyp hf
  have hfm : AEMeasurable f P := hf2.aestronglyMeasurable.aemeasurable
  have hc : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  set F : ℕ → Config N d → ℝ := fun n X => s n (flat X) with hF
  have hFunf : ∀ n, F n ∘ unflat = s n := fun n => rfl
  set G : ℕ → Config N d → ℝ := fun n => regF m (F n) with hG
  have hG1 : ∀ n, Gross.C1C (G n) := fun n =>
    Gross.C1T.comp (ContDiff.of_le (hs n) (by simp)) (contDiff_psiReg m)
  have hGlo : ∀ n X, 1 / ((m : ℝ) + 1) ≤ G n X := fun n X => psiReg_ge m _
  have hGhi : ∀ n X, G n X ≤ (m : ℝ) + 2 := fun n X => psiReg_le m _
  have hFH : ∀ n, MemH1C P (F n) := fun n => by
    show MemH1 Q (F n ∘ unflat)
    rw [hFunf]
    exact memH1_of_contDiff_ac hQac (ContDiff.of_le (hs n) (by simp))
  have hEF : ∀ n, energy V W N (F n) = dirichlet Q (s n) := fun n => by
    rw [energy_eq_dirichlet hyp (hFH n).1, hFunf]
  have hEf : energy V W N f = dirichlet Q (f ∘ unflat) := energy_eq_dirichlet hyp hf.1
  have hent : ∀ n, ent P (fun X => G n X ^ 2) ≤ ENNReal.ofReal (2 / a) * dirichlet Q (s n) := by
    intro n
    have hlsi := Gross.torus_lsi_refEnergy hac ha hrls (hG1 n) hc (hGlo n) (hGhi n)
    have hGm : Measurable (G n) := Gross.C1C.measurable (hG1 n)
    have e1 : ent P (fun X => G n X ^ 2) = ENNReal.ofReal (entR (Measure.pi fun _ : Fin N => μ)
        (fun X => G n X ^ 2)) := by
      show ent P _ = _
      rw [hgp]
      haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin N => μ) := inferInstance
      exact ent_eq_ofReal_entR (hGm.pow_const 2) (c := (1 / ((m : ℝ) + 1)) ^ 2) (by positivity)
        (fun X => pow_le_pow_left₀ hc.le (hGlo n X) 2) (C := ((m : ℝ) + 2) ^ 2)
        (fun X => pow_le_pow_left₀ (hc.le.trans (hGlo n X)) (hGhi n X) 2)
    have hRE : refEnergy μ (G n) = energy V W N (G n) := by
      unfold refEnergy energy; rw [← hP, hgp]
    have hEle : energy V W N (G n) ≤ energy V W N (F n) := energy_regF_le hyp (hFH n) m
    have hEfin : energy V W N (F n) ≠ ⊤ := by
      rw [hEF]
      exact (dirichlet_lt_top_gen (memH1_of_contDiff_ac hQac (ContDiff.of_le (hs n) (by simp)))).ne
    have hGfin : (refEnergy μ (G n)) ≠ ⊤ := by
      rw [hRE]; exact ne_top_of_le_ne_top hEfin hEle
    rw [e1]
    have h2 : entR (Measure.pi fun _ : Fin N => μ) (fun X => G n X ^ 2) ≤
        2 / a * (refEnergy μ (G n)).toReal := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]; linarith
    calc ENNReal.ofReal (entR (Measure.pi fun _ : Fin N => μ) (fun X => G n X ^ 2))
        ≤ ENNReal.ofReal (2 / a * (refEnergy μ (G n)).toReal) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (2 / a) * refEnergy μ (G n) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hGfin]
      _ ≤ ENNReal.ofReal (2 / a) * dirichlet Q (s n) := by
          rw [hRE, ← hEF n]; exact mul_le_mul' le_rfl hEle
  -- the limit
  have hPae : ∀ᵐ X ∂P, Tendsto (fun n => F n X) atTop (𝓝 (f X)) :=
    ae_of_ae_map measurable_flat.aemeasurable hae
  have hsqm : ∀ n, Measurable fun X => G n X ^ 2 := fun n =>
    (Gross.C1C.measurable (hG1 n)).pow_const 2
  have hbd : ∀ n, ∀ᵐ X ∂P, ‖G n X ^ 2‖ ≤ ((m : ℝ) + 2) ^ 2 := fun n =>
    Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hc.le.trans (hGlo n X)) (hGhi n X) 2
  have hFi : ∀ n, Integrable (fun X => G n X ^ 2) P := fun n =>
    Integrable.of_bound (hsqm n).aestronglyMeasurable _ (hbd n)
  have hrm : AEMeasurable (fun X => regF m f X ^ 2) P :=
    ((contDiff_psiReg m).continuous.measurable.comp_aemeasurable hfm).pow_const 2
  have hrbd : ∀ᵐ X ∂P, ‖regF m f X ^ 2‖ ≤ ((m : ℝ) + 2) ^ 2 := Eventually.of_forall fun X => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hc.le.trans (psiReg_ge m _)) (psiReg_le m _) 2
  have hfi : Integrable (fun X => regF m f X ^ 2) P :=
    Integrable.of_bound hrm.aestronglyMeasurable _ hrbd
  have hlim : ∀ᵐ X ∂P, Tendsto (fun n => G n X ^ 2) atTop (𝓝 (regF m f X ^ 2)) := by
    filter_upwards [hPae] with X hX
    exact (((contDiff_psiReg m).continuous.tendsto _).comp hX).pow 2
  have hint : Tendsto (fun n => ∫ X, G n X ^ 2 ∂P) atTop (𝓝 (∫ X, regF m f X ^ 2 ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ((m : ℝ) + 2) ^ 2)
      (fun n => (hsqm n).aestronglyMeasurable) (integrable_const _) hbd hlim
  have hle := ent_le_liminf hFi hfi hlim hint
  have hb : Tendsto (fun n => ENNReal.ofReal (2 / a) * dirichlet Q (s n)) atTop
      (𝓝 (ENNReal.ofReal (2 / a) * dirichlet Q (f ∘ unflat))) :=
    ENNReal.Tendsto.const_mul hdir (Or.inr ENNReal.ofReal_ne_top)
  calc ent P (fun X => regF m f X ^ 2) ≤ liminf (fun n => ent P (fun X => G n X ^ 2)) atTop := hle
    _ ≤ liminf (fun n => ENNReal.ofReal (2 / a) * dirichlet Q (s n)) atTop :=
        liminf_le_liminf (Eventually.of_forall hent)
    _ = ENNReal.ofReal (2 / a) * dirichlet Q (f ∘ unflat) := hb.liminf_eq
    _ = _ := by rw [hEf]

end Sec8
end SharpLSI.FL
