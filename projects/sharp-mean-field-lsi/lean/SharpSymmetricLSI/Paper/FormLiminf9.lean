import SharpSymmetricLSI.Paper.FormLiminf8
import SharpSymmetricLSI.Paper.R7Basic

/-!
# R33 (8.20): `H¹(P_N)` functions are in `W^{1,1}(𝕋^{N×d})`

`vol ≤ C·P_N` (densities bounded below), so `f ∈ H¹(P_N)` gives `f ∘ unflat` and its weak gradient
in `L²(vol)`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- `vol ≤ C · P_N` on `(𝕋^d)^N`. -/
theorem volume_le_smul_gibbs (N : ℕ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    (volume : Measure (Config N d)) ≤ C • gibbs V W N := by
  obtain ⟨c, Cu, L, hc, hbd⟩ := elDensity_bounds hyp
  obtain ⟨hb, -⟩ := hbd (μ : Measure (Torus d)) inferInstance
  set p := elDens V W (μ : Measure (Torus d))
  have hp0 : ∀ x, 0 ≤ p x := fun x => hc.le.trans (hb x).1
  have hpm : Measurable p := (elDensity_props hyp (μ : Measure (Torus d))).1
  have hpi : Integrable p (haar d) := integrable_of_bdd hpm (C := Cu) fun x => by
    rw [abs_of_nonneg (hp0 x)]; exact (hb x).2
  have hμp : (μ : Measure (Torus d)) = (haar d).withDensity (fun x => ENNReal.ofReal (p x)) :=
    minimizer_eq_elDensity hyp hμ
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp (μ : Measure (Torus d)) N
  have hK := centeredPartition_pos hyp (μ : Measure (Torus d)) N
  set wmin : ℝ := rexp (-BU) / centeredPartition W μ N
  have hwmin : 0 < wmin := div_pos (exp_pos _) hK
  set a : ℝ≥0∞ := ENNReal.ofReal (wmin * c ^ N)
  have ha0 : a ≠ 0 := by
    simp only [a, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  -- `a · vol ≤ P_N`
  have hlow : a • (volume : Measure (Config N d)) ≤ gibbs V W N := by
    have hm1 : Measurable fun X : Config N d => ENNReal.ofReal (∏ i, p (X i)) :=
      ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => hpm.comp
        (measurable_pi_apply i))
    have hm2 : Measurable fun X : Config N d =>
        ENNReal.ofReal (rexp (-Ucentered W μ N X) / centeredPartition W μ N) :=
      ENNReal.measurable_ofReal.comp
        (((measurable_Ucentered hyp (μ : Measure (Torus d)) N).neg.exp).div_const _)
    have hpiμ : Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        (volume : Measure (Config N d)).withDensity (fun X => ENNReal.ofReal (∏ i, p (X i))) := by
      rw [hμp]; exact pi_withDensity_ofReal hpm hp0 hpi
    rw [gibbs_eq_centered_aux hyp hμ N, hpiμ, ← withDensity_mul _ hm1 hm2, ← withDensity_const]
    refine withDensity_mono (Eventually.of_forall fun X => ?_)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hp0 _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : c ^ N ≤ ∏ i, p (X i) := by
      calc c ^ N = ∏ _i : Fin N, c := by simp
        _ ≤ ∏ i, p (X i) := Finset.prod_le_prod₀ (fun i _ => hc.le) fun i _ => (hb _).1
    have h2 : wmin ≤ rexp (-Ucentered W μ N X) / centeredPartition W μ N := by
      refine div_le_div_of_nonneg_right (exp_le_exp.2 ?_) hK.le
      have := hBU X; rw [abs_le] at this; linarith
    calc wmin * c ^ N ≤ rexp (-Ucentered W μ N X) / centeredPartition W μ N * ∏ i, p (X i) :=
          mul_le_mul h2 h1 (by positivity) (div_nonneg (exp_pos _).le hK.le)
      _ = (∏ i, p (X i)) * (rexp (-Ucentered W μ N X) / centeredPartition W μ N) := mul_comm _ _
  refine ⟨a⁻¹, ENNReal.inv_ne_top.2 ha0, ?_⟩
  calc (volume : Measure (Config N d)) = a⁻¹ • (a • volume) := by
        rw [smul_smul, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_smul]
    _ ≤ a⁻¹ • gibbs V W N := by
        intro s
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact hlow s

/-- The flat version. -/
theorem volume_le_smul_gibbs_flat_fl (N : ℕ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    (volume : Measure (UnitAddTorus (Fin N × Fin d))) ≤ C • (gibbs V W N).map flat := by
  obtain ⟨C, hC, hle⟩ := volume_le_smul_gibbs hyp hμ N
  refine ⟨C, hC, ?_⟩
  rw [← map_flat_volume N, ← Measure.map_smul]
  exact Measure.map_mono hle measurable_flat
  all_goals exact measurable_flat.aemeasurable

/-- **`H¹(P_N) ⊂ W^{1,1}(vol)`**, with the weak gradient. -/
theorem memH1C_gibbs_W11 {N : ℕ} {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    IsWeakGrad (f ∘ unflat) (weakGrad (f ∘ unflat)) ∧ Integrable (f ∘ unflat) volume ∧
      ∀ p, Integrable (fun y => weakGrad (f ∘ unflat) y p) volume := by
  obtain ⟨C, hC, hle⟩ := volume_le_smul_gibbs_flat_fl hyp hμ N
  have hw := isWeakGrad_weakGrad hf.1
  refine ⟨hw, (hf.2.1.of_measure_le_smul hC hle).integrable one_le_two, fun p => ?_⟩
  have h2 := hf.2.2.of_measure_le_smul hC hle
  refine (MemLp.of_le h2 (hw.aestronglyMeasurable_grad p) (Eventually.of_forall fun y => ?_)).integrable
    one_le_two
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  unfold sqNorm
  exact Finset.single_le_sum (f := fun q => weakGrad (f ∘ unflat) y q ^ 2)
    (fun q _ => sq_nonneg _) (Finset.mem_univ p)

end

end SharpLSI
