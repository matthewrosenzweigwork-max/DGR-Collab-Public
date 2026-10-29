import SharpSymmetricLSI.Paper.Defective12
import SharpSymmetricLSI.Paper.TorusLSI
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.H1Config

/-!
# R03 (Proposition 2.2), part 13: it suffices to treat bounded functions bounded below

For `f ∈ H¹(P_N)`, `regF n f = ψ_n ∘ f` is in `H¹(P_N)`, takes values in `[1/(n+1), n+2]`, has energy
at most `ℰ_N(f)`, is symmetric when `f` is, and `∫ (regF n f)² dP_N → ∫ f² dP_N`,
`Ent(f²) ≤ liminf Ent((regF n f)²)`. Hence a defective inequality for all `regF n f` implies it for
`f` (`defective_of_regF`).
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The regularization `ψ_n ∘ f`. -/
noncomputable def regF {N : ℕ} (n : ℕ) (f : Config N d → ℝ) : Config N d → ℝ := fun X => psiReg n (f X)

section reg
variable (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f)
include hyp hf

theorem isWeakGrad_regF (n : ℕ) :
    IsWeakGrad (regF n f ∘ unflat)
      (fun y k => deriv (psiReg n) (f (unflat y)) * weakGrad (f ∘ unflat) y k) := by
  obtain ⟨hw, hi, hgi⟩ := memH1C_data hyp hf
  exact isWeakGrad_comp hw hi hgi (contDiff_psiReg n) (abs_deriv_psiReg_le n)

theorem memH1C_regF (n : ℕ) : MemH1C (gibbs V W N) (regF n f) := by
  haveI := gibbs_isProbabilityMeasure hyp N
  have hw := isWeakGrad_regF hyp hf n
  have hac := (gibbs_map_flat_ac hyp N).1
  have hfm := (memH1C_data hyp hf).2.1.aestronglyMeasurable
  refine ⟨⟨_, hw⟩, ?_, ?_⟩
  · refine MemLp.of_bound ((((contDiff_psiReg n).continuous.comp_aestronglyMeasurable hfm)).mono_ac
      hac) ((n : ℝ) + 2) (Eventually.of_forall fun y => ?_)
    simp only [Real.norm_eq_abs, Function.comp_apply, regF]
    rw [abs_of_pos (lt_of_lt_of_le (by positivity) (psiReg_ge n _))]
    exact psiReg_le n _
  · refine hf.2.2.of_le ((Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨_, hw⟩).aestronglyMeasurable_sqNorm).mono_ac hac) ?_
    filter_upwards [hac.ae_le (weakGrad_ae_eq hw)] with y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _), hy]
    refine Real.sqrt_le_sqrt ?_
    unfold sqNorm
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_pow]
    have h1 : deriv (psiReg n) (f (unflat y)) ^ 2 ≤ 1 := by
      have := abs_deriv_psiReg_le n (f (unflat y))
      rw [← sq_abs]; nlinarith [abs_nonneg (deriv (psiReg n) (f (unflat y)))]
    nlinarith [sq_nonneg (weakGrad (f ∘ unflat) y k)]

theorem energy_regF_le (n : ℕ) : energy V W N (regF n f) ≤ energy V W N f := by
  have hw := isWeakGrad_regF hyp hf n
  have hac := (gibbs_map_flat_ac hyp N).1
  rw [energy_eq hyp ⟨_, hw⟩, energy_eq hyp hf.1]
  refine lintegral_mono_ae ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq hw)] with y hy
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hy]
  unfold sqNorm
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_pow]
  have h1 : deriv (psiReg n) (f (unflat y)) ^ 2 ≤ 1 := by
    have := abs_deriv_psiReg_le n (f (unflat y))
    rw [← sq_abs]; nlinarith [abs_nonneg (deriv (psiReg n) (f (unflat y)))]
  nlinarith [sq_nonneg (weakGrad (f ∘ unflat) y k)]

omit hf in
theorem isSymmetric_regF (n : ℕ) (hs : IsSymmetric f) : IsSymmetric (regF n f) := fun σ X => by
  simp only [regF, hs σ X]

theorem tendsto_lintegral_regF_sq :
    Tendsto (fun n => ∫⁻ X, ENNReal.ofReal (regF n f X ^ 2) ∂gibbs V W N) atTop
      (𝓝 (∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N)) := by
  haveI := gibbs_isProbabilityMeasure hyp N
  have hf2 := memLp_of_memH1C hyp hf
  have hfm : AEMeasurable f (gibbs V W N) := hf2.aestronglyMeasurable.aemeasurable
  refine tendsto_lintegral_of_dominated_convergence' (bound := fun X => ENNReal.ofReal (f X ^ 2 + 1))
    (fun n => ENNReal.measurable_ofReal.comp_aemeasurable
      (((contDiff_psiReg n).continuous.measurable.comp_aemeasurable hfm).pow_const 2))
    (fun n => Eventually.of_forall fun X => ENNReal.ofReal_le_ofReal (psiReg_sq_le n (f X))) ?_
    (Eventually.of_forall fun X => (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_psiReg_sq (f X)))
  exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt
    (hf2.integrable_sq.add (integrable_const 1)).hasFiniteIntegral).ne

theorem ent_le_liminf_regF :
    ent (gibbs V W N) (fun X => f X ^ 2) ≤
      liminf (fun n => ent (gibbs V W N) (fun X => regF n f X ^ 2)) atTop := by
  haveI := gibbs_isProbabilityMeasure hyp N
  have hf2 := memLp_of_memH1C hyp hf
  have hfm : AEMeasurable f (gibbs V W N) := hf2.aestronglyMeasurable.aemeasurable
  have hFi : ∀ n, Integrable (fun X => regF n f X ^ 2) (gibbs V W N) := fun n =>
    Integrable.of_bound (((contDiff_psiReg n).continuous.measurable.comp_aemeasurable hfm).pow_const 2
      |>.aestronglyMeasurable) (((n : ℝ) + 2) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (le_trans (by positivity) (psiReg_ge n _)) (psiReg_le n _) 2)
  have hlim0 : ∀ᵐ X ∂gibbs V W N, Tendsto (fun n => regF n f X ^ 2) atTop (𝓝 (f X ^ 2)) :=
    Eventually.of_forall fun X => tendsto_psiReg_sq (f X)
  refine ent_le_liminf (F := fun n X => regF n f X ^ 2) (f := fun X => f X ^ 2) hFi
    hf2.integrable_sq hlim0 ?_
  have hbd : ∀ n, ∀ᵐ X ∂gibbs V W N, ‖regF n f X ^ 2‖ ≤ f X ^ 2 + 1 := fun n =>
    Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact psiReg_sq_le n (f X)
  have hlim : ∀ᵐ X ∂gibbs V W N, Tendsto (fun n => regF n f X ^ 2) atTop (𝓝 (f X ^ 2)) :=
    Eventually.of_forall fun X => tendsto_psiReg_sq (f X)
  have hint : Integrable (fun X => f X ^ 2 + 1) (gibbs V W N) :=
    hf2.integrable_sq.add (integrable_const 1)
  have hm : ∀ n, AEStronglyMeasurable (fun X => regF n f X ^ 2) (gibbs V W N) := fun n =>
    (hFi n).aestronglyMeasurable
  have h := tendsto_integral_of_dominated_convergence (F := fun n X => regF n f X ^ 2)
    (f := fun X => f X ^ 2) (fun X => f X ^ 2 + 1) hm hint hbd hlim
  simpa using h

/-- **Reduction to bounded functions bounded below.** -/
theorem defective_of_regF {a B : ℝ}
    (hreg : ∀ n, ent (gibbs V W N) (fun X => regF n f X ^ 2) ≤
      ENNReal.ofReal a * energy V W N (regF n f) +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (regF n f X ^ 2) ∂gibbs V W N) :
    ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal a * energy V W N f +
      ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := by
  have hb : Tendsto (fun n => ENNReal.ofReal a * energy V W N f +
      ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (regF n f X ^ 2) ∂gibbs V W N) atTop
      (𝓝 (ENNReal.ofReal a * energy V W N f +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul (tendsto_lintegral_regF_sq hyp hf)
      (Or.inr ENNReal.ofReal_ne_top))
  calc ent (gibbs V W N) (fun X => f X ^ 2)
      ≤ liminf (fun n => ent (gibbs V W N) (fun X => regF n f X ^ 2)) atTop :=
        ent_le_liminf_regF hyp hf
    _ ≤ liminf (fun n => ENNReal.ofReal a * energy V W N f +
          ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (regF n f X ^ 2) ∂gibbs V W N) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => (hreg n).trans
          (add_le_add (mul_le_mul' le_rfl (energy_regF_le hyp hf n)) le_rfl))
    _ = _ := hb.liminf_eq

end reg

end SharpLSI
