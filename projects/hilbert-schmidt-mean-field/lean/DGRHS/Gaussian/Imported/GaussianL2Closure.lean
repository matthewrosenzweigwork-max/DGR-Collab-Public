/-
Modified narrow Apache-2.0 StatLean/Stat-Lean port.
Upstream revision: 86b3823f77fc2b0f5a9923f85b588a4f8a65f94c
Upstream path: StatLean/AsymptoticStatistics/ForMathlib/Probability/GaussianL2Closure.lean
Upstream SHA-256: 853656b9f5fb7442455004f8c56b9c6b0d612a9a3b8c71024b078c3417d62c6c
Only centered scalar L2 closure is ported. Its characteristic-function proof is
factored as an explicit lemma; a.e. measurability is supplied to the pinned
Gaussian constructor, and an exact centered pushforward export is added.
Untouched original source: records/gaussian/upstream-originals; see Imported/LICENSE.
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import DGRHS.Gaussian.Imported.IsonormalProcess

/-!
# Gaussian laws under L² closure and measure-preserving transport

Reusable closure and transport lemmas for Gaussian random elements.
-/

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

/-! A local closure brick: a centred Gaussian sequence converging in `L²`
has a centred Gaussian limit.  This is the scalar ingredient needed because
the regression part of an influence function generally lies only in the
closed, rather than algebraic, span of the bridge coordinates. -/

/-- The centered Gaussian characteristic function persists under an actual L2 limit. -/
theorem charFun_map_of_centered_tendsto_L2
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY_gauss : ∀ n, HasGaussianLaw (Y n : S → ℝ) μ)
    (hY_mean : ∀ n, ∫ x, (Y n : S → ℝ) x ∂μ = 0)
    (hYZ : Tendsto Y atTop (nhds Z)) (t : ℝ) :
    charFun (μ.map (Z : S → ℝ)) t =
      Complex.exp (((-(‖Z‖ ^ 2 * t ^ 2) / 2 : ℝ) : ℂ)) := by
  classical
  have hmeas : TendstoInMeasure μ (fun n => (Y n : S → ℝ)) atTop (Z : S → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp hYZ
  have hZmeas : AEMeasurable (Z : S → ℝ) μ := (Lp.aestronglyMeasurable Z).aemeasurable
  have hcf : ∀ (W : S → ℝ) (t : ℝ), AEMeasurable W μ →
      charFun (μ.map W) t = ∫ x, Complex.exp (↑(t * W x) * Complex.I) ∂μ := by
    intro W t hW
    rw [charFun_apply, integral_map hW (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with x
    norm_cast
  have hA : Tendsto (fun n => charFun (μ.map (Y n : S → ℝ)) t) atTop
      (nhds (charFun (μ.map (Z : S → ℝ)) t)) := by
    have hgcont : Continuous (fun z : ℝ => Complex.exp (↑(t * z) * Complex.I)) := by
      fun_prop
    have hgb : ∀ z : ℝ, ‖Complex.exp (↑(t * z) * Complex.I)‖ ≤ 1 := by
      intro z
      rw [Complex.norm_exp]
      simp [mul_comm, Complex.I_re, Complex.I_im]
    have hconv := IsonormalProcess.tendsto_integral_comp_of_tendstoInMeasure
      (fun n => (hY_gauss n).aemeasurable) hmeas hgcont hgb
    simpa only [hcf _ t (hY_gauss _).aemeasurable, hcf _ t hZmeas] using hconv
  have hform : ∀ n, charFun (μ.map (Y n : S → ℝ)) t =
      Complex.exp ((↑(-(t ^ 2 * ‖Y n‖ ^ 2) / 2 : ℝ) : ℂ)) := by
    intro n
    rw [(hY_gauss n).charFun_map_eq t]
    have hinner : (fun x => (⟪t, (Y n : S → ℝ) x⟫_ℝ : ℝ)) =
        fun x => t * (Y n : S → ℝ) x := by
      funext x
      change (Y n : S → ℝ) x * t = t * (Y n : S → ℝ) x
      ring
    rw [hinner, integral_const_mul, hY_mean n, mul_zero,
      variance_const_mul]
    have hvar : Var[(Y n : S → ℝ); μ] = ‖Y n‖ ^ 2 := by
      rw [variance_of_integral_eq_zero
        (Lp.aestronglyMeasurable (Y n)).aemeasurable (hY_mean n),
        ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    rw [hvar]
    push_cast
    ring_nf
  refine tendsto_nhds_unique hA ?_
  rw [Filter.tendsto_congr hform]
  refine (Complex.continuous_exp.tendsto _).comp
    ((Complex.continuous_ofReal.tendsto _).comp ?_)
  have hnorm := (hYZ.norm.pow 2)
  convert (Filter.Tendsto.div_const
      (Filter.Tendsto.neg ((tendsto_const_nhds (x := t ^ 2)).mul hnorm)) 2) using 1
  all_goals ring_nf

/-- Centered scalar Gaussian L2 closure, retaining the upstream public statement. -/
theorem hasGaussianLaw_of_centered_tendsto_L2
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY_gauss : ∀ n, HasGaussianLaw (Y n : S → ℝ) μ)
    (hY_mean : ∀ n, ∫ x, (Y n : S → ℝ) x ∂μ = 0)
    (hYZ : Tendsto Y atTop (nhds Z)) :
    HasGaussianLaw (Z : S → ℝ) μ := by
  classical
  have hZmeas : AEMeasurable (Z : S → ℝ) μ := (Lp.aestronglyMeasurable Z).aemeasurable
  have hChar : ∀ t : ℝ, charFun (μ.map (Z : S → ℝ)) t =
      Complex.exp (((-(‖Z‖ ^ 2 * t ^ 2) / 2 : ℝ) : ℂ)) :=
    fun t => charFun_map_of_centered_tendsto_L2 μ Y Z hY_gauss hY_mean hYZ t
  refine ⟨hZmeas, isGaussian_iff_gaussian_charFun.mpr
    ⟨0, ‖Z‖ ^ 2 • ContinuousLinearMap.mul ℝ ℝ,
      ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, ?_⟩⟩
  · simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply', smul_eq_mul]
    ring
  · simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply', smul_eq_mul]
    exact mul_nonneg (sq_nonneg _) (mul_self_nonneg x)
  · intro t
    rw [hChar t]
    congr 1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul,
      inner_zero_right]
    push_cast
    ring

set_option backward.isDefEq.respectTransparency false in
/-- The exact pushforward keeps the zero mean and L2 norm normalization. -/
theorem map_eq_gaussianReal_of_centered_tendsto_L2
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY_gauss : ∀ n, HasGaussianLaw (Y n : S → ℝ) μ)
    (hY_mean : ∀ n, ∫ x, (Y n : S → ℝ) x ∂μ = 0)
    (hYZ : Tendsto Y atTop (nhds Z)) :
    μ.map (Z : S → ℝ) = gaussianReal 0 (Real.toNNReal (‖Z‖ ^ 2)) := by
  letI : IsProbabilityMeasure (gaussianReal 0 (Real.toNNReal (‖Z‖ ^ 2))) :=
    instIsProbabilityMeasureGaussianReal 0 (Real.toNNReal (‖Z‖ ^ 2))
  refine Measure.ext_of_charFun (μ := μ.map (Z : S → ℝ))
    (ν := gaussianReal 0 (Real.toNNReal (‖Z‖ ^ 2))) (funext fun t => ?_)
  rw [charFun_map_of_centered_tendsto_L2 μ Y Z hY_gauss hY_mean hYZ t, charFun_gaussianReal t]
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  congr 1
  push_cast
  ring

end ProbabilityTheory

#print axioms ProbabilityTheory.charFun_map_of_centered_tendsto_L2
#print axioms ProbabilityTheory.hasGaussianLaw_of_centered_tendsto_L2
#print axioms ProbabilityTheory.map_eq_gaussianReal_of_centered_tendsto_L2
#check ProbabilityTheory.charFun_map_of_centered_tendsto_L2
#check ProbabilityTheory.hasGaussianLaw_of_centered_tendsto_L2
#check ProbabilityTheory.map_eq_gaussianReal_of_centered_tendsto_L2
