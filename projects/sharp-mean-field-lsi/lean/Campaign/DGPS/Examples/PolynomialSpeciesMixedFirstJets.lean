import DGPS.Examples.PolynomialSpeciesMixedGeneratorSecond
import DGPS.Examples.PolynomialSpeciesHalfTurnValue

/-! The actual mixed scalar moments have zero first jets. Their evenness is
derived from the real half-turn transformation of the same density/reference,
not assumed from a formal polynomial expansion. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem even_derivative_zero (f : ℝ → ℝ) (he : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have h := congrArg (fun g : ℝ → ℝ => iteratedDeriv 1 g 0) (funext he)
  rw [iteratedDeriv_comp_neg] at h
  norm_num [iteratedDeriv_one] at h
  linarith

private theorem moments_even (a b t : ℝ) :
    polynomialMixedFeatureMoment a b (-t) = polynomialMixedFeatureMoment a b t ∧
      polynomialMixedGeneratorMoment a b (-t) = polynomialMixedGeneratorMoment a b t := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  have hu : ∀ x : ℝ, ((-t) • v).val (x + Real.pi) = (t • v).val x := by
    intro x
    simp only [v, PeriodicC2_STR02969.val_smul, PeriodicC2_STR02969.val_add,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul, cosC2_val_STR02915, sinC2_val_STR02915,
      Real.cos_add_pi, Real.sin_add_pi]
    ring
  have hm := polynomialRange_moments_half_turn t 0 (t • v) ((-t) • v) hu
  exact ⟨hm.2.2.1, hm.2.2.2.1⟩

/-- All zero and first jets are derived from actual centering and actual
half-turn covariance. These are the jets needed before differentiating the
nonlocal Euler potential; no such jet is supplied as a hypothesis. -/
theorem polynomialMixedMoments_zero_and_first (a b : ℝ) :
    polynomialMixedFeatureMoment a b 0 = 0 ∧
      polynomialMixedGeneratorMoment a b 0 = 0 ∧
      deriv (polynomialMixedFeatureMoment a b) 0 = 0 ∧
      deriv (polynomialMixedGeneratorMoment a b) 0 = 0 := by
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  have hm := polynomialRangeFeature_centered (0, 0)
  have hA := polynomialRangeGenerator_centered (0, 0)
  rw [polynomialOriginReference_eq, mul_one] at hm hA
  have hm0 : polynomialMixedFeatureMoment a b 0 = 0 := by
    simpa only [polynomialMixedFeatureMoment, eulerMean, eulerDensity, hL, map_zero,
      zero_smul, zero_add, rho_zero_STR02955, mul_one] using hm
  have hA0 : polynomialMixedGeneratorMoment a b 0 = 0 := by
    simpa only [polynomialMixedGeneratorMoment, eulerMean, eulerDensity, hL, map_zero,
      zero_smul, zero_add, rho_zero_STR02955, mul_one] using hA
  exact ⟨hm0, hA0, even_derivative_zero _ (fun t => (moments_even a b t).1),
    even_derivative_zero _ (fun t => (moments_even a b t).2)⟩

end DGPS.Examples.PolynomialSpecies
