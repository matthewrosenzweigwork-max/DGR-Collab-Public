import DGPS.Examples.PolynomialSpeciesMixedMomentSecond
import DGPS.Examples.PolynomialSpeciesOriginData

/-! The independent s=0 reference moment has second derivative -1/12. This
is derived from the actual Haar cancellation of a mixed tilt, without assuming
selected-root differentiability or reading derivatives off a formal expansion. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem haar_tilt_moment (t : ℝ) :
    polynomialMixedFeatureMoment (-1) 0 t = -Real.sqrt 2 * moment_EX054 t 0 := by
  let φ := e0_STR02955 (polynomialRangeFeature (0, 0))
  let C := e0_STR02955 cosC2_STR02915
  have hm0 : moment_EX054 0 0 = 0 := by
    simpa only [polynomial_root_origin] using polynomial_mean_origin
  have hφ : e0_STR02955 (polynomialRangeFeature (t, 0)) = φ -
      (Real.sqrt 2 * t / 3) • C - (Real.sqrt 2 * moment_EX054 t 0) • (1 : PeriodicHolder_STR02968) := by
    apply ext_STR02954
    funext x
    simp only [e0_val_STR02955, polynomialRangeFeature_val, φ, C,
      PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_one_STR02954, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      cosC2_val_STR02915, DGPS.Examples.PolynomialCenteredResidual.feature_coe_EX057, hm0]
    ring
  have hu : t • ((-1 : ℝ) • cosC2_STR02915 + (0 : ℝ) • sinC2_STR02915) =
      -polynomialRangeLogWeight (t, 0) := by
    apply Subtype.ext
    funext x
    change (t • ((-1 : ℝ) • cosC2_STR02915 + (0 : ℝ) • sinC2_STR02915)).val x =
      -(polynomialRangeLogWeight (t, 0)).val x
    simp only [PeriodicC2_STR02969.val_smul, PeriodicC2_STR02969.val_add,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul, cosC2_val_STR02915, sinC2_val_STR02915]
    rw [polynomialRangeLogWeight_val_explicit]
    ring
  have hρ : eulerDensity (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
      (t • ((-1 : ℝ) • cosC2_STR02915 + (0 : ℝ) • sinC2_STR02915)) = 1 := by
    unfold eulerDensity
    rw [hu, map_neg, add_neg_cancel, rho_zero_STR02955]
  have hφ0 : meanCLM_STR02954 φ = 0 := by
    rw [show φ = e0_STR02955 polynomialOriginMode from congrArg e0_STR02955 polynomialOriginFeature_eq]
    exact polynomialOriginFeature_mean_zero
  have hC0 : meanCLM_STR02954 C = 0 := by
    rw [meanCLM_apply_STR02954]
    have he : C.val = Real.cos := cosC2_val_STR02915
    rw [he]
    exact meanT_cos_STR02955
  have hOne : meanCLM_STR02954 (1 : PeriodicHolder_STR02968) = 1 := by
    rw [meanCLM_apply_STR02954]
    exact meanT_const_STR02955 1
  unfold polynomialMixedFeatureMoment eulerMean
  rw [hρ, mul_one, hφ, map_sub, map_sub, map_smul, map_smul, hφ0, hC0, hOne]
  simp only [smul_eq_mul]
  ring

/-- Genuine second derivative of the actual independent zero-tilt reference
mean. This provides the constant cancellation in the mixed residual expectation. -/
theorem polynomialReferenceMoment_zero_tilt_second :
    iteratedDeriv 2 (fun t : ℝ => moment_EX054 t 0) 0 = -1 / 12 := by
  have he : polynomialMixedFeatureMoment (-1) 0 =
      fun t : ℝ => -Real.sqrt 2 * moment_EX054 t 0 := funext haar_tilt_moment
  have hs := polynomialMixedFeatureMoment_second (-1) 0
  rw [he, iteratedDeriv_const_mul_field] at hs
  apply mul_left_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  nlinarith

end DGPS.Examples.PolynomialSpecies
