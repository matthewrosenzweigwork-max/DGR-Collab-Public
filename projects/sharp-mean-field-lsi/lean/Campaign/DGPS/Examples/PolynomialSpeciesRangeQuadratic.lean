import DGPS.Examples.PolynomialSpeciesRangeHessian

/-! The actual first-harmonic coefficient of the polynomial gap at the Haar origin. -/
noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem feature_origin : e0_STR02955 (polynomialRangeFeature (0, 0)) =
    e0_STR02955 polynomialOriginMode := by
  have h := polynomialRangeFeature_actual 0
  rw [polynomial_root_origin, ← polynomialOriginMode_actual] at h
  exact h

private theorem pair_cos : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
    e0_STR02955 cosC2_STR02915) = 0 := by
  have hm : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
      (Real.sqrt 2 • e0_STR02955 cosC2_STR02915)) = 0 := by
    rw [meanCLM_apply_STR02954]
    change meanT_STR02901 (fun t => (Real.sqrt 2 * Real.cos (2 * t)) *
      (Real.sqrt 2 * Real.cos t)) = 0
    rw [meanT_eq_normInt_STR02909]
    simpa [trigBasisFun_STR02934] using
      normInt_trigBasis_mul_STR02934 (some (false, 1)) (some (false, 0))
  rw [mul_smul_comm, map_smul, smul_eq_mul] at hm
  exact (mul_eq_zero.mp hm).resolve_left (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

private theorem pair_sin : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
    e0_STR02955 sinC2_STR02915) = 0 := by
  have hm : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
      (Real.sqrt 2 • e0_STR02955 sinC2_STR02915)) = 0 := by
    rw [meanCLM_apply_STR02954]
    change meanT_STR02901 (fun t => (Real.sqrt 2 * Real.cos (2 * t)) *
      (Real.sqrt 2 * Real.sin t)) = 0
    rw [meanT_eq_normInt_STR02909]
    simpa [trigBasisFun_STR02934] using
      normInt_trigBasis_mul_STR02934 (some (false, 1)) (some (true, 0))
  rw [mul_smul_comm, map_smul, smul_eq_mul] at hm
  exact (mul_eq_zero.mp hm).resolve_left (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

/-- The actual amplitude direction is Haar centered. -/
theorem polynomial_first_amplitude_centered (a b : ℝ) :
    meanCLM_STR02954 (e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)) = 0 := by
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul]
  change a * meanT_STR02901 Real.cos + b * meanT_STR02901 Real.sin = 0
  rw [meanT_cos_STR02955, meanT_sin_STR02955]
  ring

/-- Its moment against the actual centered second harmonic vanishes. -/
theorem polynomial_first_amplitude_feature_moment (a b : ℝ) :
    meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0)) *
      e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)) = 0 := by
  rw [feature_origin, map_add, map_smul, map_smul, mul_add,
    mul_smul_comm, mul_smul_comm, map_add, map_smul, map_smul, pair_cos, pair_sin]
  simp

/-- The true origin gap Hessian on first harmonics has coefficient one half.
Thus its Taylor value coefficient is one quarter; no amplitude norm estimate is assumed. -/
theorem polynomialRangeGap_first_amplitude_hessian (a b : ℝ) :
    fderiv ℝ (fderiv ℝ (polynomialRangeGap (0, 0))) 0
      (a • cosC2_STR02915 + b • sinC2_STR02915)
      (a • cosC2_STR02915 + b • sinC2_STR02915) = (a ^ 2 + b ^ 2) / 2 := by
  rw [polynomialRangeGap_hessian_origin, polynomial_first_amplitude_centered,
    polynomial_first_amplitude_feature_moment]
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  have hcc : meanCLM_STR02954 (e0_STR02955 cosC2_STR02915 * e0_STR02955 cosC2_STR02915) = 1 / 2 :=
    meanT_cc_STR02955
  have hss : meanCLM_STR02954 (e0_STR02955 sinC2_STR02915 * e0_STR02955 sinC2_STR02915) = 1 / 2 :=
    meanT_ss_STR02955
  have hsc : meanCLM_STR02954 (e0_STR02955 sinC2_STR02915 * e0_STR02955 cosC2_STR02915) = 0 :=
    meanT_sc_STR02955
  have hcs : meanCLM_STR02954 (e0_STR02955 cosC2_STR02915 * e0_STR02955 sinC2_STR02915) = 0 := by
    rw [mul_comm]
    exact hsc
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hcc, hss, hsc, hcs, smul_eq_mul]
  ring

end DGPS.Examples.PolynomialSpecies
