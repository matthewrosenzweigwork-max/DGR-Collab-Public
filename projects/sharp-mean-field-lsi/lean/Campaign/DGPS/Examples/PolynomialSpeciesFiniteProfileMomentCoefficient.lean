import DGPS.Examples.PolynomialSpeciesFiniteProfileMomentSecond
import DGPS.Examples.PolynomialSpeciesMixedFiniteProfile

/-! Exact leading moment of the actual finite mixed profile. All pairings
use the genuine origin feature and the concrete corrected second mode. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem sine_pair_zero : polynomialOriginCoefficient polynomialOriginSineSecondE = 0 := by
  have hm : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
      (Real.sqrt 2 • e0_STR02955 polynomialOriginSineSecond)) = 0 := by
    rw [meanCLM_apply_STR02954]
    change meanT_STR02901 (fun t => (Real.sqrt 2 * Real.cos (2 * t)) *
      (Real.sqrt 2 * Real.sin (2 * t))) = 0
    rw [meanT_eq_normInt_STR02909]
    simpa [trigBasisFun_STR02934] using
      normInt_trigBasis_mul_STR02934 (some (false, 1)) (some (true, 1))
  rw [mul_smul_comm, map_smul, smul_eq_mul] at hm
  change meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
    e0_STR02955 polynomialOriginSineSecond) = 0
  exact (mul_eq_zero.mp hm).resolve_left
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

private theorem pure_coefficient (a b : ℝ) :
    polynomialOriginCoefficient (polynomialOriginSecondCorrection a b) =
      -(a ^ 2 - b ^ 2) / (3 * Real.sqrt 2) := by
  rw [polynomialOriginSecondCorrection, map_add, map_smul, map_smul,
    show polynomialOriginCoefficient polynomialOriginModeE = 1 from polynomialOriginMode_unit,
    sine_pair_zero]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]

/-- Exact actual Haar pairing of the mixed SECOND graph correction. -/
theorem polynomialOriginMixedSecondCorrection_coefficient (a b : ℝ) :
    meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
      e0_STR02955 (polynomialOriginMixedSecondCorrection a b : PeriodicC2_STR02969)) =
      -(a + a ^ 2 - b ^ 2) / (3 * Real.sqrt 2) := by
  change polynomialOriginCoefficient (polynomialOriginMixedSecondCorrection a b) = _
  rw [polynomialOriginMixedSecondCorrection, map_add, map_add, map_smul, map_smul,
    pure_coefficient, pure_coefficient, pure_coefficient]
  simp only [smul_eq_mul]
  ring

private theorem profile_eq (a b t : ℝ) :
    polynomialMixedFiniteProfile a b t =
      t • (a • cosC2_STR02915 + b • sinC2_STR02915) +
        t ^ 2 • ((1 / 2 : ℝ) •
          (polynomialOriginMixedSecondCorrection a b : PeriodicC2_STR02969)) := by
  simp only [polynomialMixedFiniteProfile, smul_add, smul_smul]
  congr 1
  congr 1
  ring

/-- The true actual centered moment's SECOND derivative on the concrete
mixed finite profile. The leading h-squared coefficient is half this value. -/
theorem polynomialMixedFiniteProfile_feature_moment_second (a b : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => eulerMean
      (e0_STR02955 (polynomialRangeLogWeight (t, 0))) (polynomialMixedFiniteProfile a b t)
      (e0_STR02955 (polynomialRangeFeature (t, 0)))) 0 =
      Real.sqrt 2 * (a ^ 2 - b ^ 2) / 12 := by
  simp_rw [profile_eq]
  rw [polynomialFiniteProfile_feature_moment_second, map_smul, mul_smul_comm, map_smul,
    polynomialOriginMixedSecondCorrection_coefficient]
  simp only [smul_eq_mul]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hs]
  nlinarith [congrArg (fun z : ℝ => z * (a + a ^ 2 - b ^ 2))
    (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))]

/-- Matching true generator expectation SECOND derivative on the concrete
profile; this does not identify the generator and feature pointwise. -/
theorem polynomialMixedFiniteProfile_generator_moment_second (a b : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => eulerMean
      (e0_STR02955 (polynomialRangeLogWeight (t, 0))) (polynomialMixedFiniteProfile a b t)
      (polynomialRangeGenerator (t, 0))) 0 =
      DGPS.Circle.AngularNormalization.a0 * Real.sqrt 2 * (a ^ 2 - b ^ 2) / 3 := by
  have he := polynomialFiniteProfile_generator_moment_second a b
    ((1 / 2 : ℝ) • (polynomialOriginMixedSecondCorrection a b : PeriodicC2_STR02969))
  simp_rw [← profile_eq] at he
  rw [he, polynomialMixedFiniteProfile_feature_moment_second]
  ring

end DGPS.Examples.PolynomialSpecies
