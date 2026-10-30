import DGPS.Examples.PolynomialSpeciesOriginMomentSecond

/-! Exact Haar Fourier evaluation of the genuine origin feature-moment second
variation. The result is a SECOND derivative, twice its epsilon² coefficient. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private def sin2 : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk (fun t => Real.sin (2 * t)) (sinFreq_isC2_STR02962 2)

private theorem feature_origin : e0_STR02955 (polynomialRangeFeature (0, 0)) =
    e0_STR02955 polynomialOriginMode := by
  have h := polynomialRangeFeature_actual 0
  rw [polynomial_root_origin, ← polynomialOriginMode_actual] at h
  exact h

private theorem mode_mean : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode) = 0 := by
  have h := polynomialRangeFeature_centered (0, 0)
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  have hQ : polynomialRangeReference (0, 0) = 1 := by
    rw [polynomialRangeReference, hL, map_zero, rho_zero_STR02955]
  rw [feature_origin, hQ, mul_one] at h
  exact h

private theorem mode_sin : meanCLM_STR02954
    (e0_STR02955 polynomialOriginMode * e0_STR02955 sin2) = 0 := by
  have hm : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
      (Real.sqrt 2 • e0_STR02955 sin2)) = 0 := by
    rw [meanCLM_apply_STR02954]
    change meanT_STR02901 (fun t => (Real.sqrt 2 * Real.cos (2 * t)) *
      (Real.sqrt 2 * Real.sin (2 * t))) = 0
    rw [meanT_eq_normInt_STR02909]
    simpa [trigBasisFun_STR02934] using
      normInt_trigBasis_mul_STR02934 (some (false, 1)) (some (true, 1))
  rw [mul_smul_comm, map_smul, smul_eq_mul] at hm
  exact (mul_eq_zero.mp hm).resolve_left (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

private theorem first_square (a b t : ℝ) :
    (a * Real.cos t + b * Real.sin t) ^ 2 = (a ^ 2 + b ^ 2) / 2 +
      (a ^ 2 - b ^ 2) / 2 * Real.cos (2 * t) + a * b * Real.sin (2 * t) := by
  rw [Real.cos_two_mul, Real.sin_two_mul]
  have ha := congrArg (fun z : ℝ => a ^ 2 * z) (Real.sin_sq_add_cos_sq t)
  have hb := congrArg (fun z : ℝ => b ^ 2 * z) (Real.sin_sq_add_cos_sq t)
  nlinarith [ha, hb]

/-- The genuine origin feature-moment Hessian has the exact coefficient. -/
theorem polynomialOriginFeature_second_coefficient (a b : ℝ) :
    meanCLM_STR02954
      ((e0_STR02955 (polynomialRangeFeature (0, 0)) *
        e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)) *
        e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)) =
      Real.sqrt 2 * (a ^ 2 - b ^ 2) / 4 := by
  rw [feature_origin]
  let φ := e0_STR02955 polynomialOriginMode
  let V := e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)
  let S := e0_STR02955 sin2
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hfun : (φ * V) * V = ((a ^ 2 + b ^ 2) / 2) • φ +
      ((a ^ 2 - b ^ 2) / (2 * Real.sqrt 2)) • (φ * φ) + (a * b) • (φ * S) := by
    apply ext_STR02954
    funext t
    change ((Real.sqrt 2 * Real.cos (2 * t)) * (a * Real.cos t + b * Real.sin t)) *
      (a * Real.cos t + b * Real.sin t) =
      ((a ^ 2 + b ^ 2) / 2) * (Real.sqrt 2 * Real.cos (2 * t)) +
      ((a ^ 2 - b ^ 2) / (2 * Real.sqrt 2)) *
        ((Real.sqrt 2 * Real.cos (2 * t)) * (Real.sqrt 2 * Real.cos (2 * t))) +
      (a * b) * ((Real.sqrt 2 * Real.cos (2 * t)) * Real.sin (2 * t))
    rw [mul_assoc, ← pow_two, first_square]
    field_simp [hn] <;> ring
  change meanCLM_STR02954 ((φ * V) * V) = _
  rw [hfun, map_add, map_add, map_smul, map_smul, map_smul,
    show meanCLM_STR02954 φ = 0 from mode_mean,
    show meanCLM_STR02954 (φ * φ) = 1 from polynomialOriginMode_unit,
    show meanCLM_STR02954 (φ * S) = 0 from mode_sin]
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero]
  have hi : (1 : ℝ) / (2 * Real.sqrt 2) = Real.sqrt 2 / 4 := by
    field_simp [hn]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (a ^ 2 - b ^ 2) / (2 * Real.sqrt 2) = (a ^ 2 - b ^ 2) * (1 / (2 * Real.sqrt 2)) := by ring
    _ = _ := by rw [hi]; ring

/-- The actual normalized moment's SECOND derivative, with no factor-two ambiguity. -/
theorem polynomialOriginAmplitudeMoment_second_exact (a b : ℝ) :
    HasDerivAt (fun z : ℝ => deriv (fun y : ℝ =>
      eulerMean (0 : PeriodicHolder_STR02968)
        (y • (a • cosC2_STR02915 + b • sinC2_STR02915))
        (e0_STR02955 (polynomialRangeFeature (0, 0)))) z)
      (Real.sqrt 2 * (a ^ 2 - b ^ 2) / 4) 0 :=
  (polynomialOriginAmplitudeMoment_second a b).congr_deriv (polynomialOriginFeature_second_coefficient a b)

end DGPS.Examples.PolynomialSpecies
