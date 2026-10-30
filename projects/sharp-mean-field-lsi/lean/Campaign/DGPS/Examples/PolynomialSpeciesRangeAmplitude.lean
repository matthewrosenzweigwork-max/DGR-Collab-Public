import DGPS.Examples.PolynomialSpeciesRangeDerivative

/-! The true first-amplitude kernel of the interacting origin linearization. The
nonlocal moment derivatives vanish by actual Haar Fourier orthogonality. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem reference_zero : polynomialRangeReference (0, 0) = 1 := by
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  rw [polynomialRangeReference, hL, map_zero, rho_zero_STR02955]

private theorem feature_zero : e0_STR02955 (polynomialRangeFeature (0, 0)) = e0_STR02955 polynomialOriginMode := by
  have h := polynomialRangeFeature_actual 0
  rw [polynomial_root_origin, ← polynomialOriginMode_actual] at h
  exact h

private theorem generator_zero : polynomialRangeGenerator (0, 0) =
    (4 * DGPS.Circle.AngularNormalization.a0) • e0_STR02955 (polynomialRangeFeature (0, 0)) := by
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  have hφ : polynomialRangeFeature (0, 0) = polynomialOriginMode := by
    apply Subtype.ext
    have he := congrArg PeriodicHolder_STR02968.val feature_zero
    simp only [e0_val_STR02955] at he
    unfold PeriodicC2_STR02969.val at he
    exact he
  unfold polynomialRangeGenerator
  rw [hL, hφ, map_zero, zero_mul, sub_zero]
  apply ext_STR02954
  funext t
  change DGPS.Circle.AngularNormalization.a0 * (-deriv (deriv polynomialOriginMode.val) t) =
    (4 * DGPS.Circle.AngularNormalization.a0) * polynomialOriginMode.val t
  rw [polynomialOriginMode_second]
  ring

private theorem kernel_line (v : PeriodicC2_STR02969)
    (hv : meanCLM_STR02954 (e0_STR02955 v) = 0)
    (hφv : meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0)) * e0_STR02955 v) = 0)
    (hv2 : e2_STR02955 v = -e0_STR02955 v) :
    HasDerivAt (fun z : ℝ => polynomialRangeEuler (0, 0) DGPS.Circle.AngularNormalization.a0 (z • v)) 0 0 := by
  let a := DGPS.Circle.AngularNormalization.a0
  let V := e0_STR02955 v
  let D := e1_STR02955 v
  let D2 := e2_STR02955 v
  let φ := e0_STR02955 (polynomialRangeFeature (0, 0))
  let B := polynomialRangeGenerator (0, 0)
  let j := polynomialRangeGradientSq (0, 0)
  let R := fun z : ℝ => rho_STR02954 (0, z • V)
  let m := fun z : ℝ => meanCLM_STR02954 (φ * R z)
  let A := fun z : ℝ => meanCLM_STR02954 (B * R z)
  let J := fun z : ℝ => meanCLM_STR02954 (j * R z)
  have hV : meanCLM_STR02954 V = 0 := hv
  have hR : HasDerivAt R V 0 := by
    simpa only [zero_add, rho_zero_STR02955, mul_one, one_mul, hV, zero_smul, sub_zero] using
      hasDerivAt_rho_path_STR02949 0 (0 : PeriodicHolder_STR02968) V
  have hR0 : R 0 = 1 := by simp only [R, zero_smul, rho_zero_STR02955]
  have hm0 : m 0 = 0 := by
    have h := polynomialRangeFeature_centered (0, 0)
    rw [reference_zero, mul_one] at h
    simpa only [m, hR0, mul_one] using h
  have hA0 : A 0 = 0 := by
    have h := polynomialRangeGenerator_centered (0, 0)
    rw [reference_zero, mul_one] at h
    simpa only [A, hR0, mul_one] using h
  have hm : HasDerivAt m 0 0 := by
    have h := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) φ).mul hR)
    simp only [Function.comp_def, zero_mul, zero_add] at h
    convert h using 1
    change (0 : ℝ) = meanCLM_STR02954 (φ * V)
    exact hφv.symm
  have hBV : meanCLM_STR02954 (B * V) = 0 := by
    rw [show B = (4 * a) • φ from generator_zero, smul_mul_assoc, map_smul, hφv, smul_zero]
  have hA : HasDerivAt A 0 0 := by
    have h := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) B).mul hR)
    simp only [Function.comp_def, zero_mul, zero_add] at h
    convert h using 1
    exact hBV.symm
  have hJ : HasDerivAt J (meanCLM_STR02954 (j * V)) 0 := by
    simpa only [Function.comp_def, Pi.mul_apply, zero_mul, zero_add] using
      meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) j).mul hR)
  have hs0 : HasDerivAt (fun z : ℝ => z • V) V 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const V
  have hs1 : HasDerivAt (fun z : ℝ => z • D) D 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const D
  have hs2 : HasDerivAt (fun z : ℝ => z • D2) D2 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const D2
  let K := fun z : ℝ =>
    a • ((-2 : ℝ) • (z • D2) - (z • D) * (z • D)) - (2 * a) • (z • V) +
      (2 * eta * (A z + eta * m z * J z - a * m z)) • φ +
      (2 * eta * m z) • B + (eta ^ 2 * m z ^ 2) • j
  have hKraw := ((((((hs2.const_smul (-2 : ℝ)).sub (hs1.mul hs1)).const_smul a).sub
    (hs0.const_smul (2 * a))).add
      (((hA.add ((hm.const_mul eta).mul hJ)).sub (hm.const_mul a)).const_mul (2 * eta) |>.smul_const φ)).add
        ((hm.const_mul (2 * eta)).smul_const B)).add
          (((hm.pow 2).const_mul (eta ^ 2)).smul_const j)
  have hK : HasDerivAt K 0 0 := by
    change HasDerivAt K _ 0 at hKraw
    apply hKraw.congr_deriv
    simp only [hm0, hA0, zero_smul, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), one_smul,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    change a • ((-2 : ℝ) • e2_STR02955 v) - (2 * a) • e0_STR02955 v = 0
    rw [hv2]
    module
  have hK0 : K 0 = 0 := by
    simp only [K, hm0, hA0, zero_smul, smul_zero, zero_mul, mul_zero, add_zero, zero_add,
      sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hN := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK.mul hR)
  simp only [Function.comp_def, hK0, hR0, zero_mul, zero_add, add_zero, mul_one, map_zero] at hN
  have h := hR.mul (hK.sub (hN.smul_const (1 : PeriodicHolder_STR02968)))
  change HasDerivAt (fun z : ℝ => R z * (K z - meanCLM_STR02954 (K z * R z) • (1 : PeriodicHolder_STR02968)))
    (V * (K 0 - meanCLM_STR02954 (K 0 * R 0) • (1 : PeriodicHolder_STR02968)) +
      R 0 * ((0 : PeriodicHolder_STR02968) - (0 : ℝ) • (1 : PeriodicHolder_STR02968))) 0 at h
  simp only [hK0, hR0, zero_mul, map_zero, zero_smul, sub_zero, mul_zero, zero_add, one_mul] at h
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  have hDensity (z : ℝ) : eulerDensity (e0_STR02955 (polynomialRangeLogWeight (0, 0)))
      (z • v) = R z := by
    simp only [eulerDensity, hL, map_zero, map_smul, zero_add, R, V]
  have hPotential (z : ℝ) : polynomialRangeEulerPotential (0, 0)
      DGPS.Circle.AngularNormalization.a0 (z • v) = K z := by
    simp only [polynomialRangeEulerPotential, hL, map_zero, map_smul, zero_mul,
      smul_zero, sub_zero, zero_add, eulerMean, eulerDensity,
      K, R, m, A, J, a, V, D, D2, φ, B, j]
    <;> rfl
  have hfun : (fun z : ℝ => polynomialRangeEuler (0, 0) DGPS.Circle.AngularNormalization.a0 (z • v)) =
      fun z : ℝ => R z * (K z - meanCLM_STR02954 (K z * R z) • (1 : PeriodicHolder_STR02968)) := by
    funext z
    simp only [polynomialRangeEuler, eulerMean, hPotential, hDensity]
  rw [hfun]
  exact h

private theorem mode_pair_cos : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode * e0_STR02955 cosC2_STR02915) = 0 := by
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

private theorem mode_pair_sin : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode * e0_STR02955 sinC2_STR02915) = 0 := by
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

/-- Every actual first-harmonic amplitude direction is killed by the projected origin derivative. -/
theorem polynomialRangeMap_first_amplitude_line (a b : ℝ) :
    HasDerivAt (fun z : ℝ => polynomialRangeMap (((z * a, z * b, (0, 0), 0) : PolynomialRangeParameters), 0)) 0 0 := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  have hv : meanCLM_STR02954 (e0_STR02955 v) = 0 := by
    change meanCLM_STR02954 (a • e0_STR02955 cosC2_STR02915 + b • e0_STR02955 sinC2_STR02915) = 0
    rw [map_add, map_smul, map_smul]
    change a * meanT_STR02901 Real.cos + b * meanT_STR02901 Real.sin = 0
    rw [meanT_cos_STR02955, meanT_sin_STR02955]
    ring
  have hp : meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0)) * e0_STR02955 v) = 0 := by
    rw [feature_zero]
    change meanCLM_STR02954 (e0_STR02955 polynomialOriginMode *
      (a • e0_STR02955 cosC2_STR02915 + b • e0_STR02955 sinC2_STR02915)) = 0
    rw [mul_add, mul_smul_comm, mul_smul_comm, map_add, map_smul, map_smul, mode_pair_cos, mode_pair_sin]
    simp
  have hc : e2_STR02955 cosC2_STR02915 = -e0_STR02955 cosC2_STR02915 := by
    apply ext_STR02954
    funext t
    change deriv (deriv Real.cos) t = -Real.cos t
    simp
  have hs : e2_STR02955 sinC2_STR02915 = -e0_STR02955 sinC2_STR02915 := by
    apply ext_STR02954
    funext t
    change deriv (deriv Real.sin) t = -Real.sin t
    simp
  have hv2 : e2_STR02955 v = -e0_STR02955 v := by
    simp only [v, map_add, map_smul, hc, hs]
    module
  have h := PY_STR02955.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (kernel_line v hv hp hv2)
  change HasDerivAt (fun z : ℝ => PY_STR02955 (polynomialRangeEuler (0, 0)
    DGPS.Circle.AngularNormalization.a0 (z • v))) _ 0 at h
  simp only [map_zero] at h
  convert h using 1
  funext z
  have he : (z * a) • cosC2_STR02915 + (z * b) • sinC2_STR02915 = z • v := by
    dsimp only [v]
    module
  simp only [polynomialRangeMap, ZeroMemClass.coe_zero, add_zero, mul_one, he]

end DGPS.Examples.PolynomialSpecies
