import DGPS.Examples.PolynomialSpeciesMixedPotentialJets

/-! The actual mixed Euler second forcing. Density normalization and mean
subtraction are differentiated before the Fourier expression is identified. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem mean_second (F : ℝ → PeriodicHolder_STR02968) (hF : ContDiff ℝ ∞ F) :
    iteratedDeriv 2 (fun t => meanCLM_STR02954 (F t)) 0 = meanCLM_STR02954 (iteratedDeriv 2 F 0) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ 2 (meanCLM_STR02954 ∘ F) 0) (fun _ => 1) = _
  rw [meanCLM_STR02954.iteratedFDeriv_comp_left hF.contDiffAt (by simp)]
  rfl

private theorem normalized_second (R K : ℝ → PeriodicHolder_STR02968)
    (hR : ContDiff ℝ ∞ R) (hK : ContDiff ℝ ∞ K)
    (hR0 : R 0 = 1) (hK0 : K 0 = 0) (hK1 : deriv K 0 = 0) :
    iteratedDeriv 2 (fun t => R t * (K t - meanCLM_STR02954 (K t * R t) • (1 : PeriodicHolder_STR02968))) 0 =
      iteratedDeriv 2 K 0 - meanCLM_STR02954 (iteratedDeriv 2 K 0) • 1 := by
  let M := fun t => meanCLM_STR02954 (K t * R t)
  have hM : ContDiff ℝ ∞ M := meanCLM_STR02954.contDiff.comp (hK.mul hR)
  have hM0 : M 0 = 0 := by simp only [M, hK0, zero_mul, map_zero]
  have hM1 : deriv M 0 = 0 := by
    have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hK.differentiable (by simp) 0).hasDerivAt.mul (hR.differentiable (by simp) 0).hasDerivAt)
    change HasDerivAt M _ 0 at hd
    simpa only [hK0, hK1, zero_mul, zero_add, map_zero] using hd.deriv
  have hKR2 : iteratedDeriv 2 (fun t => K t * R t) 0 = iteratedDeriv 2 K 0 := by
    rw [iteratedDeriv_fun_mul ((hK.of_le (by simp)).contDiffAt) ((hR.of_le (by simp)).contDiffAt)]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hK0, hK1, hR0]
  have hM2 : iteratedDeriv 2 M 0 = meanCLM_STR02954 (iteratedDeriv 2 K 0) := by
    rw [show M = fun t => meanCLM_STR02954 (K t * R t) from rfl, mean_second _ (hK.mul hR), hKR2]
  let Q := fun t => K t - M t • (1 : PeriodicHolder_STR02968)
  have hQ : ContDiff ℝ ∞ Q := hK.sub (hM.smul contDiff_const)
  have hQ0 : Q 0 = 0 := by simp only [Q, hK0, hM0, zero_smul, sub_zero]
  have hQ1 : deriv Q 0 = 0 := by
    have hd := (hK.differentiable (by simp) 0).hasDerivAt.sub
      ((hM.differentiable (by simp) 0).hasDerivAt.smul_const (1 : PeriodicHolder_STR02968))
    change HasDerivAt Q _ 0 at hd
    simpa only [hK1, hM1, zero_smul, sub_zero] using hd.deriv
  have hMs : ContDiff ℝ ∞ (fun t : ℝ => M t • (1 : PeriodicHolder_STR02968)) := hM.smul contDiff_const
  have hQ2 : iteratedDeriv 2 Q 0 = iteratedDeriv 2 K 0 - meanCLM_STR02954 (iteratedDeriv 2 K 0) • 1 := by
    rw [show Q = fun t => K t - M t • (1 : PeriodicHolder_STR02968) from rfl,
      iteratedDeriv_fun_sub ((hK.of_le (by simp)).contDiffAt) ((hMs.of_le (by simp)).contDiffAt),
      iteratedDeriv_smul_const ((hM.of_le (by simp)).contDiffAt), hM2]
  change iteratedDeriv 2 (fun t => R t * Q t) 0 = _
  rw [iteratedDeriv_fun_mul ((hR.of_le (by simp)).contDiffAt) ((hQ.of_le (by simp)).contDiffAt)]
  simpa [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, hQ0, hQ1, hR0] using hQ2

private theorem amplitude_first (a b : ℝ) :
    e1_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915) =
      (-a) • e0_STR02955 sinC2_STR02915 + b • e0_STR02955 cosC2_STR02915 := by
  rw [map_add, map_smul, map_smul]
  apply ext_STR02954
  funext x
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    e1_val_STR02955, e0_val_STR02955, cosC2_val_STR02915, sinC2_val_STR02915,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.deriv_cos', Real.deriv_sin]
  ring

private theorem mean_cos_sq : meanCLM_STR02954 (e0_STR02955 cosC2_STR02915 * e0_STR02955 cosC2_STR02915) = 1 / 2 := meanT_cc_STR02955
private theorem mean_sin_sq : meanCLM_STR02954 (e0_STR02955 sinC2_STR02915 * e0_STR02955 sinC2_STR02915) = 1 / 2 := meanT_ss_STR02955
private theorem mean_sin_cos : meanCLM_STR02954 (e0_STR02955 sinC2_STR02915 * e0_STR02955 cosC2_STR02915) = 0 := meanT_sc_STR02955

private theorem amplitude_energy (a b : ℝ) :
    meanCLM_STR02954 (e1_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915) *
      e1_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)) = (a ^ 2 + b ^ 2) / 2 := by
  have hcs : meanCLM_STR02954 (e0_STR02955 cosC2_STR02915 * e0_STR02955 sinC2_STR02915) = 0 := by
    rw [mul_comm]
    exact meanT_sc_STR02955
  rw [amplitude_first]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul,
    mean_cos_sq, mean_sin_sq, mean_sin_cos, hcs, smul_eq_mul]
  ring

private theorem cross_energy (a b : ℝ) :
    meanCLM_STR02954 (e1_STR02955 cosC2_STR02915 *
      e1_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)) = a / 2 := by
  have hc : e1_STR02955 cosC2_STR02915 = (-1 : ℝ) • e0_STR02955 sinC2_STR02915 := by
    apply ext_STR02954
    funext x
    simp only [e1_val_STR02955, PeriodicHolder_STR02968.val_smul, e0_val_STR02955,
      cosC2_val_STR02915, sinC2_val_STR02915, Pi.smul_apply, smul_eq_mul, Real.deriv_cos']
    ring
  rw [hc, amplitude_first]
  simp only [mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul,
    mean_sin_sq, mean_sin_cos, smul_eq_mul]
  ring

/-- The genuine normalized, density-weighted Euler SECOND derivative on the
mixed field/amplitude line. The coefficient is twice the quadratic forcing. -/
theorem polynomialMixedEuler_second_pointwise (a b x : ℝ) :
    (iteratedDeriv 2 (fun t : ℝ => polynomialRangeEuler (t, 0)
      DGPS.Circle.AngularNormalization.a0
      (t • (a • cosC2_STR02915 + b • sinC2_STR02915))) 0).val x =
      DGPS.Circle.AngularNormalization.a0 *
        (4 * (a + a ^ 2 - b ^ 2) * Real.cos (2 * x) + 2 * b * (1 + a) * Real.sin (2 * x)) := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  let K := fun t : ℝ => polynomialRangeEulerPotential (t, 0) DGPS.Circle.AngularNormalization.a0 (t • v)
  let R := fun t : ℝ => eulerDensity (e0_STR02955 (polynomialRangeLogWeight (t, 0))) (t • v)
  let z := Real.sqrt 2 * ((a ^ 2 - b ^ 2) / 4 + a / 6)
  let H := (-4 * DGPS.Circle.AngularNormalization.a0) • (e1_STR02955 cosC2_STR02915 * e1_STR02955 v) +
    (-2 * DGPS.Circle.AngularNormalization.a0) • (e1_STR02955 v * e1_STR02955 v) +
      (6 * DGPS.Circle.AngularNormalization.a0 * z) • e0_STR02955 polynomialOriginMode
  obtain ⟨hK, hK0, hK1, hK2⟩ := polynomialMixedPotential_jets a b
  have hR : ContDiff ℝ ∞ R := rho_smooth_STR02954.comp (contDiff_const.prodMk
    ((e0_STR02955.contDiff.comp (polynomialRange_data_smooth.1.comp (contDiff_id.prodMk contDiff_const))).add
      (e0_STR02955.contDiff.comp (contDiff_id.smul contDiff_const))))
  have hR0 : R 0 = 1 := by
    simp only [R, eulerDensity, zero_smul,
      show polynomialRangeLogWeight (0, 0) = 0 by simp [polynomialRangeLogWeight],
      map_zero, zero_add, rho_zero_STR02955]
  have hn := normalized_second R K hR hK hR0 hK0 hK1
  have he : (fun t : ℝ => polynomialRangeEuler (t, 0) DGPS.Circle.AngularNormalization.a0 (t • v)) =
      fun t => R t * (K t - meanCLM_STR02954 (K t * R t) • (1 : PeriodicHolder_STR02968)) := rfl
  have hmean : meanCLM_STR02954 H = -DGPS.Circle.AngularNormalization.a0 * (2 * a + a ^ 2 + b ^ 2) := by
    have hcross : meanCLM_STR02954 (e1_STR02955 cosC2_STR02915 * e1_STR02955 v) = a / 2 := cross_energy a b
    have henergy : meanCLM_STR02954 (e1_STR02955 v * e1_STR02955 v) = (a ^ 2 + b ^ 2) / 2 := amplitude_energy a b
    simp only [H, map_add, map_smul, hcross, henergy, polynomialOriginFeature_mean_zero,
      smul_eq_mul, mul_zero, add_zero]
    ring
  rw [he, hn, hK2]
  change (H - meanCLM_STR02954 H • (1 : PeriodicHolder_STR02968)).val x = _
  rw [hmean]
  have hN : (6 * DGPS.Circle.AngularNormalization.a0 * z) *
      (e0_STR02955 polynomialOriginMode).val x =
        DGPS.Circle.AngularNormalization.a0 * (3 * (a ^ 2 - b ^ 2) + 2 * a) * Real.cos (2 * x) := by
    change (6 * DGPS.Circle.AngularNormalization.a0 *
      (Real.sqrt 2 * ((a ^ 2 - b ^ 2) / 4 + a / 6))) * (Real.sqrt 2 * Real.cos (2 * x)) = _
    calc
      _ = 6 * DGPS.Circle.AngularNormalization.a0 * ((a ^ 2 - b ^ 2) / 4 + a / 6) *
          Real.sqrt 2 ^ 2 * Real.cos (2 * x) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  simp only [H, PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_one]
  change (-4 * DGPS.Circle.AngularNormalization.a0) *
      ((e1_STR02955 cosC2_STR02915).val x * (e1_STR02955 v).val x) +
    (-2 * DGPS.Circle.AngularNormalization.a0) * ((e1_STR02955 v).val x * (e1_STR02955 v).val x) +
    (6 * DGPS.Circle.AngularNormalization.a0 * z) * (e0_STR02955 polynomialOriginMode).val x -
    (-DGPS.Circle.AngularNormalization.a0 * (2 * a + a ^ 2 + b ^ 2)) = _
  rw [hN, amplitude_first]
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, e1_val_STR02955, e0_val_STR02955,
    cosC2_val_STR02915, sinC2_val_STR02915, Real.deriv_cos']
  rw [Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (-DGPS.Circle.AngularNormalization.a0 * (2 * a ^ 2 + 4 * a)) * Real.sin_sq_add_cos_sq x

end DGPS.Examples.PolynomialSpecies
