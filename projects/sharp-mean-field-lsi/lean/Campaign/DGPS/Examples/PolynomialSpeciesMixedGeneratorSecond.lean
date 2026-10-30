import DGPS.Examples.PolynomialSpeciesIndependentResidual
import DGPS.Examples.PolynomialSpeciesReferenceMomentSecond
import DGPS.Frontier.STR029.T46

/-! The ACTUAL mixed generator expectation has second derivative four times
the feature-moment second derivative in physical units. Only this expectation
identity is proved; the feature is not a nonzero-field eigenfunction. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

def polynomialMixedGeneratorMoment (a b t : ℝ) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
    (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) (polynomialRangeGenerator (t, 0))

private def V (a b : ℝ) : PeriodicC2_STR02969 :=
  (1 + a) • cosC2_STR02915 + b • sinC2_STR02915
private def R (a b t : ℝ) : PeriodicHolder_STR02968 := rho_STR02954 (0, t • e0_STR02955 (V a b))
private def mu (a b : ℝ) (f : PeriodicHolder_STR02968) (t : ℝ) : ℝ :=
  meanCLM_STR02954 (f * R a b t)
private def C2 : PeriodicHolder_STR02968 := (Real.sqrt 2)⁻¹ • e0_STR02955 polynomialOriginMode

private theorem C2_val (x : ℝ) : C2.val x = Real.cos (2 * x) := by
  change (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * Real.cos (2 * x)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne', one_mul]

private theorem R_smooth (a b : ℝ) : ContDiff ℝ ∞ (R a b) :=
  rho_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_id.smul contDiff_const))

private theorem mu_smooth (a b : ℝ) (f : PeriodicHolder_STR02968) : ContDiff ℝ ∞ (mu a b f) :=
  meanCLM_STR02954.contDiff.comp (contDiff_const.mul (R_smooth a b))

private theorem R_mass (a b t : ℝ) : meanCLM_STR02954 (R a b t) = 1 := by
  rw [meanCLM_apply_STR02954]
  have he : (R a b t).val = rhoT_STR02901 0 (t • V a b).val := by
    funext x
    simpa only [R, map_smul, e0_val_STR02955, PeriodicC2_STR02969.val_smul,
      PeriodicHolder_STR02968.val_smul, Pi.smul_apply, smul_eq_mul] using
      rho_val_STR02954 (0, e0_STR02955 (t • V a b)) x
  rw [he]
  exact meanT_rho_STR02950 0 (t • V a b).isC2.2.1.continuous

private theorem actual_density (a b t : ℝ) :
    eulerDensity (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
      (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) = R a b t := by
  have hL : polynomialRangeLogWeight (t, 0) = t • cosC2_STR02915 := by
    apply Subtype.ext
    funext x
    change (polynomialRangeLogWeight (t, 0)).val x = (t • cosC2_STR02915).val x
    rw [polynomialRangeLogWeight_val_explicit, PeriodicC2_STR02969.val_smul,
      Pi.smul_apply, smul_eq_mul, cosC2_val_STR02915]
    ring
  have hv : cosC2_STR02915 + (a • cosC2_STR02915 + b • sinC2_STR02915) = V a b := by
    simp only [V, add_smul, one_smul, add_assoc]
  simp only [eulerDensity, hL, R, map_smul, map_add, ← smul_add]
  simp only [V, map_add, map_smul, add_smul, one_smul, add_assoc]

private theorem cosine3_pair_zero (a b : ℝ) :
    meanCLM_STR02954 (c3_STR02954 * e0_STR02955 (V a b)) = 0 := by
  rw [meanCLM_apply_STR02954]
  change meanT_STR02901 (fun x => Real.cos (3 * x) * ((1 + a) * Real.cos x + b * Real.sin x)) = 0
  rw [meanT_eq_normInt_STR02909]
  have he : (fun x : ℝ => Real.cos (3 * x) * ((1 + a) * Real.cos x + b * Real.sin x)) =
      fun x : ℝ => 0 * Real.cos x ^ 0 + (-3 * (1 + a)) * Real.cos x ^ 2 +
        (4 * (1 + a)) * Real.cos x ^ 4 + 0 * Real.cos x ^ 6 + 0 * Real.cos x ^ 8 +
        (-3 * b) * (Real.cos x ^ 1 * Real.sin x) +
        (4 * b) * (Real.cos x ^ 3 * Real.sin x) +
        0 * (Real.cos x ^ 5 * Real.sin x) + 0 * (Real.cos x ^ 7 * Real.sin x) := by
    funext x
    rw [Real.cos_three_mul]
    ring
  rw [he, mean9_STR02946]
  ring

private theorem cosine3_first (a b : ℝ) : deriv (mu a b c3_STR02954) 0 = 0 := by
  have hV : meanCLM_STR02954 (e0_STR02955 (V a b)) = 0 :=
    polynomial_first_amplitude_centered (1 + a) b
  have hR : HasDerivAt (R a b) (e0_STR02955 (V a b)) 0 := by
    change HasDerivAt (fun t : ℝ => rho_STR02954 (0, t • e0_STR02955 (V a b))) (e0_STR02955 (V a b)) 0
    simpa only [R, zero_add, rho_zero_STR02955, mul_one, one_mul, hV, zero_smul, sub_zero] using
      hasDerivAt_rho_path_STR02949 0 (0 : PeriodicHolder_STR02968) (e0_STR02955 (V a b))
  have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_const (0 : ℝ) c3_STR02954).mul hR)
  have hd' : HasDerivAt (mu a b c3_STR02954)
      (meanCLM_STR02954 (c3_STR02954 * e0_STR02955 (V a b))) 0 := by
    change HasDerivAt (fun t => meanCLM_STR02954 (c3_STR02954 * R a b t)) (meanCLM_STR02954 (c3_STR02954 * e0_STR02955 (V a b))) 0
    convert hd using 1 <;> simp only [mu, Function.comp_def, Pi.mul_apply, zero_mul, zero_add]
  rw [hd'.deriv, cosine3_pair_zero]

private theorem cosine2_zero (a b : ℝ) : mu a b C2 0 = 0 := by
  simp only [mu, R, zero_smul, rho_zero_STR02955, mul_one, C2, map_smul,
    polynomialOriginFeature_mean_zero, smul_eq_mul, mul_zero]

private theorem reference_smooth : ContDiff ℝ ∞ (fun t : ℝ => moment_EX054 t 0) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => polynomialRangeMean (t, 0)) := polynomialRange_data_smooth.2.2.1.comp (contDiff_id.prodMk contDiff_const)
  convert h using 1
  funext t
  exact (polynomialRangeMean_eq (t, 0)).symm

private theorem residual_identity (a b t : ℝ) :
    polynomialMixedGeneratorMoment a b t - 4 * DGPS.Circle.AngularNormalization.a0 * polynomialMixedFeatureMoment a b t =
      (Real.sqrt 2 * DGPS.Circle.AngularNormalization.a0) *
        (t * mu a b c3_STR02954 t - t ^ 2 / 6 * mu a b C2 t +
          t ^ 2 / 6 + 4 * moment_EX054 t 0) := by
  let q := R a b t
  have he : (polynomialRangeGenerator (t, 0) -
      (4 * DGPS.Circle.AngularNormalization.a0) • e0_STR02955 (polynomialRangeFeature (t, 0))) * q =
      (Real.sqrt 2 * DGPS.Circle.AngularNormalization.a0) •
        (t • (c3_STR02954 * q) - (t ^ 2 / 6) • (C2 * q) +
          (t ^ 2 / 6 + 4 * moment_EX054 t 0) • q) := by
    apply ext_STR02954
    funext x
    change ((polynomialRangeGenerator (t, 0)).val x -
      4 * DGPS.Circle.AngularNormalization.a0 * (polynomialRangeFeature (t, 0)).val x) * q.val x =
      (Real.sqrt 2 * DGPS.Circle.AngularNormalization.a0) *
        (t * (Real.cos (3 * x) * q.val x) - t ^ 2 / 6 * (C2.val x * q.val x) +
          (t ^ 2 / 6 + 4 * moment_EX054 t 0) * q.val x)
    rw [polynomialRangeGenerator_residual_zero_tilt, C2_val]
    ring
  have hm := congrArg meanCLM_STR02954 he
  simp only [sub_mul, smul_mul_assoc, map_sub, map_add, map_smul, smul_eq_mul, q,
    R_mass] at hm
  unfold polynomialMixedGeneratorMoment polynomialMixedFeatureMoment eulerMean
  rw [actual_density]
  change meanCLM_STR02954 (polynomialRangeGenerator (t, 0) * R a b t) -
    4 * DGPS.Circle.AngularNormalization.a0 * meanCLM_STR02954
      (e0_STR02955 (polynomialRangeFeature (t, 0)) * R a b t) = _
  dsimp only [mu]
  simpa only [mul_one, add_assoc] using hm

private theorem bracket_second (a b : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => t * mu a b c3_STR02954 t - t ^ 2 / 6 * mu a b C2 t +
      t ^ 2 / 6 + 4 * moment_EX054 t 0) 0 = 0 := by
  have h3 := mu_smooth a b c3_STR02954
  have h2 := mu_smooth a b C2
  have hid : ContDiff ℝ ∞ (fun t : ℝ => t) := contDiff_id
  have hsq : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2 / 6) := (hid.pow 2).div_const 6
  have hp3 : ContDiff ℝ ∞ (fun t : ℝ => t * mu a b c3_STR02954 t) := hid.mul h3
  have hp2 : ContDiff ℝ ∞ (fun t : ℝ => t ^ 2 / 6 * mu a b C2 t) := hsq.mul h2
  have href : ContDiff ℝ ∞ (fun t : ℝ => 4 * moment_EX054 t 0) := contDiff_const.mul reference_smooth
  have ht3 : iteratedDeriv 2 (fun t : ℝ => t * mu a b c3_STR02954 t) 0 = 0 := by
    rw [iteratedDeriv_fun_mul ((hid.of_le (by simp)).contDiffAt) ((h3.of_le (by simp)).contDiffAt)]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, iteratedDeriv_fun_id, cosine3_first]
  have ht2 : iteratedDeriv 2 (fun t : ℝ => t ^ 2 / 6 * mu a b C2 t) 0 = 0 := by
    rw [iteratedDeriv_fun_mul (hsq.of_le (by simp)).contDiffAt
      ((h2.of_le (by simp)).contDiffAt)]
    norm_num [Finset.sum_range_succ, iteratedDeriv_div_const, iteratedDeriv_zero,
      iteratedDeriv_one, iteratedDeriv_fun_pow_zero, cosine2_zero]
  rw [iteratedDeriv_fun_add (((hp3.sub hp2).add hsq).of_le (by simp)).contDiffAt (href.of_le (by simp)).contDiffAt,
    iteratedDeriv_fun_add ((hp3.sub hp2).of_le (by simp)).contDiffAt (hsq.of_le (by simp)).contDiffAt,
    iteratedDeriv_fun_sub (hp3.of_le (by simp)).contDiffAt
      (hp2.of_le (by simp)).contDiffAt,
    ht3, ht2, iteratedDeriv_div_const, iteratedDeriv_const_mul_field,
    polynomialReferenceMoment_zero_tilt_second]
  norm_num [iteratedDeriv_fun_pow_zero]

/-- The genuine residual EXPECTATION has zero mixed second derivative.
The h*cos3 term and moving-reference constant cancel only after expectation. -/
theorem polynomialMixedGeneratorResidual_second (a b : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => polynomialMixedGeneratorMoment a b t -
      4 * DGPS.Circle.AngularNormalization.a0 * polynomialMixedFeatureMoment a b t) 0 = 0 := by
  have he := funext (residual_identity a b)
  rw [he, iteratedDeriv_const_mul_field, bracket_second, mul_zero]

private theorem actual_expectation_smooth (a b : ℝ) (F : (ℝ × ℝ) → PeriodicHolder_STR02968)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun t : ℝ =>
      eulerMean (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
        (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) (F (t, 0))) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => meanCLM_STR02954 (F (t, 0) * R a b t)) := meanCLM_STR02954.contDiff.comp
    ((hF.comp (contDiff_id.prodMk contDiff_const)).mul (R_smooth a b))
  convert hs using 1
  funext t
  unfold eulerMean
  rw [actual_density]

/-- Actual generator expectation SECOND derivative equals4*a0 times the
actual centered moment SECOND derivative on the mixed line. No pointwise
nonzero-field eigenfunction relation is used or concluded. -/
theorem polynomialMixedGeneratorMoment_second (a b : ℝ) :
    iteratedDeriv 2 (polynomialMixedGeneratorMoment a b) 0 =
      4 * DGPS.Circle.AngularNormalization.a0 * iteratedDeriv 2 (polynomialMixedFeatureMoment a b) 0 := by
  have hA := actual_expectation_smooth a b polynomialRangeGenerator polynomialRange_data_smooth.2.2.2.2.1
  have hm := actual_expectation_smooth a b (fun p => e0_STR02955 (polynomialRangeFeature p))
    (e0_STR02955.contDiff.comp polynomialRange_data_smooth.2.2.2.1)
  change ContDiff ℝ ∞ (polynomialMixedGeneratorMoment a b) at hA
  change ContDiff ℝ ∞ (polynomialMixedFeatureMoment a b) at hm
  have hcm : ContDiff ℝ ∞ (fun t => (4 * DGPS.Circle.AngularNormalization.a0) * polynomialMixedFeatureMoment a b t) := contDiff_const.mul hm
  have he := polynomialMixedGeneratorResidual_second a b
  rw [iteratedDeriv_fun_sub (hA.of_le (by simp)).contDiffAt
    (hcm.of_le (by simp)).contDiffAt, iteratedDeriv_const_mul_field] at he
  exact sub_eq_zero.mp he

end DGPS.Examples.PolynomialSpecies
