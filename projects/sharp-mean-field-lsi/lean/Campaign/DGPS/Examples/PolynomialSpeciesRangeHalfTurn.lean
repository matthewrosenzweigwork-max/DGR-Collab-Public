import DGPS.Examples.PolynomialSpeciesRangeChart
import DGPS.Examples.PolynomialSpeciesRangeOrigin
import DGPS.Frontier.STR029.T16

/-! The actual polynomial reference under a half-turn: h changes sign, while
s stays fixed. Only the generic periodic mean pullback is reused from STR029;
no symmetry of the different cos3 model is imported as a polynomial identity. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem base_zero (t : ℝ) : (polynomialRangeBaseFeature 0).val t = Real.cos (2 * t) := by
  have hm : moment_EX054 0 0 = 0 := by simpa only [polynomial_root_origin] using polynomial_mean_origin
  have he := polynomialRangeFeature_val (0, 0) t
  simp only [polynomialRangeFeature, PeriodicC2_STR02969.val_smul,
    PeriodicC2_STR02969.val_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    polynomialRangeMean_eq, hm, zero_smul, sub_zero] at he
  rw [DGPS.Examples.PolynomialCenteredResidual.feature_coe_EX057] at he
  norm_num at he
  exact he

private theorem base_difference (t : ℝ) :
    (polynomialRangeBaseFeature 3).val t - (polynomialRangeBaseFeature (-3)).val t = -2 * Real.cos t := by
  have h1 := polynomialRangeFeature_val (3, 0) t
  have h2 := polynomialRangeFeature_val (-3, 0) t
  simp only [polynomialRangeFeature, PeriodicC2_STR02969.val_smul,
    PeriodicC2_STR02969.val_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    polynomialRangeMean_eq] at h1 h2
  rw [moment_even_EX054 3 0] at h2
  rw [DGPS.Examples.PolynomialCenteredResidual.feature_coe_EX057] at h1 h2
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h1' := mul_left_cancel₀ hn h1
  have h2' := mul_left_cancel₀ hn h2
  norm_num at h1' h2'
  linarith

private theorem base_val (h t : ℝ) : (polynomialRangeBaseFeature h).val t =
    Real.cos (2 * t) - (h / 3) * Real.cos t := by
  have he : (polynomialRangeBaseFeature h).val t = (polynomialRangeBaseFeature 0).val t +
      (h / 6) * ((polynomialRangeBaseFeature 3).val t - (polynomialRangeBaseFeature (-3)).val t) := by
    simp only [polynomialRangeBaseFeature, PeriodicC2_STR02969.val_sub,
      PeriodicC2_STR02969.val_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, base_zero, base_difference]
  ring

private theorem log_val (h s t : ℝ) : (polynomialRangeLogWeight (h, s)).val t =
    h * Real.cos t - s * (Real.cos (2 * t) - (h / 3) * Real.cos t) := by
  have he : (polynomialRangeLogWeight (h, s)).val t =
      (h / 2) * ((polynomialRangeBaseFeature (-3)).val t - (polynomialRangeBaseFeature 3).val t) -
        s * (polynomialRangeBaseFeature h).val t := by
    simp only [polynomialRangeLogWeight, polynomialRangeBaseFeature,
      PeriodicC2_STR02969.val_sub, PeriodicC2_STR02969.val_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, base_val, base_val, base_val]
  ring

/-- Public actual scalar value of the uncentered polynomial feature. This avoids
unfolding an imported private mode constructor in subsequent genuine calculus. -/
theorem polynomialRangeBaseFeature_val_explicit (h t : ℝ) :
    (polynomialRangeBaseFeature h).val t = Real.cos (2 * t) - (h / 3) * Real.cos t :=
  base_val h t

/-- Public actual logarithmic weight for independent h,s. The selected root is
not differentiated when this analytic extension is later restricted. -/
theorem polynomialRangeLogWeight_val_explicit (h s t : ℝ) :
    (polynomialRangeLogWeight (h, s)).val t =
      h * Real.cos t - s * (Real.cos (2 * t) - (h / 3) * Real.cos t) :=
  log_val h s t

/-- Actual uncentered feature covariance under field reversal and half-turn. -/
theorem polynomialRangeBaseFeature_half_turn (h t : ℝ) :
    (polynomialRangeBaseFeature (-h)).val (t + Real.pi) =
      (polynomialRangeBaseFeature h).val t := by
  rw [base_val, base_val, show 2 * (t + Real.pi) = 2 * t + 2 * Real.pi by ring,
    Real.cos_add_two_pi, Real.cos_add_pi]
  ring

/-- The exact independent logarithmic reference, with s fixed. -/
theorem polynomialRangeLogWeight_half_turn (h s t : ℝ) :
    (polynomialRangeLogWeight (-h, s)).val (t + Real.pi) =
      (polynomialRangeLogWeight (h, s)).val t := by
  rw [log_val, log_val, show 2 * (t + Real.pi) = 2 * t + 2 * Real.pi by ring,
    Real.cos_add_two_pi, Real.cos_add_pi]
  ring

private theorem partition_half_turn (h s : ℝ) :
    Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (-h, s))) =
      Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, s))) := by
  let f := fun t : ℝ => Real.exp ((polynomialRangeLogWeight (-h, s)).val t)
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro t
    dsimp only [f]
    rw [(polynomialRangeLogWeight (-h, s)).isC2.1 t]
  rw [Z_eq_meanT_STR02954, Z_eq_meanT_STR02954]
  simp only [zero_mul, zero_add, e0_val_STR02955]
  calc
    meanT_STR02901 f = meanT_STR02901 (pb_STR02916 1 Real.pi f) :=
      (meanT_pb_STR02916 (Or.inl rfl) Real.pi hp).symm
    _ = _ := by
      congr 1
      funext t
      simp only [pb_STR02916, one_mul, f, polynomialRangeLogWeight_half_turn]

private theorem reference_val (p : ℝ × ℝ) (t : ℝ) :
    (polynomialRangeReference p).val t = Real.exp ((polynomialRangeLogWeight p).val t) /
      Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight p)) := by
  rw [polynomialRangeReference, rho_val_STR02954]
  simp only [rhoT_STR02901, zero_mul, zero_add, e0_val_STR02955, Z_eq_meanT_STR02954]

/-- The normalized moving reference has the same actual half-turn covariance. -/
theorem polynomialRangeReference_half_turn (h s t : ℝ) :
    (polynomialRangeReference (-h, s)).val (t + Real.pi) =
      (polynomialRangeReference (h, s)).val t := by
  rw [reference_val, reference_val, polynomialRangeLogWeight_half_turn, partition_half_turn]

/-- Centering is against the same normalized reference on both sides. -/
theorem polynomialRangeMean_half_turn (h s : ℝ) :
    polynomialRangeMean (-h, s) = polynomialRangeMean (h, s) := by
  let f := fun t : ℝ => (polynomialRangeBaseFeature (-h)).val t *
    (polynomialRangeReference (-h, s)).val t
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro t
    dsimp only [f]
    rw [(polynomialRangeBaseFeature (-h)).isC2.1 t,
      (polynomialRangeReference (-h, s)).isPerHolder.1 t]
  unfold polynomialRangeMean
  rw [meanCLM_apply_STR02954, meanCLM_apply_STR02954]
  change meanT_STR02901 f = meanT_STR02901 (fun t : ℝ =>
    (polynomialRangeBaseFeature h).val t * (polynomialRangeReference (h, s)).val t)
  calc
    meanT_STR02901 f = meanT_STR02901 (pb_STR02916 1 Real.pi f) :=
      (meanT_pb_STR02916 (Or.inl rfl) Real.pi hp).symm
    _ = _ := by
      congr 1
      funext t
      simp only [pb_STR02916, one_mul, f, polynomialRangeBaseFeature_half_turn,
        polynomialRangeReference_half_turn]

private theorem feature_val (h s t : ℝ) : (polynomialRangeFeature (h, s)).val t =
    Real.sqrt 2 * ((polynomialRangeBaseFeature h).val t - polynomialRangeMean (h, s)) := by
  rw [polynomialRangeFeature_val, polynomialRangeMean_eq, base_val,
    DGPS.Examples.PolynomialCenteredResidual.feature_coe_EX057]

/-- The ACTUAL centered polynomial feature transforms exactly; no eigenfunction
identity or selected-root parity is a premise. -/
theorem polynomialRangeFeature_half_turn (h s t : ℝ) :
    (polynomialRangeFeature (-h, s)).val (t + Real.pi) =
      (polynomialRangeFeature (h, s)).val t := by
  rw [feature_val, feature_val, polynomialRangeBaseFeature_half_turn, polynomialRangeMean_half_turn]

end DGPS.Examples.PolynomialSpecies
