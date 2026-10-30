import DGPS.Examples.PolynomialSpeciesRangeChart
import DGPS.Examples.PolynomialSpeciesRangeInverse

/-! Public exact origin data of the SAME independent polynomial reference.
These constants are derived at (h,s)=(0,0) only, for genuine second-jet use. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem log_zero : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]

/-- The actual centered feature at the origin is the normalized second cosine. -/
theorem polynomialOriginFeature_eq : polynomialRangeFeature (0, 0) = polynomialOriginMode := by
  have h := polynomialRangeFeature_actual 0
  rw [polynomial_root_origin, ← polynomialOriginMode_actual] at h
  apply Subtype.ext
  have he := congrArg PeriodicHolder_STR02968.val h
  simp only [e0_val_STR02955] at he
  unfold PeriodicC2_STR02969.val at he
  exact he

/-- The actual independent reference is normalized Haar at its origin. -/
theorem polynomialOriginReference_eq : polynomialRangeReference (0, 0) = 1 := by
  rw [polynomialRangeReference, log_zero, map_zero, rho_zero_STR02955]

/-- Actual Haar centering of the same feature. -/
theorem polynomialOriginFeature_mean_zero : meanCLM_STR02954 (e0_STR02955 polynomialOriginMode) = 0 := by
  have h := polynomialRangeFeature_centered (0, 0)
  rw [polynomialOriginFeature_eq, polynomialOriginReference_eq, mul_one] at h
  exact h

/-- The weighted-generator identity is asserted ONLY at the actual origin. -/
theorem polynomialOriginGenerator_eq : polynomialRangeGenerator (0, 0) =
    (4 * DGPS.Circle.AngularNormalization.a0) • e0_STR02955 polynomialOriginMode := by
  unfold polynomialRangeGenerator
  rw [log_zero, polynomialOriginFeature_eq, map_zero, zero_mul, sub_zero]
  apply ext_STR02954
  funext t
  change DGPS.Circle.AngularNormalization.a0 * (-deriv (deriv polynomialOriginMode.val) t) =
    (4 * DGPS.Circle.AngularNormalization.a0) * polynomialOriginMode.val t
  rw [polynomialOriginMode_second]
  ring

/-- The exact physical squared-gradient mean, derived by periodic integration by
parts and the actual Haar unit normalization. -/
theorem polynomialOriginGradientSq_mean : meanCLM_STR02954 (polynomialRangeGradientSq (0, 0)) =
    4 * DGPS.Circle.AngularNormalization.a0 := by
  let H := e1_STR02955 polynomialOriginMode * e1_STR02955 polynomialOriginMode +
    e0_STR02955 polynomialOriginMode * e2_STR02955 polynomialOriginMode
  have hd : ∀ t, HasDerivAt (fun s => polynomialOriginMode.val s * deriv polynomialOriginMode.val s)
      (H.val t) t := by
    intro t
    convert ((polynomialOriginMode.isC2.2.1 t).hasDerivAt.mul
      (polynomialOriginMode.isC2.2.2.1 t).hasDerivAt) using 1
    rfl
  have hp : polynomialOriginMode.val (2 * Real.pi) * deriv polynomialOriginMode.val (2 * Real.pi) =
      polynomialOriginMode.val 0 * deriv polynomialOriginMode.val 0 := by
    rw [show polynomialOriginMode.val (2 * Real.pi) = polynomialOriginMode.val 0 by
      simpa using polynomialOriginMode.isC2.1 0,
      show deriv polynomialOriginMode.val (2 * Real.pi) = deriv polynomialOriginMode.val 0 by
        simpa using (periodic_deriv_STR02901 polynomialOriginMode.isC2.1) 0]
  have hm : meanCLM_STR02954 H = 0 := ftc_mean_STR02955 hd H.isPerHolder.2.1 hp
  have hsecond : e2_STR02955 polynomialOriginMode = (-4 : ℝ) • e0_STR02955 polynomialOriginMode := by
    apply ext_STR02954
    funext t
    exact polynomialOriginMode_second t
  dsimp only [H] at hm
  rw [map_add, hsecond, mul_smul_comm, map_smul, polynomialOriginMode_unit] at hm
  have hnorm : meanCLM_STR02954 (e1_STR02955 polynomialOriginMode * e1_STR02955 polynomialOriginMode) = 4 := by
    change meanCLM_STR02954 (e1_STR02955 polynomialOriginMode * e1_STR02955 polynomialOriginMode) + (-4 : ℝ) * 1 = 0 at hm
    linarith
  unfold polynomialRangeGradientSq
  rw [polynomialOriginFeature_eq, map_smul, hnorm]
  change DGPS.Circle.AngularNormalization.a0 * 4 = 4 * DGPS.Circle.AngularNormalization.a0
  ring

end DGPS.Examples.PolynomialSpecies
