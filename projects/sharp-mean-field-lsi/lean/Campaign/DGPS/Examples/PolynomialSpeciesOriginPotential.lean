import DGPS.Examples.PolynomialSpeciesOriginData
import DGPS.Examples.PolynomialSpeciesRangeMap

/-! Exact pure-amplitude origin potential, before differentiation. The true
normalized feature moment and gradient-square moment remain in the identity;
only the actual Haar-origin generator identity is used. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem amplitude_second (a b : ℝ) :
    e2_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915) =
      (-1 : ℝ) • e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915) := by
  have hc : e2_STR02955 cosC2_STR02915 = (-1 : ℝ) • e0_STR02955 cosC2_STR02915 := by
    apply ext_STR02954
    funext t
    rw [e2_val_STR02955, PeriodicHolder_STR02968.val_smul]
    simp only [cosC2_val_STR02915, e0_val_STR02955, Pi.smul_apply, smul_eq_mul]
    rw [Real.deriv_cos']
    change deriv (-Real.sin) t = -1 * Real.cos t
    rw [((Real.hasDerivAt_sin t).neg).deriv]
    ring
  have hs : e2_STR02955 sinC2_STR02915 = (-1 : ℝ) • e0_STR02955 sinC2_STR02915 := by
    apply ext_STR02954
    funext t
    rw [e2_val_STR02955, PeriodicHolder_STR02968.val_smul]
    simp only [sinC2_val_STR02915, e0_val_STR02955, Pi.smul_apply, smul_eq_mul]
    rw [Real.deriv_sin]
    simp [Real.deriv_cos']
  rw [map_add, map_smul, map_smul, hc, hs, map_add, map_smul, map_smul]
  apply ext_STR02954
  funext t
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The actual nonlinear potential on a pure first-harmonic path. Its linear
terms cancel at the actual rate a0. The moments are still the genuine normalized
moments, not a prescribed polynomial or a graph-jet assumption. -/
theorem polynomialOriginPotential_amplitude (a b z : ℝ) :
    polynomialRangeEulerPotential (0, 0) DGPS.Circle.AngularNormalization.a0
      (z • (a • cosC2_STR02915 + b • sinC2_STR02915)) =
    let v := a • cosC2_STR02915 + b • sinC2_STR02915
    let φ := e0_STR02955 polynomialOriginMode
    let j := polynomialRangeGradientSq (0, 0)
    let m := eulerMean (0 : PeriodicHolder_STR02968) (z • v) φ
    let J := eulerMean (0 : PeriodicHolder_STR02968) (z • v) j
    (-DGPS.Circle.AngularNormalization.a0 * z ^ 2) •
      (e1_STR02955 v * e1_STR02955 v) +
      (2 * eta * (7 * DGPS.Circle.AngularNormalization.a0 + eta * J) * m) • φ +
      (eta ^ 2 * m ^ 2) • j := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  let φ := e0_STR02955 polynomialOriginMode
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  have hA : eulerMean (0 : PeriodicHolder_STR02968) (z • v)
      (polynomialRangeGenerator (0, 0)) =
      (4 * DGPS.Circle.AngularNormalization.a0) * eulerMean (0 : PeriodicHolder_STR02968) (z • v) φ := by
    rw [polynomialOriginGenerator_eq]
    simp only [eulerMean, smul_mul_assoc, map_smul, smul_eq_mul, φ]
  unfold polynomialRangeEulerPotential
  dsimp only
  simp only [hL, polynomialOriginFeature_eq, map_zero, zero_mul, sub_zero]
  dsimp only [v, φ] at hA
  rw [hA, polynomialOriginGenerator_eq]
  simp only [map_smul, amplitude_second]
  apply ext_STR02954
  funext t
  have hz : PeriodicHolder_STR02968.val 0 t = 0 := rfl
  simp only [hz, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_mul_STR02954,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

/-- The coefficient multiplying the genuine moment at the path origin is6*a0.
This is where the exact eta relation enters the quadratic forcing. -/
theorem polynomialOriginPotential_moment_coefficient :
    2 * eta * (7 * DGPS.Circle.AngularNormalization.a0 + eta *
      eulerMean (0 : PeriodicHolder_STR02968) 0 (polynomialRangeGradientSq (0, 0))) =
      6 * DGPS.Circle.AngularNormalization.a0 := by
  have hJ : eulerMean (0 : PeriodicHolder_STR02968) 0
      (polynomialRangeGradientSq (0, 0)) = 4 * DGPS.Circle.AngularNormalization.a0 := by
    simpa only [eulerMean, eulerDensity, map_zero, zero_add, rho_zero_STR02955, mul_one] using
      polynomialOriginGradientSq_mean
  rw [hJ]
  nlinarith [congrArg (fun x : ℝ => 2 * DGPS.Circle.AngularNormalization.a0 * x) eta_relation]

end DGPS.Examples.PolynomialSpecies
