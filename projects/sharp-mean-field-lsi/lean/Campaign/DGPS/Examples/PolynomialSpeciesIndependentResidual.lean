import DGPS.Examples.PolynomialSpeciesRangeHalfTurn

/-! The true independent-reference residual at s=0, before any selected-root
restriction. This is not the false nonzero-field eigenfunction identity. -/

noncomputable section
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Examples.PolynomialCenteredResidual

namespace DGPS.Examples.PolynomialSpecies

/-- Exact physical generator-minus-4*a0*feature for the independent reference
q_{h,0}. Its constant term retains the ACTUAL reference feature mean. -/
theorem polynomialRangeGenerator_residual_zero_tilt (h x : ℝ) :
    (polynomialRangeGenerator (h, 0)).val x -
        4 * DGPS.Circle.AngularNormalization.a0 * (polynomialRangeFeature (h, 0)).val x =
      Real.sqrt 2 * DGPS.Circle.AngularNormalization.a0 *
        (h * Real.cos (3 * x) - h ^ 2 / 6 * Real.cos (2 * x) +
          h ^ 2 / 6 + 4 * moment_EX054 h 0) := by
  let φ := polynomialRangeFeature (h, 0)
  let L := polynomialRangeLogWeight (h, 0)
  let m := moment_EX054 h 0
  have hφ : φ.val = Phi_EX057 h m := by
    funext t
    rw [polynomialRangeFeature_val]
    unfold Phi_EX057
    rw [feature_coe_EX057]
  have hdφ : deriv φ.val = fun t => Real.sqrt 2 * Pd_EX057 h t := by
    rw [hφ]
    funext t
    exact (hasDerivAt_Phi_EX057 h m t).deriv
  have hddφ : deriv (deriv φ.val) = fun t => Real.sqrt 2 * Pdd_EX057 h t := by
    rw [hdφ]
    funext t
    exact (hasDerivAt_sqrtPd_EX057 h t).deriv
  have hL : L.val = fun t => h * Real.cos t := by
    funext t
    rw [polynomialRangeLogWeight_val_explicit]
    ring
  have hdL : deriv L.val = fun t => -h * Real.sin t := by
    rw [hL]
    funext t
    exact ((Real.hasDerivAt_cos t).const_mul h).deriv.trans (by ring)
  change DGPS.Circle.AngularNormalization.a0 *
      (-deriv (deriv φ.val) x - deriv L.val x * deriv φ.val x) -
        4 * DGPS.Circle.AngularNormalization.a0 * φ.val x = _
  rw [hddφ, hdL, hdφ, hφ]
  calc
    _ = Real.sqrt 2 * DGPS.Circle.AngularNormalization.a0 *
        (h * Real.sin x * Pd_EX057 h x + h * Real.cos x + 4 * m) := by
      unfold Pdd_EX057 Phi_EX057
      ring
    _ = _ := by rw [trig_A_EX057]

end DGPS.Examples.PolynomialSpecies
