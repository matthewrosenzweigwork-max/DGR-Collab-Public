import DGPS.Examples.PolynomialSpeciesRangeDeficit
import DGPS.Examples.PolynomialFiniteProfileCoefficients

/-! Exact nonlocal remainder decomposition of the ACTUAL physical deficit,
and the fourth-coefficient algebra for the genuine cos-one finite profiles.
The estimates of the true generator and feature moments remain separate. -/

noncomputable section
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- Exact identity, valid at every independent reference and every C2 chart.
The two true residual expectations are retained explicitly; no nonzero-field
eigenfunction identity is asserted. -/
theorem polynomialRangeDeficit_nonlocal_remainder (p : ℝ × ℝ) (γ : ℝ)
    (u : PeriodicC2_STR02969) :
    let L := e0_STR02955 (polynomialRangeLogWeight p)
    let m := eulerMean L u (e0_STR02955 (polynomialRangeFeature p))
    let A := eulerMean L u (polynomialRangeGenerator p)
    let J := eulerMean L u (polynomialRangeGradientSq p)
    polynomialRangeDeficit p (DGPS.Circle.AngularNormalization.a0 * (1 + γ)) u =
      eulerFisher L u - 2 * DGPS.Circle.AngularNormalization.a0 * eulerEntropy L u +
        3 * DGPS.Circle.AngularNormalization.a0 * m ^ 2 -
        2 * DGPS.Circle.AngularNormalization.a0 * γ * polynomialRangeGap p u +
        2 * eta * m * (A - 4 * DGPS.Circle.AngularNormalization.a0 * m) +
        eta ^ 2 * m ^ 2 * (J - 4 * DGPS.Circle.AngularNormalization.a0) := by
  dsimp only
  unfold polynomialRangeDeficit polynomialRangeGap
  linear_combination (DGPS.Circle.AngularNormalization.a0 *
    (eulerMean (e0_STR02955 (polynomialRangeLogWeight p)) u
      (e0_STR02955 (polynomialRangeFeature p))) ^ 2) * eta_relation

/-- Finite-profile fourth coefficient after the TRUE moment coefficient is
inserted. This is coefficient algebra; it does not assume or certify a
uniform asymptotic estimate for the actual moments. -/
def polynomialFiniteNonlocalFourth (a b c d : ℝ) : ℝ :=
  polynomialFiniteI4 a b c d - 2 * polynomialFiniteH4 a b c d +
    6 * (c / 2 + a / 12 + (a ^ 2 - b ^ 2) / 8) ^ 2

theorem polynomialFiniteNonlocalFourth_squares (a b c d : ℝ) :
    polynomialFiniteNonlocalFourth a b c d =
      3 * (c + (a + a ^ 2 - b ^ 2) / 6) ^ 2 +
        (3 / 2) * (d + b * (1 + a) / 6) ^ 2 +
        (a ^ 2 + b ^ 2) / 12 + a * (a ^ 2 + b ^ 2) / 12 +
        (a ^ 4 + b ^ 4) / 24 := by
  unfold polynomialFiniteNonlocalFourth
  rw [polynomialFiniteI4_eq, polynomialFiniteH4_eq]
  ring

/-- The actual mixed range correction cancels precisely the two completed
squares of the finite coefficient. No optimizer assertion is involved. -/
theorem polynomialFiniteNonlocalFourth_mixed (a b : ℝ) :
    polynomialFiniteNonlocalFourth a b (-(a + a ^ 2 - b ^ 2) / 6)
        (-(b * (1 + a)) / 6) =
      (a ^ 2 + b ^ 2) / 12 + a * (a ^ 2 + b ^ 2) / 12 +
        (a ^ 4 + b ^ 4) / 24 := by
  rw [polynomialFiniteNonlocalFourth_squares]
  ring

end DGPS.Examples.PolynomialSpecies
