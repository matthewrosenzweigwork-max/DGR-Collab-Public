import DGPS.Examples.PolynomialSpeciesRangeDeficit
import DGPS.Examples.PolynomialSpeciesReducedGap

/-! The literal amplitude radial derivative of the actual independent-parameter
reduced deficit. This definition fixes the SAME graph convention shared by the
origin, field and selected-rate estimates; it imposes no analytic hypothesis. -/

noncomputable section
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Radial amplitude derivative with independent reference pair and rate.
The derivative varies only amplitude; the original graph correction varies
with it and is retained inside the actual physical deficit. -/
def polynomialReducedDeficitRadial (ψ : PolynomialRangeParameters → E_STR02969)
    (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun y : ℝ × ℝ => polynomialRangeDeficit θ.1
    (DGPS.Circle.AngularNormalization.a0 * (1 + θ.2))
      (polynomialGapLift ψ θ y)) x x

end DGPS.Examples.PolynomialSpecies
