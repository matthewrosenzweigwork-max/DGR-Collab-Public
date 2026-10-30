import DGPS.Circle.AngularNormalization

/-! Literal physical fourth-order coefficient, in the SAME four independent
coefficient coordinates used by the actual scaled deficit. -/

noncomputable section
namespace DGPS.Examples.PolynomialSpecies

/-- Physical a0 is retained; sigma does not enter this fourth-order coefficient. -/
def polynomialScaledQuartic (c : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  DGPS.Circle.AngularNormalization.a0 *
    ((c.1^2+c.2.1^2)/12 + c.1*(c.1^2+c.2.1^2)/12 +
      (c.1^4+c.2.1^4)/24-c.2.2.1*(c.1^2+c.2.1^2)/2)

end DGPS.Examples.PolynomialSpecies
