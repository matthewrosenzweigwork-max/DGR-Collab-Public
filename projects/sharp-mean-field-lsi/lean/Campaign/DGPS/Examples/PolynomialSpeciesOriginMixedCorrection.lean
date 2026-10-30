import DGPS.Examples.PolynomialSpeciesOriginSecondCorrection

/-! The explicit mixed field/amplitude correction in the actual complement.
Its inverse identity uses the actual origin range equivalence. Identifying it
with the actual graph second derivative additionally requires the genuine mixed
Euler forcing; that identification is not assumed or claimed here. -/

noncomputable section
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- The SECOND derivative correction on the line (ta,tb,(t,0),0).
The quadratic Taylor coefficient is one half of this element. -/
def polynomialOriginMixedSecondCorrection (a b : ℝ) : E_STR02969 :=
  polynomialOriginSecondCorrection a b +
    a • polynomialOriginSecondCorrection 1 0 + b • polynomialOriginSecondCorrection 1 1

theorem polynomialOriginMixedSecondCorrection_val (a b t : ℝ) :
    (polynomialOriginMixedSecondCorrection a b : PeriodicC2_STR02969).val t =
      -(a + a ^ 2 - b ^ 2) / 3 * Real.cos (2 * t) -
        b * (1 + a) / 3 * Real.sin (2 * t) := by
  change (polynomialOriginSecondCorrection a b : PeriodicC2_STR02969).val t +
    a * (polynomialOriginSecondCorrection 1 0 : PeriodicC2_STR02969).val t +
    b * (polynomialOriginSecondCorrection 1 1 : PeriodicC2_STR02969).val t = _
  rw [polynomialOriginSecondCorrection_val, polynomialOriginSecondCorrection_val,
    polynomialOriginSecondCorrection_val]
  ring

theorem polynomialOriginMixedSecondCorrection_inverse (a b t : ℝ) :
    ((polynomialOriginRangeEquiv (polynomialOriginMixedSecondCorrection a b) : Y_STR02969) :
      PeriodicHolder_STR02968).val t =
      -DGPS.Circle.AngularNormalization.a0 *
        (4 * (a + a ^ 2 - b ^ 2) * Real.cos (2 * t) +
          2 * b * (1 + a) * Real.sin (2 * t)) := by
  unfold polynomialOriginMixedSecondCorrection
  rw [map_add, map_add, map_smul, map_smul]
  change ((polynomialOriginRangeEquiv (polynomialOriginSecondCorrection a b) : Y_STR02969) :
      PeriodicHolder_STR02968).val t +
    a * ((polynomialOriginRangeEquiv (polynomialOriginSecondCorrection 1 0) : Y_STR02969) :
      PeriodicHolder_STR02968).val t +
    b * ((polynomialOriginRangeEquiv (polynomialOriginSecondCorrection 1 1) : Y_STR02969) :
      PeriodicHolder_STR02968).val t = _
  rw [polynomialOriginSecondCorrection_inverse, polynomialOriginSecondCorrection_inverse,
    polynomialOriginSecondCorrection_inverse]
  ring

end DGPS.Examples.PolynomialSpecies
