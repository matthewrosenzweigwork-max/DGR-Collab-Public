import DGPS.Examples.PolynomialSpeciesRangeHalfTurn

/-! Exact half-turn covariance of the TRUE generator and squared physical
feature gradient in the independent polynomial reference. -/

noncomputable section
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem derivative_shift (f g : ℝ → ℝ) (he : ∀ t, f (t + Real.pi) = g t) (t : ℝ) :
    deriv f (t + Real.pi) = deriv g t := by
  have hfun : (fun y : ℝ => f (y + Real.pi)) = g := funext he
  have h := deriv_comp_add_const (f := f) Real.pi t
  rw [hfun] at h
  exact h.symm

/-- The logarithmic drift is transported without an extra sign. -/
theorem polynomialRangeLogWeight_derivative_half_turn (h s t : ℝ) :
    deriv (polynomialRangeLogWeight (-h, s)).val (t + Real.pi) =
      deriv (polynomialRangeLogWeight (h, s)).val t :=
  derivative_shift _ _ (polynomialRangeLogWeight_half_turn h s) t

/-- First spatial derivative of the actual centered feature. -/
theorem polynomialRangeFeature_derivative_half_turn (h s t : ℝ) :
    deriv (polynomialRangeFeature (-h, s)).val (t + Real.pi) =
      deriv (polynomialRangeFeature (h, s)).val t :=
  derivative_shift _ _ (polynomialRangeFeature_half_turn h s) t

/-- Second spatial derivative, still of that same centered feature. -/
theorem polynomialRangeFeature_second_half_turn (h s t : ℝ) :
    deriv (deriv (polynomialRangeFeature (-h, s)).val) (t + Real.pi) =
      deriv (deriv (polynomialRangeFeature (h, s)).val) t :=
  derivative_shift _ _ (polynomialRangeFeature_derivative_half_turn h s) t

/-- The actual weighted generator includes the transported logarithmic drift. -/
theorem polynomialRangeGenerator_half_turn (h s t : ℝ) :
    (polynomialRangeGenerator (-h, s)).val (t + Real.pi) =
      (polynomialRangeGenerator (h, s)).val t := by
  change DGPS.Circle.AngularNormalization.a0 *
      (-deriv (deriv (polynomialRangeFeature (-h, s)).val) (t + Real.pi) -
        deriv (polynomialRangeLogWeight (-h, s)).val (t + Real.pi) *
          deriv (polynomialRangeFeature (-h, s)).val (t + Real.pi)) =
    DGPS.Circle.AngularNormalization.a0 *
      (-deriv (deriv (polynomialRangeFeature (h, s)).val) t -
        deriv (polynomialRangeLogWeight (h, s)).val t *
          deriv (polynomialRangeFeature (h, s)).val t)
  rw [polynomialRangeFeature_second_half_turn, polynomialRangeLogWeight_derivative_half_turn,
    polynomialRangeFeature_derivative_half_turn]

/-- Physical squared-gradient normalization is retained exactly. -/
theorem polynomialRangeGradientSq_half_turn (h s t : ℝ) :
    (polynomialRangeGradientSq (-h, s)).val (t + Real.pi) =
      (polynomialRangeGradientSq (h, s)).val t := by
  change DGPS.Circle.AngularNormalization.a0 *
      (deriv (polynomialRangeFeature (-h, s)).val (t + Real.pi) *
        deriv (polynomialRangeFeature (-h, s)).val (t + Real.pi)) =
    DGPS.Circle.AngularNormalization.a0 *
      (deriv (polynomialRangeFeature (h, s)).val t * deriv (polynomialRangeFeature (h, s)).val t)
  rw [polynomialRangeFeature_derivative_half_turn]

end DGPS.Examples.PolynomialSpecies
