import DGPS.Examples.PolynomialSpeciesRangeHalfTurn

/-! Genuine SAME-field spatial reflection of the independent polynomial
reference and its actual generator data. This is distinct from half-turn
field reversal and uses no symmetry theorem for a different model. -/

noncomputable section
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

theorem polynomialRangeLogWeight_reflection (h s t : ℝ) :
    (polynomialRangeLogWeight (h, s)).val (-t) = (polynomialRangeLogWeight (h, s)).val t := by
  rw [polynomialRangeLogWeight_val_explicit, polynomialRangeLogWeight_val_explicit,
    show 2 * (-t) = -(2 * t) by ring, Real.cos_neg, Real.cos_neg]

theorem polynomialRangeFeature_reflection (h s t : ℝ) :
    (polynomialRangeFeature (h, s)).val (-t) = (polynomialRangeFeature (h, s)).val t := by
  rw [polynomialRangeFeature_val, polynomialRangeFeature_val,
    DGPS.Examples.PolynomialCenteredResidual.feature_coe_EX057,
    DGPS.Examples.PolynomialCenteredResidual.feature_coe_EX057,
    show 2 * (-t) = -(2 * t) by ring, Real.cos_neg, Real.cos_neg]

theorem polynomialRangeReference_reflection (h s t : ℝ) :
    (polynomialRangeReference (h, s)).val (-t) = (polynomialRangeReference (h, s)).val t := by
  rw [polynomialRangeReference, rho_val_STR02954, rho_val_STR02954]
  simp only [rhoT_STR02901, zero_mul, zero_add, e0_val_STR02955,
    polynomialRangeLogWeight_reflection]

private theorem derivative_even (f : ℝ → ℝ) (he : ∀ t, f (-t) = f t) (t : ℝ) :
    deriv f (-t) = -deriv f t := by
  have h := congrArg (fun g : ℝ → ℝ => deriv g t) (funext he)
  rw [deriv_comp_neg] at h
  linarith only [h]

private theorem second_even (f : PeriodicC2_STR02969)
    (he : ∀ t, f.val (-t) = f.val t) (t : ℝ) :
    deriv (deriv f.val) (-t) = deriv (deriv f.val) t := by
  have hf : pb_STR02916 (-1) 0 f.val = f.val := by
    funext x
    simpa only [pb_STR02916, neg_one_mul, add_zero] using he x
  have hd := deriv2_pb_STR02916 (σ := -1) (c := 0) (Or.inr rfl)
    f.isC2.2.1 f.isC2.2.2.1
  rw [hf] at hd
  simpa only [pb_STR02916, neg_one_mul, add_zero] using (congrFun hd t).symm

theorem polynomialRangeLogWeight_derivative_reflection (h s t : ℝ) :
    deriv (polynomialRangeLogWeight (h, s)).val (-t) =
      -deriv (polynomialRangeLogWeight (h, s)).val t :=
  derivative_even _ (polynomialRangeLogWeight_reflection h s) t

theorem polynomialRangeFeature_derivative_reflection (h s t : ℝ) :
    deriv (polynomialRangeFeature (h, s)).val (-t) =
      -deriv (polynomialRangeFeature (h, s)).val t :=
  derivative_even _ (polynomialRangeFeature_reflection h s) t

theorem polynomialRangeFeature_second_reflection (h s t : ℝ) :
    deriv (deriv (polynomialRangeFeature (h, s)).val) (-t) =
      deriv (deriv (polynomialRangeFeature (h, s)).val) t :=
  second_even _ (polynomialRangeFeature_reflection h s) t

/-- The true generator is even because BOTH first spatial derivatives are
odd, while the second derivative is even. No feature eigenrelation is used. -/
theorem polynomialRangeGenerator_reflection (h s t : ℝ) :
    (polynomialRangeGenerator (h, s)).val (-t) = (polynomialRangeGenerator (h, s)).val t := by
  change DGPS.Circle.AngularNormalization.a0 *
      (-deriv (deriv (polynomialRangeFeature (h, s)).val) (-t) -
        deriv (polynomialRangeLogWeight (h, s)).val (-t) *
          deriv (polynomialRangeFeature (h, s)).val (-t)) = _
  rw [polynomialRangeFeature_second_reflection, polynomialRangeLogWeight_derivative_reflection,
    polynomialRangeFeature_derivative_reflection]
  change _ = DGPS.Circle.AngularNormalization.a0 *
    (-deriv (deriv (polynomialRangeFeature (h, s)).val) t -
      deriv (polynomialRangeLogWeight (h, s)).val t * deriv (polynomialRangeFeature (h, s)).val t)
  ring

theorem polynomialRangeGradientSq_reflection (h s t : ℝ) :
    (polynomialRangeGradientSq (h, s)).val (-t) = (polynomialRangeGradientSq (h, s)).val t := by
  change DGPS.Circle.AngularNormalization.a0 *
    (deriv (polynomialRangeFeature (h, s)).val (-t) * deriv (polynomialRangeFeature (h, s)).val (-t)) = _
  rw [polynomialRangeFeature_derivative_reflection]
  change _ = DGPS.Circle.AngularNormalization.a0 *
    (deriv (polynomialRangeFeature (h, s)).val t * deriv (polynomialRangeFeature (h, s)).val t)
  ring

end DGPS.Examples.PolynomialSpecies
