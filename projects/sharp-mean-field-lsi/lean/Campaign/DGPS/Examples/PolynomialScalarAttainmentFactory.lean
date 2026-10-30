import DGPS.Examples.PolynomialHaarTrialBounds
import DGPS.Examples.PolynomialScalarAttainment
import DGPS.Examples.PolynomialReferencePoincare
import DGPS.Examples.PolynomialGaussianPoincare

/-! Actual canonical scalar attainment before optimizer classification. The
strict spectral barrier is discharged by the genuine fixed Haar trial and the
actual reference Poincare lower bound; every original competitor remains allowed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

/-- Actual strict scalar/reference-Poincare/Gaussian comparison, obtained
without an optimizer or graph premise. One threshold precedes the physical
field and every genuine drift. -/
theorem polynomial_scalar_strict_reference_barrier :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h ≤ δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
        scalarRate (canonical_elementary_polynomial_model h) b < poincareRate (polynomialRankOne h).lgeMu ∧
        scalarRate (canonical_elementary_polynomial_model h) b <
          gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
            (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu) := by
  obtain ⟨δT, hδT, htrial⟩ := polynomial_haar_trial_strict_upper
  obtain ⟨δP, hδP, hPC⟩ := polynomial_reference_poincare_quadratic_lower
  refine ⟨min δT δP, lt_min hδT hδP, fun h hh hδ b => ?_⟩
  obtain ⟨hG, hQ⟩ := htrial h hh (hδ.trans (min_le_left _ _)) b
  have hs : scalarRate (canonical_elementary_polynomial_model h) b <
      ENNReal.ofReal (a0 * (1 + 5 * h ^ 2 / 48)) :=
    (scalarRate_le_quotient _ _ _ hG).trans_lt hQ
  have hreal : a0 * (1 + 5 * h ^ 2 / 48) < a0 * (1 + h ^ 2 / 8) := by
    apply mul_lt_mul_of_pos_left _ a0_pos
    nlinarith [sq_pos_of_pos hh]
  have hup : ENNReal.ofReal (a0 * (1 + 5 * h ^ 2 / 48)) < ENNReal.ofReal (a0 * (1 + h ^ 2 / 8)) :=
    ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hreal,
      mul_pos a0_pos (by positivity : 0 < 1 + h ^ 2 / 8)⟩
  have hp := hPC h (show |h| ≤ δP by rw [abs_of_pos hh]; exact hδ.trans (min_le_right _ _))
  change ENNReal.ofReal (a0 * (1 + h ^ 2 / 8)) ≤ poincareRate (polynomialRankOne h).lgeMu at hp
  have hstrict := (hs.trans hup).trans_le hp
  exact ⟨hstrict, hstrict.trans_le (polynomial_poincareRate_le_gaussianRate h _ _)⟩

/-- For every sufficiently small positive field, the actual canonical scalar
rate is attained by an original absolute H1 density with positive gap. All
analytic bridge hypotheses, including the strict Gaussian barrier, are proved
by their actual producers before the endpoint compactness argument is applied. -/
theorem polynomial_scalar_attainment :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∃ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ ∧
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
          scalarRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨δ, hδ, hbarrier⟩ := polynomial_scalar_strict_reference_barrier
  exact ⟨δ, hδ, fun h hh hsmall b => polynomial_scalar_attainment_of_lt_gaussian h b
    (hbarrier h hh hsmall.le b).2⟩

end DGPS.Examples.PolynomialSpecies
