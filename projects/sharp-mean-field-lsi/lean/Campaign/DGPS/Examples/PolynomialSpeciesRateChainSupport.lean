import DGPS.Examples.PolynomialScalarAttainmentFactory
import DGPS.Examples.PolynomialSpeciesPositiveRate
import DGPS.Structural.AmplitudePoincare
import DGPS.Structural.AmplitudeComparison
import DGPS.Variational.SpeciesInclusion
import DGPS.Foundations.RateArithmetic

noncomputable section
open MeasureTheory
open scoped ENNReal
open DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialExactGap
namespace DGPS.Examples.PolynomialSpecies

/-- The true moving reference has finite native Poincare rate, by the
original-domain sine Rayleigh comparison and its actual positive density bounds. -/
theorem polynomial_reference_poincare_finite (h : ℝ) :
    poincareRate (polynomialRankOne h).lgeMu ≠ ⊤ := by
  let P := (polynomialRankOne h).ref
  have hupper : 0 < P.upper := by
    obtain ⟨x, hxlow, hxup⟩ := (P.lower_le.and P.le_upper).exists
    exact P.lower_pos.trans_le (hxlow.trans hxup)
  have hratio : P.upper ≤ Real.exp (Real.log (P.upper / P.lower)) * P.lower := by
    rw [Real.exp_log (div_pos hupper P.lower_pos), div_mul_cancel₀ _ P.lower_pos.ne']
  have hu := DGPS.Structural.poincareRate_le_haarRate_densityRatio (by norm_num : 0 < (1 : ℕ))
    P (Real.log (P.upper / P.lower)) P.lower P.upper P.lower_pos P.lower_le P.le_upper hratio
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu

/-- The native Gaussian rate is finite at the exact moving equilibrium, for
its proved coercive centered density Hessian. -/
theorem polynomial_reference_gaussian_finite (h : ℝ) :
    gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
      (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu) ≠ ⊤ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (polynomial_reference_poincare_finite h))
    (DGPS.Structural.gaussianRate_le_hessianUpper_poincare
      (polynomialRankOne h).lgeMu (canonical_elementary_polynomial_model h)
      (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu))

/-- All parts of the frozen rate chain other than strict species descent.
No asymptotic or spectral-expansion premise is supplied. -/
theorem polynomial_rate_chain_without_descent :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      let rStar := scalarRate (canonical_elementary_polynomial_model h) b
      let rMs := speciesRate (canonical_elementary_polynomial_model h) b
      let lamG := gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
        (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu)
      let lamTwo := min lamG (poincareRate (polynomialRankOne h).lgeMu)
      (∀ r ∈ [rStar, rMs, lamG, lamTwo], FiniteRate r) ∧
        0 < rMs ∧ rMs ≤ rStar ∧ rStar < lamTwo ∧ lamTwo ≤ lamG := by
  obtain ⟨δB, hδB, hbarrier⟩ := polynomial_scalar_strict_reference_barrier
  obtain ⟨δP, hδP, hpositive⟩ := polynomial_actual_speciesRate_positive
  refine ⟨min δB δP, lt_min hδB hδP, ?_⟩
  intro h hh hsmall b
  have hb := hbarrier h hh (hsmall.le.trans (min_le_left _ _)) b
  have hp := hpositive h (by rw [abs_of_pos hh]; exact hsmall.le.trans (min_le_right _ _)) b
  have hmspos : 0 < speciesRate (canonical_elementary_polynomial_model h) b :=
    (ENNReal.ofReal_pos.2 (half_pos a0_pos)).trans_le hp
  have hinc := speciesRate_le_scalarRate (canonical_elementary_polynomial_model h) b
  have hGfin := polynomial_reference_gaussian_finite h
  have hPfin := polynomial_reference_poincare_finite h
  have hSfin : scalarRate (canonical_elementary_polynomial_model h) b ≠ ⊤ :=
    ne_top_of_le_ne_top hGfin hb.2.le
  have hMfin : speciesRate (canonical_elementary_polynomial_model h) b ≠ ⊤ :=
    ne_top_of_le_ne_top hSfin hinc
  have hTfin : min
      (gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
        (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu))
      (poincareRate (polynomialRankOne h).lgeMu) ≠ ⊤ :=
    ne_top_of_le_ne_top hGfin (min_le_left _ _)
  refine ⟨?_, hmspos, hinc, lt_min hb.2 hb.1, min_le_left _ _⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hSfin
  · exact hMfin
  · exact hGfin
  · exact hTfin

end DGPS.Examples.PolynomialSpecies
