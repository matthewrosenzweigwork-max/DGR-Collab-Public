import DGPS.Examples.PolynomialSpeciesRateChainSupport
import DGPS.Examples.PolynomialSpeciesStrictDescent

noncomputable section
open MeasureTheory
open scoped ENNReal
open DGPS.Circle.AngularNormalization
open DGPS.Examples.PolynomialExactGap
namespace DGPS.Examples.PolynomialSpecies

/-- Full actual fixed-model strict rate chain, with every rate finite and the true moving equilibrium Hessian. -/
theorem strict_rate_chain :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      let rStar := scalarRate (canonical_elementary_polynomial_model h) b
      let rMs := speciesRate (canonical_elementary_polynomial_model h) b
      let lamG := gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
        (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu)
      let lamTwo := min lamG (poincareRate (polynomialRankOne h).lgeMu)
      (∀ r ∈ [rStar, rMs, lamG, lamTwo], FiniteRate r) ∧
        0 < rMs ∧ rMs < rStar ∧ rStar < lamTwo ∧ lamTwo ≤ lamG := by
  obtain ⟨δB, hδB, hbase⟩ := polynomial_rate_chain_without_descent
  obtain ⟨δD, hδD, hdescent⟩ := polynomial_actual_speciesRate_lt_scalarRate
  refine ⟨min δB δD, lt_min hδB hδD, ?_⟩
  intro h hh hsmall b
  obtain ⟨hfinite, hpositive, _hinclusion, hbarrier, hlast⟩ :=
    hbase h hh (hsmall.trans_le (min_le_left _ _)) b
  exact ⟨hfinite, hpositive, hdescent h hh (hsmall.trans_le (min_le_right _ _)) b,
    hbarrier, hlast⟩

end DGPS.Examples.PolynomialSpecies
