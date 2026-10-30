import DGPS.Examples.PolynomialSpeciesStrictRateChain
import DGPS.Examples.PolynomialSpeciesExactlyTwoOptimizers
import DGPS.Examples.PolynomialSpeciesNativeDescentFactory

/-! Candidate complete T11 exports. Native H1 tests are universally quantified;
all splits have equal weights and exact barycenter PROBABILITY law. The latter
is the source probability statement, not literal equality of arbitrary stored
square-root representatives (which can differ on Haar-null sets). -/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Examples.PolynomialExactGap
namespace DGPS.Examples.PolynomialSpecies

theorem every_small_nonzero_split_improves :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∀ f : WeakH1Test (densityMeasure ρ),
      (∫ x, f.fn x ∂(densityMeasure ρ : Measure (Torus 1))) = 0 →
      (∫ x, f.fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) = 1 →
      (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) =
        (poincareRate (densityMeasure ρ)).toReal →
    ∃ (g : Torus 1 → ℝ) (hc : Continuous g) (hg : IsWeakGradient g f.grad)
        (hm : ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) = 0),
      g =ᵐ[haar 1] f.fn ∧ g =ᵐ[(densityMeasure ρ : Measure (Torus 1))] f.fn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
        ∃ hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x,
          let F := nativeH1BinarySplit ρ g f.grad hg hc hm t hp
          (∀ s : Fin F.count, PositiveH1Density (F.density s)) ∧
          densityMeasure (barycenter F) = densityMeasure ρ ∧
          (speciesGap (canonical_elementary_polynomial_model h) F : ℝ) = (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) +
            (1 / 2 : ℝ) * ((∫ x, InformationTheory.klFun (1 + t * g x)
              ∂(densityMeasure ρ : Measure (Torus 1))) +
              ∫ x, InformationTheory.klFun (1 + t * (-g x))
                ∂(densityMeasure ρ : Measure (Torus 1))) ∧
          0 < speciesGap (canonical_elementary_polynomial_model h) F ∧ speciesDissipation (canonical_elementary_polynomial_model h) b F ≠ ⊤ ∧
            speciesQuotient (canonical_elementary_polynomial_model h) b F < scalarRate (canonical_elementary_polynomial_model h) b :=
  polynomial_all_actual_optimizers_every_native_eigenfunction_descent

/-- Complete fixed-model source result, on one common small-field interval:
finite strict rates at the exact moving equilibrium, exactly two smooth positive
optimizer laws exchanged by reflection, and two-sided improvement for every
normalized first native H1 Poincare eigenfunction of every actual optimizer. -/
theorem actual_species_descent :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      (let rStar := scalarRate (canonical_elementary_polynomial_model h) b
      let rMs := speciesRate (canonical_elementary_polynomial_model h) b
      let lamG := gaussianRate (canonical_elementary_polynomial_model h) (polynomialRankOne h).lgeMu
        (densityHessian_coercive_EX055 h (polynomialRankOne h).lgeMu)
      let lamTwo := min lamG (poincareRate (polynomialRankOne h).lgeMu)
      (∀ r ∈ [rStar, rMs, lamG, lamTwo], FiniteRate r) ∧
        0 < rMs ∧ rMs < rStar ∧ rStar < lamTwo ∧ lamTwo ≤ lamG) ∧
      (∃ ρplus ρminus : AbsoluteDensity 1,
        SmoothPositiveDensity ρplus ∧ SmoothPositiveDensity ρminus ∧
        IsScalarOptimizer (canonical_elementary_polynomial_model h) b ρplus ∧
        IsScalarOptimizer (canonical_elementary_polynomial_model h) b ρminus ∧
        densityMeasure ρplus ≠ densityMeasure ρminus ∧
        (densityMeasure ρminus : Measure (Torus 1)) =
          Measure.map (fun x : Torus 1 => -x) (densityMeasure ρplus) ∧
        ∀ ρ : AbsoluteDensity 1,
          IsScalarOptimizer (canonical_elementary_polynomial_model h) b ρ ↔
          densityMeasure ρ = densityMeasure ρplus ∨ densityMeasure ρ = densityMeasure ρminus) ∧
      (∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∀ f : WeakH1Test (densityMeasure ρ),
      (∫ x, f.fn x ∂(densityMeasure ρ : Measure (Torus 1))) = 0 →
      (∫ x, f.fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) = 1 →
      (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) =
        (poincareRate (densityMeasure ρ)).toReal →
    ∃ (g : Torus 1 → ℝ) (hc : Continuous g) (hg : IsWeakGradient g f.grad)
        (hm : ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) = 0),
      g =ᵐ[haar 1] f.fn ∧ g =ᵐ[(densityMeasure ρ : Measure (Torus 1))] f.fn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
        ∃ hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x,
          let F := nativeH1BinarySplit ρ g f.grad hg hc hm t hp
          (∀ s : Fin F.count, PositiveH1Density (F.density s)) ∧
          densityMeasure (barycenter F) = densityMeasure ρ ∧
          (speciesGap (canonical_elementary_polynomial_model h) F : ℝ) = (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) +
            (1 / 2 : ℝ) * ((∫ x, InformationTheory.klFun (1 + t * g x)
              ∂(densityMeasure ρ : Measure (Torus 1))) +
              ∫ x, InformationTheory.klFun (1 + t * (-g x))
                ∂(densityMeasure ρ : Measure (Torus 1))) ∧
          0 < speciesGap (canonical_elementary_polynomial_model h) F ∧ speciesDissipation (canonical_elementary_polynomial_model h) b F ≠ ⊤ ∧
            speciesQuotient (canonical_elementary_polynomial_model h) b F < scalarRate (canonical_elementary_polynomial_model h) b) := by
  obtain ⟨δR, hδR, hrate⟩ := strict_rate_chain
  obtain ⟨δO, hδO, hopt⟩ := exactly_two_scalar_optimizers
  obtain ⟨δD, hδD, hdescent⟩ := every_small_nonzero_split_improves
  refine ⟨min δR (min δO δD), lt_min hδR (lt_min hδO hδD), ?_⟩
  intro h hh hsmall b
  exact ⟨hrate h hh (hsmall.trans_le (min_le_left _ _)) b,
    hopt h hh (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) b,
    hdescent h hh (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) b⟩

end DGPS.Examples.PolynomialSpecies
