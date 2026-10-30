import DGPS.Examples.PolynomialSpeciesActualNativeDescent
import DGPS.Examples.PolynomialSpeciesCompleteGraph

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DGPS.Examples.PolynomialSpecies

/-- Unconditional original-domain factory; the actual retained graph is produced internally. -/
theorem polynomial_all_actual_optimizers_poincare_margin :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      poincareRate (densityMeasure ρ) ≤ ENNReal.ofReal
        ((scalarRate (canonical_elementary_polynomial_model h) b).toReal - c * h ^ 2) ∧
      poincareRate (densityMeasure ρ) < scalarRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, hamp, henv⟩ :=
    exists_polynomial_range_graph_complete
  exact polynomial_scalarMinimizer_actual_poincare_margin hU h0U hN h0N hψ hψN hgraph hzero hamp henv

/-- Unconditional original-domain factory; the actual retained graph is produced internally. -/
theorem polynomial_all_actual_optimizers_every_native_eigenfunction_descent :
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
            speciesQuotient (canonical_elementary_polynomial_model h) b F < scalarRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, hamp, henv⟩ :=
    exists_polynomial_range_graph_complete
  exact polynomial_scalarMinimizer_every_native_eigenfunction_descent hU h0U hN h0N hψ hψN hgraph hzero hamp henv

end DGPS.Examples.PolynomialSpecies
