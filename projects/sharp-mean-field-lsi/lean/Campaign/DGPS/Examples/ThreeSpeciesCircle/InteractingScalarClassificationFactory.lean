import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarClassification

/-! The actual canonical-model scalar classification, with the genuine
ordinary graph supplied internally. This exports no branch, capture,
attainment, regularity or optimizer premise. -/

noncomputable section
open MeasureTheory

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Exactly three smooth positive probability laws minimize the actual global
scalar quotient. One field interval is chosen first; at fixed field one
coupling threshold precedes EVERY drift and EVERY original H1 competitor.
Only the canonical three representatives are claimed pointwise smooth and
positive. Arbitrary original minimizers are classified by their laws. -/
theorem scalarOptimizer_exact_three_rotationBranches :
    ∃ δ : ℝ, 0<δ ∧ ∀ h : ℝ, 0<h → h<δ →
      ∃ ε0 : ℝ, 0<ε0 ∧ ε0≤epsMax h ∧ ∀ ε : ℝ, 0<ε → ε<ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), ∃ ξ : Fin 3 → AbsoluteDensity 1,
          (∀ j, IsSmoothPeriodic (ξ j).sqrt ∧ ∀ x, 0<(ξ j).sqrt x) ∧
          Pairwise (fun i j => densityMeasure (ξ i)≠densityMeasure (ξ j)) ∧
          (∀ j x, (ξ j).density x=(ξ 0).density (x-pt ((j:ℕ)/3))) ∧
          (∀ j, 0<scalarGap (modelData h ε) (ξ j) ∧
            scalarQuotient (modelData h ε) b (ξ j)=scalarRate (modelData h ε) b) ∧
          ∀ ρ : AbsoluteDensity 1,
            (0<scalarGap (modelData h ε) ρ ∧
              scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b) ↔
            ∃ j : Fin 3, densityMeasure ρ=densityMeasure (ξ j) := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨δ,hδ,_,hclassify⟩ := elementaryModel_scalar_exact_three_of_graph D
  exact ⟨δ,hδ,hclassify⟩

end DGPS.Examples.ThreeSpeciesCircle
