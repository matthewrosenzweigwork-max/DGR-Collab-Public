import DGPS.Examples.PolynomialSpeciesExactlyTwoCharts
import DGPS.Examples.PolynomialSpeciesCompleteGraph
import DGPS.Examples.PolynomialSpeciesOptimizerSmooth
import DGPS.Examples.PolynomialSpeciesReflectionPushforward

/-! Candidate frozen T11 optimizer-classification export.
The interacting graph and all analytic hypotheses are produced internally.
No optimizer classification, compactness, origin exclusion, implicit branch,
smoothness or reflection-preservation premise appears in the public theorem. -/
noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- Exactly two positive smooth positive-gap global scalar optimizer laws for
the fixed physical polynomial model, exchanged by spatial reflection. The
drift is arbitrary genuine model drift, hence this includes the canonical one. -/
theorem exactly_two_scalar_optimizers :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∃ ρplus ρminus : AbsoluteDensity 1,
        SmoothPositiveDensity ρplus ∧ SmoothPositiveDensity ρminus ∧
        IsScalarOptimizer (canonical_elementary_polynomial_model h) b ρplus ∧
        IsScalarOptimizer (canonical_elementary_polynomial_model h) b ρminus ∧
        densityMeasure ρplus ≠ densityMeasure ρminus ∧
        (densityMeasure ρminus : Measure (Torus 1)) =
          Measure.map (fun x : Torus 1 => -x) (densityMeasure ρplus) ∧
        ∀ ρ : AbsoluteDensity 1,
          IsScalarOptimizer (canonical_elementary_polynomial_model h) b ρ ↔
          densityMeasure ρ = densityMeasure ρplus ∨ densityMeasure ρ = densityMeasure ρminus := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, hamp, henv⟩ :=
    exists_polynomial_range_graph_complete
  obtain ⟨δC, hδC, hcharts⟩ := polynomial_exactly_two_scalar_optimizer_charts
    hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  obtain ⟨δS, hδS, hsmooth⟩ := polynomial_scalarMinimizer_smoothPositiveDensity
  refine ⟨min δC δS, lt_min hδC hδS, ?_⟩
  intro h hh hsmall b
  obtain ⟨u, v, huv, hne, huopt, hvopt, hclass⟩ :=
    hcharts h hh (hsmall.trans_le (min_le_left _ _)) b
  have hhS : h < δS := hsmall.trans_le (min_le_right _ _)
  exact ⟨polynomialChartAbsolute h u, polynomialChartAbsolute h v,
    hsmooth h hh hhS b _ huopt.1 huopt.2,
    hsmooth h hh hhS b _ hvopt.1 hvopt.2,
    huopt, hvopt, hne, polynomial_reflected_chart_pushforward h u v huv, hclass⟩

end DGPS.Examples.PolynomialSpecies
