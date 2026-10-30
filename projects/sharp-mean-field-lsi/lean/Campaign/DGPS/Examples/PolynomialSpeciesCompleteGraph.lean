import DGPS.Examples.PolynomialSpeciesRangeGraphDerivative
import DGPS.Examples.PolynomialSpeciesRangeEnvelope

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029
namespace DGPS.Examples.PolynomialSpecies

theorem exists_polynomial_range_graph_complete :
    ∃ (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
      (ψ : PolynomialRangeParameters → E_STR02969),
      IsOpen U ∧ (0 : PolynomialRangeParameters) ∈ U ∧ IsOpen N ∧ (0 : E_STR02969) ∈ N ∧
      ContDiffOn ℝ ∞ ψ U ∧ (∀ p ∈ U, ψ p ∈ N) ∧
      (∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) ∧
      (∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
        ψ (0, 0, (h, s), γ) = 0) ∧
      fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0 ∧
      ∀ a b h γ : ℝ, ((a, b, (h, PolynomialEquilibrium.root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
        HasDerivAt (fun τ : ℝ => polynomialChartDeficit h
          (DGPS.Circle.AngularNormalization.a0 * (1 + τ))
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, PolynomialEquilibrium.root_EX054 h), τ) : PeriodicC2_STR02969)))
          (-2 * DGPS.Circle.AngularNormalization.a0 * polynomialChartGap h
            (a • cosC2_STR02915 + b • sinC2_STR02915 +
              (ψ (a, b, (h, PolynomialEquilibrium.root_EX054 h), γ) : PeriodicC2_STR02969))) γ := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, hamp⟩ :=
    exists_polynomial_range_graph_first_amplitude_zero
  refine ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, hamp, ?_⟩
  intro a b h γ hp
  let w := fun τ : ℝ => ψ (a, b, (h, PolynomialEquilibrium.root_EX054 h), τ)
  have hw : DifferentiableAt ℝ w γ :=
    ((hψ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).comp γ (by fun_prop)
  apply polynomialChartDeficit_rate_envelope h a b γ w (deriv w γ) hw.hasDerivAt
  have hR := (hgraph _ hp _ (hψN _ hp)).2 rfl
  change PY_STR02955 (polynomialRangeEuler (h, PolynomialEquilibrium.root_EX054 h)
    (DGPS.Circle.AngularNormalization.a0 * (1 + γ))
    (a • cosC2_STR02915 + b • sinC2_STR02915 + (w γ : PeriodicC2_STR02969))) = 0 at hR
  rw [polynomialRangeEuler_actual] at hR
  exact hR

end DGPS.Examples.PolynomialSpecies
