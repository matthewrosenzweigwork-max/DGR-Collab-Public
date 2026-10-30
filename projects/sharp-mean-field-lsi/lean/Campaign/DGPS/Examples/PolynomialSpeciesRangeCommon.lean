import DGPS.Examples.PolynomialSpeciesRangeControl
import DGPS.Examples.PolynomialSpeciesRangeEnvelope
import DGPS.Examples.PolynomialSpeciesRangeGraphDerivative

/-! One actual interacting graph carries the amplitude bound, amplitude jet,
selected-root entry and actual rate envelope. Independent existential graph
witnesses are never identified without proof. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- The concrete common-witness range data needed before a reduced Taylor estimate.
Every derivative and envelope assertion concerns the same actual correction function. -/
theorem exists_polynomial_common_range_graph :
    ∃ (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
      (ψ : PolynomialRangeParameters → E_STR02969) (δ K : ℝ),
      IsOpen U ∧ (0 : PolynomialRangeParameters) ∈ U ∧
      IsOpen N ∧ (0 : E_STR02969) ∈ N ∧ ContDiffOn ℝ ∞ ψ U ∧
      (∀ p ∈ U, ψ p ∈ N) ∧
      (∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) ∧
      (∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
        ψ (0, 0, (h, s), γ) = 0) ∧
      fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0 ∧
      0 < δ ∧ 0 ≤ K ∧ Metric.ball (0 : PolynomialRangeParameters) δ ⊆ U ∧
      (∀ a b h s γ : ℝ, ‖((a, b, (h, s), γ) : PolynomialRangeParameters)‖ < δ →
        ‖ψ (a, b, (h, s), γ)‖ ≤ K * max |a| |b|) ∧
      (∀ᶠ x : ℝ × ℝ × ℝ × ℝ in 𝓝 0,
        ((x.1, x.2.1, (x.2.2.1, root_EX054 x.2.2.1), x.2.2.2) : PolynomialRangeParameters) ∈ U) ∧
      ∀ a b h γ : ℝ, ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
        HasDerivAt (fun τ : ℝ => polynomialChartDeficit h
          (DGPS.Circle.AngularNormalization.a0 * (1 + τ))
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
          (-2 * DGPS.Circle.AngularNormalization.a0 * polynomialChartGap h
            (a • cosC2_STR02915 + b • sinC2_STR02915 +
              (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ := by
  obtain ⟨U, N, ψ, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, hamp⟩ :=
    exists_polynomial_range_graph_first_amplitude_zero
  have hc : ContDiffAt ℝ 1 ψ (0 : PolynomialRangeParameters) :=
    (hψ.contDiffAt (hU.mem_nhds h0U)).of_le (by simp)
  obtain ⟨K, t, ht, hLip⟩ := hc.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (hU.mem_nhds h0U))
  have hballU : Metric.ball (0 : PolynomialRangeParameters) δ ⊆ U := fun p hp => (hball hp).2
  refine ⟨U, N, ψ, δ, K, hU, h0U, hN, h0N, hψ, hψN, hgraph, hzero, hamp,
    hδ, K.coe_nonneg, hballU, ?_, ?_, ?_⟩
  · intro a b h s γ hp
    let p : PolynomialRangeParameters := (a, b, (h, s), γ)
    let p0 : PolynomialRangeParameters := (0, 0, (h, s), γ)
    have hpp : p ∈ Metric.ball (0 : PolynomialRangeParameters) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hp
    have hnorm : ‖p0‖ ≤ ‖p‖ := by
      dsimp only [p0, p]
      simp only [Prod.norm_def, norm_zero]
      have ht : (0 : ℝ) ≤ max (max ‖h‖ ‖s‖) ‖γ‖ := by positivity
      rw [max_eq_right ht, max_eq_right ht]
      exact le_max_of_le_right (le_max_right _ _)
    have hp0 : p0 ∈ Metric.ball (0 : PolynomialRangeParameters) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hnorm.trans_lt hp
    have hz : ψ p0 = 0 := hzero h s γ (hballU hp0)
    have hd := hLip.dist_le_mul p (hball hpp).1 p0 (hball hp0).1
    rw [hz, dist_zero_right] at hd
    have hdist : dist p p0 = max |a| |b| := by
      simp only [p, p0, Prod.dist_eq, dist_self, dist_zero_right, Real.norm_eq_abs,
        max_eq_left (abs_nonneg b)]
    rw [hdist] at hd
    exact hd
  · exact polynomial_selected_parameters_tendsto.eventually (hU.mem_nhds h0U)
  · intro a b h γ hp
    let w := fun τ : ℝ => ψ (a, b, (h, root_EX054 h), τ)
    have hw : DifferentiableAt ℝ w γ :=
      ((hψ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).comp γ (by fun_prop)
    apply polynomialChartDeficit_rate_envelope h a b γ w (deriv w γ) hw.hasDerivAt
    have hR := (hgraph _ hp _ (hψN _ hp)).2 rfl
    change PY_STR02955 (polynomialRangeEuler (h, root_EX054 h)
      (DGPS.Circle.AngularNormalization.a0 * (1 + γ))
      (a • cosC2_STR02915 + b • sinC2_STR02915 + (w γ : PeriodicC2_STR02969))) = 0 at hR
    rw [polynomialRangeEuler_actual] at hR
    exact hR

end DGPS.Examples.PolynomialSpecies
