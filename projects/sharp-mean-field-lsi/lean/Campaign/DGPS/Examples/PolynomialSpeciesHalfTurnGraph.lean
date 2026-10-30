import DGPS.Examples.PolynomialSpeciesHalfTurnEuler

/-! Actual local half-turn equivariance of ONE interacting range graph. The
transformed correction is put in the original uniqueness neighborhood by its
proved norm isometry and continuity at zero; no symmetric IFT domain is assumed. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Field reversal paired with first-amplitude reversal; s and rate stay fixed. -/
def polynomialHalfTurnParameters (p : PolynomialRangeParameters) : PolynomialRangeParameters :=
  (-p.1, -p.2.1, (-p.2.2.1.1, p.2.2.1.2), p.2.2.2)

private theorem parameters_smooth : ContDiff ℝ ∞ polynomialHalfTurnParameters := by
  unfold polynomialHalfTurnParameters
  fun_prop

private theorem parameters_zero : polynomialHalfTurnParameters 0 = 0 := by ext <;> simp [polynomialHalfTurnParameters]

/-- The actual independent reduced value, with the full nonlocal moments retained. -/
def polynomialReducedDeficit (ψ : PolynomialRangeParameters → E_STR02969)
    (p : PolynomialRangeParameters) : ℝ :=
  polynomialRangeDeficit p.2.2.1 (DGPS.Circle.AngularNormalization.a0 * (1 + p.2.2.2))
    (p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915 + (ψ p : PeriodicC2_STR02969))

/-- Actual graph equivariance follows from the actual transformed range equation
and uniqueness of the SAME graph. The radius precedes every small parameter. -/
theorem polynomial_range_graph_half_turn {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b h s γ : ℝ,
      ‖((a, b, (h, s), γ) : PolynomialRangeParameters)‖ < δ →
      ψ (-a, -b, (-h, s), γ) = pullE_STR02916 1 (Or.inl rfl) (-Real.pi) (ψ (a, b, (h, s), γ)) := by
  obtain ⟨r, hr, hballN⟩ := Metric.mem_nhds_iff.1 (hN.mem_nhds h0N)
  have hc : ContinuousAt ψ (0 : PolynomialRangeParameters) :=
    (hψ.contDiffAt (hU.mem_nhds h0U)).continuousAt
  have hsmall : ∀ᶠ p : PolynomialRangeParameters in 𝓝 0, ‖ψ p‖ < r := by
    have ht : Tendsto (fun p => ‖ψ p‖) (𝓝 (0 : PolynomialRangeParameters)) (𝓝 (0 : ℝ)) := by
      simpa only [hψ0, norm_zero] using hc.tendsto.norm
    exact ht.eventually (gt_mem_nhds hr)
  have htrans : ∀ᶠ p : PolynomialRangeParameters in 𝓝 0, polynomialHalfTurnParameters p ∈ U := by
    have ht := parameters_smooth.continuous.tendsto (0 : PolynomialRangeParameters)
    rw [parameters_zero] at ht
    exact ht.eventually (hU.mem_nhds h0U)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (hU.mem_nhds h0U) (inter_mem htrans hsmall))
  refine ⟨δ, hδ, ?_⟩
  intro a b h s γ hp
  let p : PolynomialRangeParameters := (a, b, (h, s), γ)
  have hm : p ∈ Metric.ball (0 : PolynomialRangeParameters) δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hp
  obtain ⟨hpU, htpU, hpn⟩ := hball hm
  have htN : pullE_STR02916 1 (Or.inl rfl) (-Real.pi) (ψ p) ∈ N := by
    apply hballN
    rw [Metric.mem_ball, dist_zero_right, norm_pullE_STR02916]
    exact hpn
  have hz : polynomialRangeMap (p, ψ p) = 0 := (hgraph p hpU _ (hψN p hpU)).2 rfl
  have htzero := polynomialRangeMap_half_turn_zero a b h s γ (ψ p) hz
  exact (hgraph (polynomialHalfTurnParameters p) htpU _ htN).1 htzero

/-- The actual reduced value is even under simultaneous reversal of a,b,h on
one common neighborhood. No reduced parity or Taylor coefficient is a premise. -/
theorem polynomial_reduced_deficit_half_turn {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b h s γ : ℝ,
      ‖((a, b, (h, s), γ) : PolynomialRangeParameters)‖ < δ →
      polynomialReducedDeficit ψ (-a, -b, (-h, s), γ) = polynomialReducedDeficit ψ (a, b, (h, s), γ) := by
  obtain ⟨δ, hδ, heq⟩ := polynomial_range_graph_half_turn hU h0U hN h0N hψ hψ0 hψN hgraph
  refine ⟨δ, hδ, ?_⟩
  intro a b h s γ hp
  have hψeq := heq a b h s γ hp
  let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (ψ (a, b, (h, s), γ) : PeriodicC2_STR02969)
  let v := (-a) • cosC2_STR02915 + (-b) • sinC2_STR02915 +
    (ψ (-a, -b, (-h, s), γ) : PeriodicC2_STR02969)
  have hu (t : ℝ) : v.val (t + Real.pi) = u.val t := by
    change (-a) * Real.cos (t + Real.pi) + (-b) * Real.sin (t + Real.pi) +
      (ψ (-a, -b, (-h, s), γ) : PeriodicC2_STR02969).val (t + Real.pi) =
        a * Real.cos t + b * Real.sin t + (ψ (a, b, (h, s), γ) : PeriodicC2_STR02969).val t
    rw [hψeq, pullE_val_STR02916, Real.cos_add_pi, Real.sin_add_pi]
    simp only [one_mul, add_neg_cancel_right]
    ring
  exact polynomialRangeDeficit_half_turn h s
    (DGPS.Circle.AngularNormalization.a0 * (1 + γ)) u v hu

end DGPS.Examples.PolynomialSpecies
