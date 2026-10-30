import DGPS.Examples.PolynomialSpeciesReflectionEuler

/-! SAME-field reflection of ONE genuine implicit graph. Its uniqueness
neighborhood need not be symmetric: norm isometry and continuity put the
reflected correction into that original neighborhood on a smaller common ball. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

def polynomialReflectionParameters (p : PolynomialRangeParameters) : PolynomialRangeParameters :=
  (p.1, -p.2.1, p.2.2.1, p.2.2.2)

private theorem parameters_smooth : ContDiff ℝ ∞ polynomialReflectionParameters := by
  unfold polynomialReflectionParameters
  fun_prop

private theorem parameters_zero : polynomialReflectionParameters 0 = 0 := by
  ext <;> simp [polynomialReflectionParameters]

theorem polynomial_range_graph_reflection {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b h s γ : ℝ,
      ‖((a, b, (h, s), γ) : PolynomialRangeParameters)‖ < δ →
      ψ (a, -b, (h, s), γ) = pullE_STR02916 (-1) (Or.inr rfl) 0 (ψ (a, b, (h, s), γ)) := by
  obtain ⟨r, hr, hballN⟩ := Metric.mem_nhds_iff.1 (hN.mem_nhds h0N)
  have hc : ContinuousAt ψ (0 : PolynomialRangeParameters) :=
    (hψ.contDiffAt (hU.mem_nhds h0U)).continuousAt
  have hsmall : ∀ᶠ p : PolynomialRangeParameters in 𝓝 0, ‖ψ p‖ < r := by
    have ht : Tendsto (fun p => ‖ψ p‖) (𝓝 (0 : PolynomialRangeParameters)) (𝓝 (0 : ℝ)) := by
      simpa only [hψ0, norm_zero] using hc.tendsto.norm
    exact ht.eventually (gt_mem_nhds hr)
  have htrans : ∀ᶠ p : PolynomialRangeParameters in 𝓝 0, polynomialReflectionParameters p ∈ U := by
    have ht := parameters_smooth.continuous.tendsto (0 : PolynomialRangeParameters)
    rw [parameters_zero] at ht
    exact ht.eventually (hU.mem_nhds h0U)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1
    (inter_mem (hU.mem_nhds h0U) (inter_mem htrans hsmall))
  refine ⟨δ, hδ, fun a b h s γ hp => ?_⟩
  let p : PolynomialRangeParameters := (a, b, (h, s), γ)
  have hm : p ∈ Metric.ball (0 : PolynomialRangeParameters) δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hp
  obtain ⟨hpU, htpU, hpn⟩ := hball hm
  have htN : pullE_STR02916 (-1) (Or.inr rfl) 0 (ψ p) ∈ N := by
    apply hballN
    rw [Metric.mem_ball, dist_zero_right, norm_pullE_STR02916]
    exact hpn
  have hz : polynomialRangeMap (p, ψ p) = 0 := (hgraph p hpU _ (hψN p hpU)).2 rfl
  have htzero := polynomialRangeMap_reflection_zero a b h s γ (ψ p) hz
  exact (hgraph (polynomialReflectionParameters p) htpU _ htN).1 htzero

/-- The SAME-graph chart has the literal spatial pullback relation. Field,
independent reference tilt and normalized rate are fixed. -/
theorem polynomial_range_graph_profile_reflection
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b h s γ : ℝ,
      ‖((a, b, (h, s), γ) : PolynomialRangeParameters)‖ < δ → ∀ t : ℝ,
      (a • cosC2_STR02915 + (-b) • sinC2_STR02915 +
          (ψ (a, -b, (h, s), γ) : PeriodicC2_STR02969)).val (-t) =
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, s), γ) : PeriodicC2_STR02969)).val t := by
  obtain ⟨δ, hδ, heq⟩ := polynomial_range_graph_reflection hU h0U hN h0N hψ hψ0 hψN hgraph
  refine ⟨δ, hδ, fun a b h s γ hp t => ?_⟩
  rw [heq a b h s γ hp]
  change a * Real.cos (-t) + (-b) * Real.sin (-t) +
    (pullE_STR02916 (-1) (Or.inr rfl) 0 (ψ (a, b, (h, s), γ)) : PeriodicC2_STR02969).val (-t) = _
  rw [pullE_val_STR02916, Real.cos_neg, Real.sin_neg]
  simp only [neg_one_mul, neg_neg, add_zero]
  change _ = a * Real.cos t + b * Real.sin t + (ψ (a, b, (h, s), γ) : PeriodicC2_STR02969).val t
  ring

/-- Exact value, gap and normalized-law reflection on the SAME graph. These
are fixed-field identities, with no critical-point or optimizer premise. -/
theorem polynomial_range_graph_reflection_values
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b h s γ : ℝ,
      ‖((a, b, (h, s), γ) : PolynomialRangeParameters)‖ < δ →
      let u := a • cosC2_STR02915 + b • sinC2_STR02915 +
        (ψ (a, b, (h, s), γ) : PeriodicC2_STR02969)
      let v := a • cosC2_STR02915 + (-b) • sinC2_STR02915 +
        (ψ (a, -b, (h, s), γ) : PeriodicC2_STR02969)
      polynomialRangeDeficit (h, s) (DGPS.Circle.AngularNormalization.a0 * (1 + γ)) v =
          polynomialRangeDeficit (h, s) (DGPS.Circle.AngularNormalization.a0 * (1 + γ)) u ∧
        polynomialRangeGap (h, s) v = polynomialRangeGap (h, s) u ∧
        ∀ t : ℝ, (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) v).val (-t) =
          (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, s))) u).val t := by
  obtain ⟨δ, hδ, heq⟩ := polynomial_range_graph_profile_reflection hU h0U hN h0N hψ hψ0 hψN hgraph
  refine ⟨δ, hδ, fun a b h s γ hp => ?_⟩
  let u := a • cosC2_STR02915 + b • sinC2_STR02915 +
    (ψ (a, b, (h, s), γ) : PeriodicC2_STR02969)
  let v := a • cosC2_STR02915 + (-b) • sinC2_STR02915 +
    (ψ (a, -b, (h, s), γ) : PeriodicC2_STR02969)
  have hu : ∀ t : ℝ, v.val (-t) = u.val t := heq a b h s γ hp
  refine ⟨polynomialRangeDeficit_reflection h s _ u v hu, ?_,
    polynomialRangeDensity_reflection h s u v hu⟩
  obtain ⟨hH, _, hm, _, _⟩ := polynomialRange_moments_reflection h s u v hu
  unfold polynomialRangeGap
  dsimp only
  rw [hH, hm]

end DGPS.Examples.PolynomialSpecies
