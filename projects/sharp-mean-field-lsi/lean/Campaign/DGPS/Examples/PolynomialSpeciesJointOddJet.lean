import DGPS.Examples.PolynomialSpeciesHalfTurnGraph
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The actual simultaneous field/amplitude symmetry kills the cubic joint
jet. This rules out an h*R^2 term using the genuine SAME graph, rather than an
assumed parity of a reduced polynomial or a different one-body model. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Every joint first-field/first-amplitude line of the actual reduced value
has zero cubic derivative at the origin. Its only graph hypotheses are the
actual IFT producer's outputs. The independent s and normalized rate are zero
on this line; neither a cubic cancellation nor a remainder is a premise. -/
theorem polynomial_reduced_deficit_joint_third_zero
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (a b h : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => polynomialReducedDeficit ψ
      (t * a, t * b, (t * h, 0), 0)) 0 = 0 := by
  obtain ⟨δ, hδ, heq⟩ := polynomial_reduced_deficit_half_turn
    hU h0U hN h0N hψ hψ0 hψN hgraph
  let p := fun t : ℝ => ((t * a, t * b, (t * h, 0), 0) : PolynomialRangeParameters)
  let F := fun t : ℝ => polynomialReducedDeficit ψ (p t)
  have hp : Continuous p := by dsimp only [p]; fun_prop
  have hp0 : p 0 = 0 := by ext <;> simp [p]
  have ht : Tendsto p (𝓝 0) (𝓝 0) := by
    simpa only [hp0] using (hp.tendsto (0 : ℝ))
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ‖p t‖ < δ := by
    have hs := ht.norm
    simp only [norm_zero] at hs
    exact hs.eventually (gt_mem_nhds hδ)
  have he : (fun t : ℝ => F (-t)) =ᶠ[𝓝 0] F := by
    filter_upwards [hn] with t ht
    have hh := heq (t * a) (t * b) (t * h) 0 0 ht
    simpa only [F, p, neg_mul] using hh
  have hd := he.iteratedDeriv_eq 3
  rw [iteratedDeriv_comp_neg] at hd
  norm_num at hd
  change iteratedDeriv 3 F 0 = 0
  linarith

end DGPS.Examples.PolynomialSpecies
