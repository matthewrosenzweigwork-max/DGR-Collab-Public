import Mathlib

/-!
# Second-order Taylor bound (Phase 1 infrastructure)

`taylor2`: if `f'' ≤ K` on the segment between `x₀` and `x`, then
`f x - f x₀ - f' x₀ (x - x₀) ≤ K/2 (x - x₀)²`. (Also inlined in the proof of R34, Lemma B.1 (ii).)
-/

namespace SharpLSI

/-- Second-order Taylor upper bound from an upper bound on the second derivative. -/
theorem taylor2 {f f' f'' : ℝ → ℝ} {x₀ x K : ℝ}
    (hf : ∀ y ∈ Set.uIcc x₀ x, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.uIcc x₀ x, HasDerivAt f' (f'' y) y)
    (hK : ∀ y ∈ Set.uIcc x₀ x, f'' y ≤ K) :
    f x - f x₀ - f' x₀ * (x - x₀) ≤ K / 2 * (x - x₀) ^ 2 := by
  set g : ℝ → ℝ := fun y => f y - f' x₀ * (y - x₀) - K / 2 * (y - x₀) ^ 2 with hg
  set g' : ℝ → ℝ := fun y => f' y - f' x₀ - K * (y - x₀) with hg'
  have hgd : ∀ y ∈ Set.uIcc x₀ x, HasDerivAt g (g' y) y := by
    intro y hy
    have h1 : HasDerivAt (fun y => f' x₀ * (y - x₀)) (f' x₀) y := by
      simpa using ((hasDerivAt_id' y).sub_const x₀).const_mul (f' x₀)
    have h2 : HasDerivAt (fun y => K / 2 * (y - x₀) ^ 2) (K * (y - x₀)) y := by
      have := (((hasDerivAt_id' y).sub_const x₀).pow 2).const_mul (K / 2)
      convert this using 1; push_cast; ring
    exact ((hf y hy).sub h1).sub h2
  have hg'd : ∀ y ∈ Set.uIcc x₀ x, HasDerivAt g' (f'' y - K) y := by
    intro y hy
    have h1 : HasDerivAt (fun y => K * (y - x₀)) K y := by
      simpa using ((hasDerivAt_id' y).sub_const x₀).const_mul K
    exact ((hf' y hy).sub_const (f' x₀)).sub h1
  have key : g x ≤ g x₀ := by
    rcases le_total x₀ x with h | h
    · have hI : Set.uIcc x₀ x = Set.Icc x₀ x := Set.uIcc_of_le h
      rw [hI] at hgd hg'd hK
      have hanti : AntitoneOn g' (Set.Icc x₀ x) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · exact fun y hy => (hg'd y hy).continuousAt.continuousWithinAt
        · intro y hy; exact (hg'd y (interior_subset hy)).differentiableAt.differentiableWithinAt
        · intro y hy; rw [(hg'd y (interior_subset hy)).deriv]; linarith [hK y (interior_subset hy)]
      have hanti2 : AntitoneOn g (Set.Icc x₀ x) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · exact fun y hy => (hgd y hy).continuousAt.continuousWithinAt
        · intro y hy; exact (hgd y (interior_subset hy)).differentiableAt.differentiableWithinAt
        · intro y hy
          have hy' := interior_subset hy
          rw [(hgd y hy').deriv]
          have := hanti ⟨le_refl x₀, h⟩ hy' hy'.1
          simpa [hg'] using this
      exact hanti2 ⟨le_refl x₀, h⟩ ⟨h, le_refl x⟩ h
    · have hI : Set.uIcc x₀ x = Set.Icc x x₀ := Set.uIcc_of_ge h
      rw [hI] at hgd hg'd hK
      have hanti : AntitoneOn g' (Set.Icc x x₀) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · exact fun y hy => (hg'd y hy).continuousAt.continuousWithinAt
        · intro y hy; exact (hg'd y (interior_subset hy)).differentiableAt.differentiableWithinAt
        · intro y hy; rw [(hg'd y (interior_subset hy)).deriv]; linarith [hK y (interior_subset hy)]
      have hmono : MonotoneOn g (Set.Icc x x₀) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        · exact fun y hy => (hgd y hy).continuousAt.continuousWithinAt
        · intro y hy; exact (hgd y (interior_subset hy)).differentiableAt.differentiableWithinAt
        · intro y hy
          have hy' := interior_subset hy
          rw [(hgd y hy').deriv]
          have := hanti hy' ⟨h, le_refl x₀⟩ hy'.2
          simpa [hg'] using this
      exact hmono ⟨le_refl x, h⟩ ⟨h, le_refl x₀⟩ h
  simp only [hg] at key
  linarith

end SharpLSI
