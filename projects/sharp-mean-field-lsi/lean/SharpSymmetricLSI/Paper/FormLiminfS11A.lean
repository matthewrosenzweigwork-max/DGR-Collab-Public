import Mathlib

/-!
# A three-ε lemma for families of approximations

`tendsto_of_approx_family`: if `x = u_R + w_R` for every `R`, `u_R → α_R`, `|w_R| ≤ ε_R` eventually,
`ε_R → 0` and `α_R → α`, then `x → α`.
-/

open Filter Topology

namespace SharpLSI

theorem tendsto_of_approx_family {x : ℕ → ℝ} {α : ℝ} {u w : ℕ → ℕ → ℝ} {αR εR : ℕ → ℝ}
    (hsplit : ∀ R k, x k = u R k + w R k) (hu : ∀ R, Tendsto (u R) atTop (𝓝 (αR R)))
    (hw : ∀ R, ∀ᶠ k in atTop, |w R k| ≤ εR R) (hε : Tendsto εR atTop (𝓝 0))
    (hα : Tendsto αR atTop (𝓝 α)) : Tendsto x atTop (𝓝 α) := by
  rw [Metric.tendsto_atTop]
  intro ε hε0
  have h3 : 0 < ε / 3 := by positivity
  obtain ⟨R, hR1, hR2⟩ := ((hε.eventually (gt_mem_nhds h3)).and
    ((Metric.tendsto_nhds.1 hα) (ε / 3) h3)).exists
  obtain ⟨K1, hK1⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 (hu R)) (ε / 3) h3)
  obtain ⟨K2, hK2⟩ := eventually_atTop.1 (hw R)
  refine ⟨max K1 K2, fun k hk => ?_⟩
  have h1 := hK1 k (le_of_max_le_left hk)
  have h2 := hK2 k (le_of_max_le_right hk)
  rw [Real.dist_eq] at h1 hR2 ⊢
  rw [hsplit R k]
  calc |u R k + w R k - α| = |(u R k - αR R) + w R k + (αR R - α)| := by ring_nf
    _ ≤ |u R k - αR R| + |w R k| + |αR R - α| := abs_add_three _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

end SharpLSI
