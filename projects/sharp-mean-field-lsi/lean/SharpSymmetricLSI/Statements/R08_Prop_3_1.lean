import SharpSymmetricLSI.Statements.R39_Prop_3_5
import SharpSymmetricLSI.Paper.Cosine31
import SharpSymmetricLSI.Statements.R01_Theorem_1_1

/-!
# R8: Proposition 3.1 (`prop:cosine-separation`), cosine counterexample

Manuscript Proposition 3.1, (3.5), (3.6): for every fixed `κ > 0`, the cosine potentials satisfy
(1.2) (some `K_V, K_W ≥ 0`); `0 < inf_{N≥1} r^all_{N,κ}`; `r^all_{N,κ} ≤ a` for every `N ≥ 1`;
and `a < r_{*,κ} = lim_N r^sym_{N,κ} ≤ a min{1+κ/2, 4}`.
-/

open Filter Topology

namespace SharpLSI

/-- Proposition 3.1. -/
theorem prop_cosine {κ : ℝ} (hκ : 0 < κ) :
    (∃ KV KW : ℝ, Hyp cosV (cosW κ) KV KW) ∧
    0 < ⨅ N ∈ {N : ℕ | 1 ≤ N}, rAll cosV (cosW κ) N ∧
    (∀ N : ℕ, 1 ≤ N → rAll cosV (cosW κ) N ≤ ENNReal.ofReal aCos) ∧
    ENNReal.ofReal aCos < rStar cosV (cosW κ) ∧
    Tendsto (fun N => rSym cosV (cosW κ) N) atTop (𝓝 (rStar cosV (cosW κ))) ∧
    rStar cosV (cosW κ) ≤ ENNReal.ofReal (aCos * min (1 + κ / 2) 4) := by
  exact prop_cosine_of hκ (sharp_symmetric_lsi_limit le_rfl (cosine_hyp_aux hκ))

end SharpLSI
