import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Sec8NoInt5

/-!
# S17: the closing remark of Section 8 (no interaction)

Manuscript, end of Section 8.5: when `W = 0` the Gibbs law is `μ^{⊗N}`, tensorization gives
`r_N^all = r_LS(μ)` for every `N`, and `r_ms = r_* = r_LS(μ)`.

Encodings: (1.2) for `V` with `W = 0`; `μ` is the minimizer of `F` (for `W = 0`, `μ ∝ e^{-V} m`);
"every `N`" is `N ≥ 1`.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The `W = 0` remark. -/
theorem no_interaction {V : Torus d → ℝ} {KV KW : ℝ} (hd : 1 ≤ d)
    (hyp : Hyp V (fun _ _ => 0) KV KW) (μ : ProbabilityMeasure (Torus d))
    (hμ : IsMinimizer V (fun _ _ => 0) μ) :
    (∀ N : ℕ, 1 ≤ N → rAll V (fun _ _ => 0) N = rLS (μ : Measure (Torus d))) ∧
      rMs V (fun _ _ => 0) = rLS (μ : Measure (Torus d)) ∧
      rStar V (fun _ _ => 0) = rLS (μ : Measure (Torus d)) := by
  exact Sec8.no_interaction_core hd hyp μ hμ

end SharpLSI.FL
