import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Statements.S01_Theorem_1_1
import FullLabeledLSI.Paper.Sec8Obstruction

/-!
# S13: Proposition 8.2 (`prop:quotient-optimizer`), an obstruction at a mean-field quotient optimizer

Manuscript Proposition 8.2, (8.5), (8.6). Assume (1.2). If `ρ` is a smooth strictly positive
probability density with `G(ρ) > 0` and `D(ρ) = 2 r_* G(ρ)`, and the ordinary Poincaré constant of
`ρ` is strictly smaller than `r_*`, then `lim r_N^all = r_ms < r_* = lim r_N^sym`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Proposition 8.2, (8.6). -/
theorem quotient_optimizer_obstruction {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (ρ : Torus d → ℝ) (hρs : IsSmoothT ρ)
    (hρp : ∀ x, 0 < ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) (hG : 0 < gap V W (densMeasure ρ))
    (hatt : dissipation V W ρ = 2 * rStar V W * (gap V W (densMeasure ρ)).toENNReal)
    (hP : poincareConst (densMeasure ρ) < rStar V W) :
    Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W)) ∧ rMs V W < rStar V W ∧
      Tendsto (fun N => rSym V W N) atTop (𝓝 (rStar V W)) := by
  exact Sec8.quotient_optimizer_core hd hyp (full_labeled_lsi_limit hd hyp) hρs hρp hρ1 hG hatt hP

end SharpLSI.FL
