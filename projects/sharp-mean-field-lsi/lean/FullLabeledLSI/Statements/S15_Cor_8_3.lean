import FullLabeledLSI.Defs.F01_Species
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D12_Cosine
import FullLabeledLSI.Statements.S01_Theorem_1_1
import FullLabeledLSI.Paper.Sec8Cosine

/-!
# S15: Corollary 8.3 (`cor:cosine`), the cosine interaction

Manuscript Corollary 8.3, (8.12), (8.13). On the unit circle, `V = 0`,
`W_κ(x,y) = κ(cos(2π(x-y)) - 1)`, `κ > 0` (`cosV`, `cosW κ` of the symmetric project, D12). For every
fixed `κ`: `lim r_{N,κ}^all = 4π² < r_{*,κ} = lim r_{N,κ}^sym`. The proof computes `r_ms = 4π²`,
which is also asserted. `aCos = 4π²` (D12).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

/-- Corollary 8.3, (8.13), with `r_ms = 4π²`. -/
theorem cosine_full_labeled_limit {κ : ℝ} (hκ : 0 < κ) :
    rMs cosV (cosW κ) = ENNReal.ofReal aCos ∧
      Tendsto (fun N => rAll cosV (cosW κ) N) atTop (𝓝 (ENNReal.ofReal aCos)) ∧
      ENNReal.ofReal aCos < rStar cosV (cosW κ) ∧
      Tendsto (fun N => rSym cosV (cosW κ) N) atTop (𝓝 (rStar cosV (cosW κ))) := by
  exact Sec8.cosine_core hκ (full_labeled_lsi_limit (le_refl 1) (SharpLSI.cosine_hyp hκ))

end SharpLSI.FL
