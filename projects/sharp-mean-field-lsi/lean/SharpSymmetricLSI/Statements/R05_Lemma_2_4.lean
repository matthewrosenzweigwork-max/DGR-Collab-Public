import SharpSymmetricLSI.Defs.D05_FreeEnergy
import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Paper.PartitionLimit

/-!
# R5: Lemma 2.4 (`lem:partition`), the partition-function limit

Manuscript Lemma 2.4, (2.9): under (1.2), `N^{-1} log Z_N → -F_*`.
(`F_*` is finite under (1.2), `exists_minimizer`; the limit is stated in `EReal`.)
-/

open Filter Topology

namespace SharpLSI

variable {d : ℕ}

/-- Lemma 2.4. -/
theorem partition_limit {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    Tendsto (fun N : ℕ => ((Real.log (partitionFn V W N) / N : ℝ) : EReal)) atTop
      (𝓝 (-Fstar V W)) := by
  exact partition_limit_aux hyp

end SharpLSI
