import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Statements.R09_Cosine_Upper
import SharpSymmetricLSI.Statements.R12_Cosine_Strict

/-!
# R38: Remark 3.4 (`rem:cosine-qualitative`), the mathematical inequality

Manuscript Remark 3.4 and (1.11): `limsup_N r^all_{N,κ} ≤ a < r_{*,κ}`. Only this inequality
is formalized; the claims about the hypotheses and normalization of [DGPS, Conjecture 1] are
a documented remark (statement map), not a Lean statement.
-/

open Filter

namespace SharpLSI

/-- Remark 3.4 / (1.11). -/
theorem cosine_contradicts_dgps {κ : ℝ} (hκ : 0 < κ) :
    limsup (fun N => rAll cosV (cosW κ) N) atTop ≤ ENNReal.ofReal aCos ∧
      ENNReal.ofReal aCos < rStar cosV (cosW κ) := by
  refine ⟨limsup_le_of_le (by isBoundedDefault) ?_, cosine_strict hκ⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact cosine_rAll_le hκ hN

end SharpLSI
