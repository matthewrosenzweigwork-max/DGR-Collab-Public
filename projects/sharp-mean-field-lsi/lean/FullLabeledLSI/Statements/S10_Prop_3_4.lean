import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Statements.R06_Upper_Bound
import FullLabeledLSI.Paper.Sec3Pos2

/-!
# S10: Proposition 3.4 (`prop:ms-positive`), positivity of `r_ms`

Manuscript Proposition 3.4, (3.10). Assume (1.2), `r_* > 0` and the coercivity (3.7)
`G(ρ) ≥ c H(ρ|μ)` with `c ∈ (0,1]`. Then `r_ms > 0`; more explicitly, with `B = ‖∇₁W‖_∞` and
`a = r_LS(μ)`, `r_ms ≥ [1/r_* + (2/a)(1 + B²/(c r_*))]⁻¹`.

Encodings: (3.7) is the coercivity clause of the symmetric `EquilibriumConclusion` (finite-entropy
probabilities, `EReal`). `B` is any real with `|∇₁W| ≤ B` a.e. on `𝕋^d × 𝕋^d` (the bound is
decreasing in `B`, so this is equivalent to `B = ‖∇₁W‖_∞`); `∇₁W = grad1W` (R6). The bound is
written in `ℝ≥0∞` arithmetic.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Proposition 3.4, (3.10). -/
theorem rMs_lower_bound {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcoer : ∀ ρ : ProbabilityMeasure (Torus d), klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
      (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) ≤
        gap V W ρ)
    (B : ℝ) (hB : ∀ᵐ X ∂(volume : Measure (Config 2 d)),
      sqNorm (fun k => grad1W W (X 0) (X 1) k) ≤ B ^ 2) :
    0 < rMs V W ∧
      ((rStar V W)⁻¹ + 2 * (rLS (μ : Measure (Torus d)))⁻¹ *
          (1 + ENNReal.ofReal (B ^ 2 / c) * (rStar V W)⁻¹))⁻¹ ≤ rMs V W := by
  exact rMs_lower_bound_aux hd hyp hr hμ hc hcoer hB

end SharpLSI.FL
