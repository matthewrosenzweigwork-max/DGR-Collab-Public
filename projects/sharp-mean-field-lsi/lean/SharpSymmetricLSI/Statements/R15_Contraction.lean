import SharpSymmetricLSI.Statements.R14_Local_Structure
import SharpSymmetricLSI.Paper.Sec42Final

/-!
# R15: Section 4.2, contraction of the minimizer set; (4.11)–(4.13)

Manuscript Section 4.2, "Contraction by the mean-field evolution". Assume (1.2), `r_* > 0`.
The map (4.12) contracts `𝒮` (with the weak topology) to a point, so `𝒮` is contractible; being
a compact manifold without boundary it is a point: `𝒮 = {μ}` and `ker(I+T) = {0}`; and (4.13)
`I + T ≥ σ I` for some `σ > 0`.
-/

open MeasureTheory

namespace SharpLSI

variable {d : ℕ}

/-- Section 4.2: `𝒮` is contractible, hence a point; `ker(I+T) = 0`; (4.13). -/
theorem minSet_singleton {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ContractibleSpace {ν : ProbabilityMeasure (Torus d) // IsMinimizer V W ν} ∧
    (∀ ν, IsMinimizer V W ν → ν = μ) ∧
    (∀ h, InKerIT W μ h → h =ᵐ[(μ : Measure (Torus d))] 0) ∧
    ∃ σ : ℝ, 0 < σ ∧ ∀ h, MemL20 μ h → σ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h := by
  exact minSet_singleton_aux hd hyp hr hμ

end SharpLSI
