import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D13_Equilibrium
import SharpSymmetricLSI.Statements.R15_Contraction
import SharpSymmetricLSI.Paper.Coercivity4

/-!
# R16: Lemma 4.2 (`lem:coercivity`), global comparison with relative entropy

Manuscript Lemma 4.2. Assume (1.2), `r_* > 0`, and let `μ` be the (unique) minimizer. There is
`c ∈ (0,1]` with `G(ρ) ≥ c H(ρ|μ)` for every finite-entropy probability `ρ`.
-/

open MeasureTheory InformationTheory

namespace SharpLSI

variable {d : ℕ}

/-- Lemma 4.2. -/
theorem gap_ge_entropy {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ρ : ProbabilityMeasure (Torus d),
      klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
        (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ENNReal) : EReal) ≤
          gap V W ρ := by
  obtain ⟨-, huniq, -, hσ⟩ := minSet_singleton hd hyp hr hμ
  exact coercivity_of_unique_nondegenerate hyp hμ huniq hσ

end SharpLSI
