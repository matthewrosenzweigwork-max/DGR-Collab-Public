import FullLabeledLSI.Defs.F03_RelFisher
import FullLabeledLSI.Paper.Sec3Diss

/-!
# S7: Proposition 3.1 (`prop:decomp`), exact entropy and dissipation decompositions

Manuscript Proposition 3.1, (3.1), (3.2). For every admissible finite family,
`G_θ(ρ) = G(ρ̄) + ∑ₐ θₐ H(ρₐ|ρ̄)` and `D_θ(ρ) = D(ρ̄) + ∑ₐ θₐ I(ρₐ|ρ̄)`; in particular `G_θ ≥ 0`.
`H(ρₐ|ρ̄)` is `klDiv` of the density measures; `I(ρₐ|ρ̄)` is `relFisher` (F3, the weighted-score
interpretation the manuscript uses on the finite-Fisher-information domain). (1.2) is assumed (the
proposition is stated in a section where it is standing).
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Proposition 3.1. -/
theorem species_decomposition {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible) :
    msGap V W F = gap V W (densMeasure F.bar) +
      ((∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) : ℝ≥0∞) :
        EReal) ∧
    msDiss V W F = dissipation V W F.bar + ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar ∧
    0 ≤ msGap V W F := by
  obtain ⟨h1, h3⟩ := msGap_decomp F hyp hF
  exact ⟨h1, msDiss_decomp F hyp hF, h3⟩

end SharpLSI.FL
