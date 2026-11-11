import PaperSolution

/-! Public corollary with explicit integrability. The statement is repeated verbatim
from PaperDomainChallenge so the two environments can be checked separately.
-/

namespace LogGasPaper

open scoped NNReal ENNReal

/-- Uniform partition bound assuming that every finite-entropy probability density
has an absolutely integrable interaction-energy integrand and satisfies log-HLS.
The constant is chosen before the kernel representative, particle number and coupling.
-/
def PaperTheoremWithDomain : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ B : ℝ, 0 < B → B ≤ 2 * d → ∀ β₀ : ℝ, 0 ≤ β₀ → β₀ < B →
    ∃ C : ℝ≥0, ∀ g : Torus d → ℝ, IsLogKernel d g → LogHLSWithDomain g B →
      ∀ N : ℕ, 2 ≤ N → ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → partitionFunction g N β ≤ (C : ℝ≥0∞)

theorem main_with_domain : PaperTheoremWithDomain := by
  intro d hd B hB0 hB β₀ hβ0 hβB
  obtain ⟨C, hC⟩ := main d hd B hB0 hB β₀ hβ0 hβB
  exact ⟨C, fun g hg hH N hN β hβ hβle =>
    hC g hg hH.toLogHLS N hN β hβ hβle⟩

end LogGasPaper
