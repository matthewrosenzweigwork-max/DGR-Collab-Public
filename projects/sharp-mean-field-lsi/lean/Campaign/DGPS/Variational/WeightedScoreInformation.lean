import DGPS.Variational.ScoreDecomposition
import DGPS.Variational.SpeciesGap

/-!
# Weighted-score information decomposition (DEF015)

Under the standing model data, with `s̄ = 2 ∇√ρ̄ / √ρ̄` on `{ρ̄ > 0}` and `0` elsewhere
(`DGPS.SpeciesFamily.score`), every `I_s = ∫ |2 ∇u_s - u_s s̄|² dm` is finite and
`D_θ = D(ρ̄) + ∑ θ_s I_s` in `ℝ≥0∞`.  Obtained as the dissipation projections of LIP003
(`DGPS.Lipschitz.square_root_mixture_and_score_decompositions`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS

variable {d : ℕ}

/-- DEF015: every weighted-score information `I_s` is finite. -/
theorem def015_scoreInformation_ne_top (F : SpeciesFamily d) (s : Fin F.count) :
    F.scoreInformation s ≠ ⊤ :=
  (F.scoreInformation_ne_top s).1

/-- DEF015 (weighted-score information decomposition): every `I_s` is finite and
`D_θ = D(ρ̄) + ∑ θ_s I_s` in `ℝ≥0∞`. -/
theorem speciesDissipation_decomposition (A : InteractionData d) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) :
    (∀ s, F.scoreInformation s ≠ ⊤) ∧
    speciesDissipation A b F = scalarDissipation A b (barycenter F) +
      ∑ s, ENNReal.ofReal (F.weight s) * F.scoreInformation s := by
  have h := Lipschitz.square_root_mixture_and_score_decompositions A b F
  exact ⟨fun s => (h.2.2.2.2.1 s).1, h.2.2.2.2.2.2.2⟩

end DGPS
