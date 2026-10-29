import FullLabeledLSI.Defs.F04_Reveal
import FullLabeledLSI.Paper.PermAvg
import FullLabeledLSI.Paper.PermAvgFisher2

/-!
# S18: Lemma 5.1 (`lem:permutation`), permutation averaging

Manuscript Lemma 5.1, (5.1), (5.2). Let `ν` have a smooth positive density on `(𝕋^d)^N` and
`ν̄ = (N!)⁻¹ ∑_σ σ_# ν`. If `P` is permutation invariant with positive Lipschitz density, then
`H(ν|P) = H(ν̄|P) + H(ν|ν̄)` and `I(ν|P) = I(ν̄|P) + I(ν|ν̄)`.

Encodings: `σ_# ν = ν.map (· ∘ σ)` (averaging over all `σ` makes the direction of the action
irrelevant); `ν` and `P` are probability measures; `P = p m^{⊗N}` with `p > 0`, `p` Lipschitz (product
metric) and permutation invariant; `I = fisherInfoC`, `H = klDiv`, both in `ℝ≥0∞`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- The permutation average `ν̄ = (N!)⁻¹ ∑_σ σ_# ν`. -/
noncomputable def permAvg (ν : Measure (Config N d)) : Measure (Config N d) :=
  ((Nat.factorial N : ℝ≥0∞)⁻¹) • ∑ σ : Equiv.Perm (Fin N), ν.map (fun X => X ∘ σ)

/-- Lemma 5.1. -/
theorem permutation_averaging (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hν : HasSmoothPosDensity ν) (p : Config N d → ℝ) (hp : ∀ X, 0 < p X)
    (hpL : ∃ L, LipschitzWith L p) (hps : IsSymmetric p)
    (hP1 : IsProbabilityMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (p X))) :
    let P := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (p X)
    klDiv ν P = klDiv (permAvg ν) P + klDiv ν (permAvg ν) ∧
      fisherInfoC ν P = fisherInfoC (permAvg ν) P + fisherInfoC ν (permAvg ν) := by
  intro P
  exact ⟨permAvg_klDiv ν hν p hp hpL hps hP1, permAvg_fisher ν hν p hp hpL hps hP1⟩

end SharpLSI.FL
