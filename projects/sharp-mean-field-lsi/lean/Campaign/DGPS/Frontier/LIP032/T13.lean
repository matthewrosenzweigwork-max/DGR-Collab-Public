import DGPS.Frontier.LIP032.T41
import DGPS.Frontier.LIP032.T43
import DGPS.Frontier.LIP032.T45

/-!
# LIP032.13: Compact minimizing set with nonzero cosine moments

Task id and title: LIP032.13, "Compact minimizing set with nonzero cosine moments" (node LIP032,
contractibility of the minimizer set; leaf formalization of the explicit unit-circle counterexample
interaction `A_*`).

## Provides
* `DGPS.Frontier.LIP032.lip032_13_compact_minimizing_set_nonzero_cosine_moments`: MAIN. For the
  explicit interaction `A_*` on `𝕋¹` with `V_* = -4 γ²` and `W_*(x, y) = 4 (γ x - γ y)²`: the
  potentials of `A_*` are `V_*` and `W_*`; they are smooth; `A_*` is Lipschitz in the sense of
  `LipschitzData`; `W_*` is symmetric and vanishes on the diagonal; the minimizer set `S_*` is
  nonempty and weakly compact; and every `ν ∈ S_*` has nonzero cosine moment `M(ν) = ∫ γ dν`.

## R5 notes
* The model is the explicit `A_* = interactionDataStar_LIP03241` of LIP032.41, with
  `γ(x) = cos(2π x)` on `𝕋¹` (the campaign function `cosMode`, whose lift to `ℝ` is `s ↦ cos(2π s)`),
  `V_* = -4 γ²` and `W_*(x, y) = 4 (γ x - γ y)²`. The main statement records that the data of `A_*`
  are these two functions, so the explicit formulas are pinned down by the specification.
* "Smooth" for `V_*` is the campaign predicate `IsSmoothPeriodic` (the lift to `Fin 1 → ℝ` is `C^∞`).
  The campaign has no smoothness predicate for functions of two torus points, so "smooth" for `W_*`
  is read as `C^∞` of the lift `(s, t) ↦ W_*(lift s, lift t)` on `(Fin 1 → ℝ) × (Fin 1 → ℝ)`.
* "Lipschitz" is the campaign predicate `LipschitzData` (DEF007): the existence of a constant `L` with
  `|V_* x - V_* y| ≤ L · torusDist x y`, and of a constant `L` with
  `|W_* x y - W_* x' y'| ≤ L √(torusDist x x'² + torusDist y y'²)`. The explicit constants of LIP032.41
  are not stated here; the statement asserts only the existence of constants, as in the campaign
  predicate.
* "Symmetric and zero on the diagonal" is stated for `W_*`; the same facts hold for `A_*.W` by
  definition of `A_*`.
* The minimizer set `S_*` is `minimizerSetStar_LIP03244` of LIP032.44: the set of probabilities `ν` on
  `𝕋¹` with `freeEnergy A_* ν = freeEnergyMinimum A_*` in `EReal`. The free energy is the campaign
  DEF008 value `H(ν | m) + ∫ V_* dν + (1/2) ∬ W_* d(ν ⊗ ν)` with `m = haar 1`, and the minimum is the
  infimum over all Borel probabilities. Membership is exact equality in `EReal`; finiteness of the
  entropy of a minimizer is not assumed but derived (LIP032.43, from LIP017).
* "Nonempty" is read as the existence of a probability `ν` with `freeEnergy A_* ν = freeEnergyMinimum A_*`
  (LIP017, conjunct 1, through LIP032.43).
* "Weakly compact" is read as `IsCompact` for the topology of `ProbabilityMeasure (𝕋¹)`, which is
  Mathlib's topology of weak convergence of probability measures (campaign LIB05). Compactness comes
  from LIP032.45 (the level set of the parameter energy is compact and `S_* = μ_P(J_*)`).
* `M(ν) = ∫ γ dν` is `momentStar_LIP03241` applied to the underlying measure of `ν`. The claim
  `M(ν) ≠ 0` is stated for minimizers only; the stronger bound `1/32 ≤ M(ν)²` of LIP032.43 is not part
  of the main statement.
* No positive-rate, flow, LIP031 or LIP028 hypothesis occurs. The LIP031 header (`0 < r`,
  `ofReal r < scalarRate A drift`) is not inherited: none of the prerequisites LIP032.41 to LIP032.45
  uses LIP031. The statement is therefore unconditional, which is the intended reading for this
  explicit counterexample, and no statement issue arises. No hypothesis is added to the specification.
* The proof assembles the conjuncts of LIP032.41 (smoothness, data, Lipschitz, symmetry, diagonal),
  the nonemptiness and moment conjuncts of LIP032.43, and the compactness conjunct of LIP032.45.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.LIP032

/-- MAIN (LIP032.13). For the explicit unit-circle interaction `A_*` with `V_* = -4 γ²` and
`W_*(x, y) = 4 (γ x - γ y)²`, the potentials are smooth and Lipschitz, the interaction is symmetric
and vanishes on the diagonal, the minimizer set `S_*` is nonempty and weakly compact, and every
`ν ∈ S_*` satisfies `M(ν) = ∫ γ dν ≠ 0`. -/
theorem lip032_13_compact_minimizing_set_nonzero_cosine_moments :
    (interactionDataStar_LIP03241.V = VStar_LIP03241 ∧
        interactionDataStar_LIP03241.W = WStar_LIP03241) ∧
      (IsSmoothPeriodic VStar_LIP03241 ∧
        ContDiff ℝ ∞ (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
          WStar_LIP03241 (torusLift p.1) (torusLift p.2))) ∧
      LipschitzData interactionDataStar_LIP03241 ∧
      ((∀ x y, WStar_LIP03241 x y = WStar_LIP03241 y x) ∧ ∀ x, WStar_LIP03241 x x = 0) ∧
      (minimizerSetStar_LIP03244.Nonempty ∧ IsCompact minimizerSetStar_LIP03244) ∧
      ∀ ν ∈ minimizerSetStar_LIP03244, momentStar_LIP03241 (ν : Measure (Torus 1)) ≠ 0 := by
  obtain ⟨-, -, hsV, hsW⟩ := lip032_41_smooth_model_exact_one_moment_energy_smooth
  obtain ⟨hdV, hdW, hLip⟩ := lip032_41_smooth_model_exact_one_moment_energy_data
  obtain ⟨hsymm, hdiag⟩ := lip032_41_smooth_model_exact_one_moment_energy_symm_diag
  obtain ⟨hne, -, hmom⟩ := lip032_43_strict_negative_minimum_nonzero_cosine_moments
  obtain ⟨-, hcpt⟩ := lip032_45_compactness_through_closed_parameter_energy_level_minimizer_set
  exact ⟨⟨hdV, hdW⟩, ⟨hsV, hsW⟩, hLip, ⟨hsymm, hdiag⟩, ⟨hne, hcpt⟩,
    fun ν hν => (hmom ν hν).2⟩

end DGPS.Frontier.LIP032
