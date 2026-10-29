import FullLabeledLSI.Defs.F02_Constants
import FullLabeledLSI.Paper.Sec6Continuity

/-!
# S24: Lemma 6.2 (`lem:continuity`), continuity of the entropy and quadratic terms

Manuscript Lemma 6.2, (6.16), (6.17). If `X_n, Y_n` have a common `L^q` bound for some `q > 2` and
`‖X_n - Y_n‖_2 → 0`, then `Ent(X_n²) - Ent(Y_n²) → 0` and `E X_n² - E Y_n² → 0`; if `W_n` is bounded
in every finite `L^s`, then `E[(X_n² - Y_n²) W_n] → 0`. Each conclusion is uniform when the stated
bounds are common and the `L²` difference tends to zero uniformly (varying probability spaces).

Encoding: the uniform form, as a modulus. For `q > 2`, a bound `B` on `‖X‖_q, ‖Y‖_q` (and bounds
`Bs s` on `‖W‖_s`, `1 ≤ s < ⊤`) and `ε > 0` there is `δ > 0` such that on every probability space,
`‖X - Y‖_2 ≤ δ` implies the three differences are at most `ε`. This implies the sequential statement on
varying spaces. `Ent` is `ent` (finite here), read through `toReal`. Probability spaces are in `Type`.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

/-- Lemma 6.2, (6.16). -/
theorem entropy_continuity (q : ℝ≥0∞) (hq : 2 < q) (hq' : q ≠ ⊤) (B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ), MemLp X q P → MemLp Y q P →
      eLpNorm X q P ≤ ENNReal.ofReal B → eLpNorm Y q P ≤ ENNReal.ofReal B →
      eLpNorm (X - Y) 2 P ≤ ENNReal.ofReal δ →
      |(ent P (fun ω => X ω ^ 2)).toReal - (ent P (fun ω => Y ω ^ 2)).toReal| ≤ ε ∧
        |∫ ω, X ω ^ 2 ∂P - ∫ ω, Y ω ^ 2 ∂P| ≤ ε :=
  Sec6.entropy_modulus q hq hq' B ε hε

/-- Lemma 6.2, (6.17). -/
theorem weighted_continuity (q : ℝ≥0∞) (hq : 2 < q) (hq' : q ≠ ⊤) (B : ℝ) (Bs : ℝ≥0∞ → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y W : Ω → ℝ), MemLp X q P → MemLp Y q P →
      eLpNorm X q P ≤ ENNReal.ofReal B → eLpNorm Y q P ≤ ENNReal.ofReal B →
      (∀ s : ℝ≥0∞, 1 ≤ s → s ≠ ⊤ → MemLp W s P ∧ eLpNorm W s P ≤ ENNReal.ofReal (Bs s)) →
      eLpNorm (X - Y) 2 P ≤ ENNReal.ofReal δ →
      |∫ ω, (X ω ^ 2 - Y ω ^ 2) * W ω ∂P| ≤ ε :=
  Sec6.weighted_modulus q hq hq' B Bs ε hε

end SharpLSI.FL
