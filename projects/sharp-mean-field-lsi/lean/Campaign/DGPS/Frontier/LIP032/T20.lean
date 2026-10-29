import DGPS.Frontier.LIP032.T17

/-!
# LIP032.20: Log-partition Lipschitz bound

Task id and title: LIP032.20, "Log-partition Lipschitz bound" (node LIP032, contractibility of
the minimizer set; leaf formalization, no positive-rate hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_20_log_partition_lipschitz_bound` : for continuous real `U`, `V`
  on `𝕋^d`, `|log Z(U) - log Z(V)| ≤ ‖U - V‖_∞`, where `‖U - V‖_∞ = ⨆ x, |U x - V x|`.
* `DGPS.Frontier.LIP032.lip032_20_log_partition_lipschitz_bound_of_le` : the same estimate for
  every real `δ` with `|U x - V x| ≤ δ` for all `x` (the form used by the proof).

## R5 notes
* Hypotheses: `U V : Torus d → ℝ` continuous; nothing else. The normalizer `Z` is
  `normalizer_LIP03217` (LIP032.17), the Bochner integral `∫ e^{-U} dm` with `m = haar d`.
* The sup norm `‖U - V‖_∞` is spelled as the real supremum `⨆ x, |U x - V x|`. It is the true
  supremum because `|U - V|` is continuous on the compact torus, hence bounded above, so the
  `iSup` junk value for unbounded families is never used (the bound is proved in the file).
* "Each potential is bounded by compactness" is realised by deriving bounds `B_U`, `B_V` from
  continuity on the compact space `Torus d` and then applying LIP032.17 to each.
* All inequalities are between finite real integrals; positivity of `Z(V)` is used for the
  division and for monotonicity of the logarithm.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- A continuous real function on the torus is bounded in absolute value. -/
theorem exists_abs_bound_LIP03220 {U : Torus d → ℝ} (hc : Continuous U) :
    ∃ B : ℝ, ∀ x, |U x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_range hc.abs).bddAbove
  exact ⟨B, fun x => hB ⟨x, rfl⟩⟩

/-- The pointwise-bound form of the log-partition estimate. -/
theorem lip032_20_log_partition_lipschitz_bound_of_le
    {U V : Torus d → ℝ} (hU : Continuous U) (hV : Continuous V) {δ : ℝ}
    (hδ : ∀ x, |U x - V x| ≤ δ) :
    |Real.log (normalizer_LIP03217 U) - Real.log (normalizer_LIP03217 V)| ≤ δ := by
  obtain ⟨BU, hBU⟩ := exists_abs_bound_LIP03220 hU
  obtain ⟨BV, hBV⟩ := exists_abs_bound_LIP03220 hV
  obtain ⟨-, -, hZU, -⟩ := lip032_17_positive_normalized_exponential U hU BU hBU
  obtain ⟨-, -, hZV, -⟩ := lip032_17_positive_normalized_exponential V hV BV hBV
  have iU := integrable_exp_LIP03217 hU hBU
  have iV := integrable_exp_LIP03217 hV hBV
  have hlo : Real.exp (-δ) * normalizer_LIP03217 V ≤ normalizer_LIP03217 U := by
    have h := integral_mono (iV.const_mul (Real.exp (-δ))) iU (fun x => by
      have := abs_le.mp (hδ x)
      calc Real.exp (-δ) * Real.exp (-V x) = Real.exp (-δ + -V x) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-U x) := Real.exp_le_exp.mpr (by linarith [this.1, this.2]))
    simpa [normalizer_LIP03217, integral_const_mul] using h
  have hhi : normalizer_LIP03217 U ≤ Real.exp δ * normalizer_LIP03217 V := by
    have h := integral_mono iU (iV.const_mul (Real.exp δ)) (fun x => by
      have := abs_le.mp (hδ x)
      calc Real.exp (-U x) ≤ Real.exp (δ + -V x) :=
            Real.exp_le_exp.mpr (by linarith [this.1, this.2])
        _ = Real.exp δ * Real.exp (-V x) := Real.exp_add _ _)
    simpa [normalizer_LIP03217, integral_const_mul] using h
  rw [abs_le]
  have hl1 : Real.log (Real.exp (-δ) * normalizer_LIP03217 V) ≤
      Real.log (normalizer_LIP03217 U) :=
    Real.log_le_log (mul_pos (Real.exp_pos _) hZV) hlo
  have hl2 : Real.log (normalizer_LIP03217 U) ≤
      Real.log (Real.exp δ * normalizer_LIP03217 V) :=
    Real.log_le_log hZU hhi
  rw [Real.log_mul (Real.exp_pos _).ne' hZV.ne', Real.log_exp] at hl1 hl2
  constructor <;> linarith

/-- **LIP032.20.** For continuous real potentials `U`, `V` on the torus,
`|log Z(U) - log Z(V)| ≤ ‖U - V‖_∞`. -/
theorem lip032_20_log_partition_lipschitz_bound
    (U V : Torus d → ℝ) (hU : Continuous U) (hV : Continuous V) :
    |Real.log (normalizer_LIP03217 U) - Real.log (normalizer_LIP03217 V)| ≤
      ⨆ x, |U x - V x| := by
  have hb : BddAbove (Set.range fun x => |U x - V x|) :=
    (isCompact_range (hU.sub hV).abs).bddAbove
  exact lip032_20_log_partition_lipschitz_bound_of_le hU hV (fun x => le_ciSup hb x)

end DGPS.Frontier.LIP032
