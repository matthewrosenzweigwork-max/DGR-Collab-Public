import DGPS.Frontier.LIP032.T48
import DGPS.Frontier.LIP032.T49

/-!
## LIP032.15: Counterexample scalar rate is zero

Task id and title: LIP032.15, "Counterexample scalar rate is zero" (node LIP032, contractibility of the
minimizer set; leaf formalization, verification level V1). The base commit `6ccc9af` contains the
prerequisites LIP032.48 (`DGPS.Frontier.LIP032.T48`) and LIP032.49 (`DGPS.Frontier.LIP032.T49`), which
are used as dependencies. Paths are relative to `Campaign/`.

### Provides
* `DGPS.Frontier.LIP032.lip032_15_counterexample_scalar_rate_zero` : MAIN. For the explicit model `A_*`
  (`interactionDataStar_LIP03241`) and its classical-gradient drift `drift_*` (`driftStar_LIP03249`),
  `scalarRate A_* drift_* = 0` in `ℝ≥0∞`.
* `DGPS.Frontier.LIP032.lip032_15_counterexample_scalar_rate_zero_upper_LIP03215` : helper, the upper
  bound `scalarRate A_* drift_* ≤ 0`, obtained from the positive-gap competitor `ρ_H`.

### R5 notes
* Hypotheses. The main statement has no binders and adds no hypothesis. Its inputs are the constructed
  objects `interactionDataStar_LIP03241` (the model `A_*` of LIP032.41: `V_* = -4 γ²`,
  `W_*(x,y) = 4 (γ x - γ y)²`, `γ = cos (2π x)`) and `driftStar_LIP03249` (of LIP032.49). The statement
  is the equality of the brief; it is neither strengthened nor weakened.
* No positive-rate and no flow hypothesis. The premises `0 < r` and `ofReal r < scalarRate A drift` of the
  LIP031 result `DGPS.Lipschitz.positive_rate_flow_tails_and_limiting_minimizer`
  (`DGPS/Lipschitz/MinimizerRetraction.lean`, the header as read) are neither assumed nor used, and this
  unit does not invoke LIP031. The main result shows that the positive-rate premise cannot hold for
  `A_*` with `drift_*`: no real `r > 0` satisfies `ofReal r < scalarRate A_* drift_*`. This consequence is
  recorded, not a statement issue, because the counterexample lies outside the positive-rate context by
  design.
* Domain restriction. The torus is `d = 1`, the circle `Torus 1` with Haar probability `haar 1`; the
  restriction is fixed by `A_*`.
* Non-literal reading 1, the drift. "Validated classical-gradient drift" is read as `driftStar_LIP03249`:
  the drift whose force at each absolute density `ρ` is the classical gradient `smoothGrad` of the potential
  `V_* + W_* * (ρ m)`. "Validated" means that the LIP032.49 binding applies to it. The explicit formulas
  `G_*` and `B_*` of the source are not used.
* Non-literal reading 2, the rate. `scalarRate` is the infimum in `ℝ≥0∞`, over densities with positive gap,
  of `scalarDissipation / (2 * scalarGap)` (`DGPS.scalarRate`, `DGPS/Model/ScalarRate.lean`). The equality
  `= 0` is an equality in `ℝ≥0∞`; it is not a finiteness claim. The lower bound `0 ≤ scalarRate` is the
  trivial bound of `ℝ≥0∞`. The empty-infimum value `⊤` does not occur, because `ρ_H` is a positive-gap
  competitor.
* Non-literal reading 3, the denominator. The specification's `ofReal (2 G_H)` is the campaign expression
  `ENNReal.ofReal (2 * ↑(scalarGap A ρ))`, which is the form of the LIP032.49 rate interface. The proof uses
  that form directly, so no normalization step is needed.
* Positive gap. The competitor `ρ_H` (`absoluteRhoH_LIP03249`, the constant density `1`) has positive
  `scalarGap` (`scalarGap_absoluteRhoH_pos_LIP03249`), from the LIP032.48 lower bound `1/8 ≤ G_H`.
* Proof route. The rate interface of LIP032.49 gives `scalarRate ≤ scalarDissipation ρ_H / ofReal (2 G)`.
  The dissipation of `ρ_H` is zero for `drift_*`, because the campaign score vanishes almost everywhere at
  `ρ_H` (the LIP032.48 literal zero score `2 ∇√ρ_H + √ρ_H · force = 0`). So the quotient is
  `0 / ofReal (2 G)`, which is `0`. Hence the rate is at most `0`, and the main result follows from the
  trivial lower bound. The same dissipation vanishing holds for every weak-drift provider (LIP032.49
  `_any_provider`); this file uses the one drift the brief names.
* Representative choices. The score uses `weakGradient`, a chosen representative. The dissipation is a
  lower Lebesgue integral in `ℝ≥0∞`, so almost-everywhere vanishing of the score suffices. Nothing depends
  on the representative.
* Scope. This leaf does not touch the frozen contractibility statement of LIP032. The node note's
  statement-issue branch concerns that frozen statement and is not triggered by this leaf.
-/

namespace DGPS.Frontier.LIP032

/-- Helper: the scalar rate of `A_*` with drift `drift_*` is at most `0`. The competitor `ρ_H` has
positive gap and zero dissipation, so its quotient `0 / ofReal (2 G)` is `0`. -/
theorem lip032_15_counterexample_scalar_rate_zero_upper_LIP03215 :
    scalarRate interactionDataStar_LIP03241 driftStar_LIP03249 ≤ 0 := by
  have hle := (gate_lip032_49_named_density_drift_dissipation_rate_binding_rate_interface
    interactionDataStar_LIP03241 driftStar_LIP03249).2 absoluteRhoH_LIP03249
    scalarGap_absoluteRhoH_pos_LIP03249
  rw [scalarDissipation_absoluteRhoH_LIP03249, ENNReal.zero_div] at hle
  exact hle

/-- **LIP032.15.** For the explicit model `A_*` and its classical-gradient drift `drift_*`, the
scalar rate is zero: `scalarRate A_* drift_* = 0` in `ℝ≥0∞`. -/
theorem lip032_15_counterexample_scalar_rate_zero :
    scalarRate interactionDataStar_LIP03241 driftStar_LIP03249 = 0 :=
  le_antisymm lip032_15_counterexample_scalar_rate_zero_upper_LIP03215 zero_le

end DGPS.Frontier.LIP032
