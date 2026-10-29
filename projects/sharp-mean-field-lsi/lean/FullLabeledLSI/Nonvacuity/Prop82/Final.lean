import FullLabeledLSI.Nonvacuity.Prop82.B5Field
import FullLabeledLSI.Nonvacuity.Prop82.CFinal
import FullLabeledLSI.Nonvacuity.Prop82.DFinal
import FullLabeledLSI.Nonvacuity.Prop82.EFinal

/-!
# Proposition 8.2 is not vacuous: the unconditional theorem

The four analytic inputs of `AnalyticSteps` are proved in lanes B (attainment, `B*.lean`),
C (smooth positive representative, `C*.lean`), D (half-turn entropy estimates, `D*.lean`) and
E (heat stationarity, `E*.lean`).  This file assembles them.

The model is the coupling-one cosine model on the circle: `d = 1`, `V = 0`,
`W (x, y) = cos (2 π (x - y)) - 1`, `KV = 0`, `KW = 8 π²`.  No antecedent of
`SharpLSI.FL.quotient_optimizer_obstruction` is altered.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

/-- All four analytic steps, proved. -/
theorem analyticSteps : AnalyticSteps :=
  ⟨attainment_below_threshold, positive_smooth_representative, halfTurnEntropyEstimates,
    heat_stationarity⟩

/-- The density-dependent antecedents of Proposition 8.2 hold simultaneously in the model. -/
theorem nonvacuous : Nonvacuous := nonvacuity_of_analytic_steps analyticSteps

/-- The hypotheses of `quotient_optimizer_obstruction` are satisfiable, with `V`, `W`,
`KV`, `KW` and the density exhibited; all quantities are the original definitions. -/
theorem prop82_hypotheses_satisfiable :
    ∃ (V : Torus 1 → Real) (W : Torus 1 → Torus 1 → Real) (KV KW : Real),
      1 ≤ (1 : Nat) ∧ Hyp V W KV KW ∧
      ∃ rho : Torus 1 → Real, IsSmoothT rho ∧ (∀ x, 0 < rho x) ∧
        (∫ x, rho x ∂haar 1 = 1) ∧ 0 < gap V W (densMeasure rho) ∧
        dissipation V W rho = 2 * rStar V W * (gap V W (densMeasure rho)).toENNReal ∧
        poincareConst (densMeasure rho) < rStar V W := by
  obtain ⟨rho, hs, hp, hm, hG, ha, hP⟩ := nonvacuous
  exact ⟨cosV, cosW 1, 0, 2 * aCos, le_rfl, model_hyp, rho, hs, hp, hm, hG, ha, hP⟩

/-- The conclusion of Proposition 8.2 in the model, obtained by applying the unchanged
`quotient_optimizer_obstruction` to the exhibited density. -/
theorem prop82_applies :
    Tendsto (fun N => rAll cosV (cosW 1) N) atTop (𝓝 (rMs cosV (cosW 1))) ∧
    rMs cosV (cosW 1) < rStar cosV (cosW 1) ∧
    Tendsto (fun N => rSym cosV (cosW 1) N) atTop (𝓝 (rStar cosV (cosW 1))) :=
  obstruction_of_analytic_steps analyticSteps

end SharpLSI.FL.Prop82
