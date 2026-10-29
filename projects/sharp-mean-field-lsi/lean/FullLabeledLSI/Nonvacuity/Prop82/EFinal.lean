import FullLabeledLSI.Nonvacuity.Prop82.Assembly
import FullLabeledLSI.Nonvacuity.Prop82.E5_Stationarity

/-!
# Lane E, final: `HeatStationarity`

DRAFT written in the cloud without a compiler (lane E, cloud thread). This is the only lane E file
that imports `Assembly` (which imports the uncompiled-at-the-time `ExplicitTrial`).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

/-- The field `HeatStationarity` of `AnalyticSteps`, with exactly the statement of
`Assembly.lean`. -/
theorem heat_stationarity : HeatStationarity := by
  intro rho h hQ
  have hcore := HeatE.heat_stationarity_core h hQ
  have hmul : firstMode rho * alignedSecondMoment rho = HeatE.momNum rho := by
    unfold alignedSecondMoment
    rw [mul_div_cancel₀ _ hQ.ne']
    rfl
  have e : 3 * aCos ^ 2 * firstMode rho * alignedSecondMoment rho =
      3 * aCos ^ 2 * HeatE.momNum rho := by
    rw [mul_assoc, hmul]
  rw [e]
  exact hcore

end SharpLSI.FL.Prop82
