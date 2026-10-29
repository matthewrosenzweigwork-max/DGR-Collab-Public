import FullLabeledLSI.Nonvacuity.Prop82.Assembly
import FullLabeledLSI.Nonvacuity.Prop82.B4Attainment

/-!
# Lane B, module 5: the field `AttainmentBelowThreshold`

`Assembly.lean` is not modified; this file proves its `AttainmentBelowThreshold`
field from the core theorem of `B4Attainment`.
-/

namespace SharpLSI.FL.Prop82

/-- The exact statement of the field of `AnalyticSteps`, with no extra hypotheses. -/
theorem attainment_below_threshold : AttainmentBelowThreshold :=
  attainment_below_threshold_core

#print axioms attainment_below_threshold

end SharpLSI.FL.Prop82
