import FullLabeledLSI.Nonvacuity.Prop82.DMoment

/-!
# Lane D: the closed field `HalfTurnEntropyEstimates`
-/

namespace SharpLSI.FL.Prop82

theorem halfTurnEntropyEstimates : HalfTurnEntropyEstimates := fun _rho h =>
  ⟨halfTurn_finite h, halfTurn_fisher h, halfTurn_entropy h, fun hQ => halfTurn_moment h hQ⟩

end SharpLSI.FL.Prop82
