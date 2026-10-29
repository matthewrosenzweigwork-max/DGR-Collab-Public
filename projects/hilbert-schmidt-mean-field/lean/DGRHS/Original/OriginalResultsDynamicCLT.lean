import Batteries.Tactic.Alias
import DGRHS.Commutator.SourceLogOriginalDynamicCLT
import DGRHS.Commutator.SourceRieszOriginalDynamicCLT
import DGRHS.Commutator.SourceLogDistributionalClass
import DGRHS.Commutator.SourceRieszDistributionalClass

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). Source-facing export suite, area: dynamic CLT and the
mean-field solution class (thm:dynamicLinearStatisticsCLT, source 862–914;
cl:meanFieldWeak, source 3897–3908). All targets are new UNCOMPILED
candidates in this return (Riesz additionally depends on B's six UNCOMPILED
bodies). -/

/-- thm:dynamicLinearStatisticsCLT (862–914), LOG `s = 0`, original PV-distributional class. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_original_class :=
  DGRHS.Commutator.exists_sourceLog_original_class_named_Uprop_dynamic_joint_CLT

/-- thm:dynamicLinearStatisticsCLT (862–914), positive Riesz `0 < s < d/2`. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_original_class :=
  DGRHS.Commutator.exists_sourceRiesz_original_class_named_Uprop_dynamic_joint_CLT

/-- Mean-field solution class identification, LOG (3897–3908). -/
alias DGRHS.Original.cl_meanFieldWeak.log_pv_distributional_to_static :=
  DGRHS.Commutator.SourceLogPVDistributionalWeakMeanField.to_static

/-- Converse: the every-time bounded-C2 class gives the distributional class and trace. -/
alias DGRHS.Original.cl_meanFieldWeak.log_static_to_distributional :=
  DGRHS.Commutator.SourceLogStaticWeakMeanField.to_distributional

/-- Mean-field solution class identification, positive Riesz (3897–3908). -/
alias DGRHS.Original.cl_meanFieldWeak.riesz_pv_distributional_to_static :=
  DGRHS.Commutator.SourceRieszPVDistributionalWeakMeanField.to_static
