import Batteries.Tactic.Alias
import DGRHS.Kinetic.KineticModulatedPartition
import DGRHS.Kinetic.KineticTheorem28Moment

/-! Packet P14b: Original aliases for the kinetic half of Remark 2.1
(`rem:torus-kinetic-variants`, TeX 495): kinetic modulated partition-function estimates
(Theorem 2.2 (i), (ii)) and the kinetic exponential moment (2.21) of Theorem 2.8.
Each alias has exactly the type of the underlying declaration. -/

/-- rem:torus-kinetic-variants (kinetic half), Theorem 2.2(i) Riesz, kinetic partition function. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceRieszPartition_uniform := DGRHS.Kinetic.kinetic_sourceRieszPartition_uniform

/-- rem:torus-kinetic-variants (kinetic half), Theorem 2.2(i) log, kinetic partition function. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceLogPartition_uniform := DGRHS.Kinetic.kinetic_sourceLogPartition_uniform

/-- rem:torus-kinetic-variants (kinetic half), Theorem 2.2(ii) Riesz rate. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_source_riesz_partition_rate := DGRHS.Kinetic.kinetic_source_riesz_partition_rate

/-- rem:torus-kinetic-variants (kinetic half), Theorem 2.2(ii) log rate. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_source_log_partition_rate := DGRHS.Kinetic.kinetic_source_log_partition_rate

/-- rem:torus-kinetic-variants (kinetic half), Theorem 2.8 exponential moment (2.21), kinetic. -/
alias DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceT28_exponential_moment := DGRHS.Kinetic.kinetic_sourceT28_exponential_moment

#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceRieszPartition_uniform
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceLogPartition_uniform
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_source_riesz_partition_rate
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_source_log_partition_rate
#print axioms DGRHS.Original.rem_torus_kinetic_variants.Kinetic_kinetic_sourceT28_exponential_moment
