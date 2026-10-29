import Batteries.Tactic.Alias
import DGRHS.Commutator.SourceRieszOriginalDynamicCLTNarrow
import DGRHS.Commutator.SourceRieszOriginalFiniteNAdjointDuality
import DGRHS.Commutator.SourceLogOriginalFiniteNAdjointDuality
import DGRHS.Original.SourcePathTightness
import DGRHS.Original.SourcePathContinuousPaths

/-! Source-facing aliases (packet P12a) closing the three Euclidean rows that the status table still
marked conditional.  Every `alias` has exactly the type of its root declaration.  The module is not
imported by `Release.lean`; the coordinator wires it.

* Theorem 2.13 (`thm:dynamicLinearStatisticsCLT`, TeX 862-914), positive Riesz case: the release form
  is the narrow-continuity export of packet P3, whose hypothesis list is the printed one under the owner
  conventions (a) narrow continuity, (c) validity of the Ito formulas, and the PV-distributional reading
  of the weak mean-field class (equal to the printed symmetrized identity, TeX 3897-3904); the partition
  bounds (ii) are derived and there is no extended-energy hypothesis for `s > 0`.
* Proposition 8.2 (`prop:finiteNAdjointDuality`, TeX 3859-3877): as-printed exports in the class of
  Theorem 2.13 for both kernels (this packet).
* Remark 2.15 (`rem:pathSpaceCLT`, TeX 922-925): conditional by nature; the aliases below are the
  printed conditional implication (tightness + finite-dimensional convergence + measure-determining tests
  imply that every subsequential limit has the same law, hence convergence of the path laws). -/

/-- thm:dynamicLinearStatisticsCLT (TeX 862-914), positive Riesz `0 < s < d/2`, release form: the mean-field
trajectory is a narrowly continuous path in the PV-distributional weak class, partition bounds derived
(packet P3; ledger label: DEV as printed under conventions (a)-(c), packet P12a diagnosis). -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_original_class_as_printed :=
  DGRHS.Commutator.exists_sourceRiesz_original_class_narrow_dynamic_joint_CLT

/-- prop:finiteNAdjointDuality (TeX 3859-3877), positive Riesz, as printed in the class of Theorem 2.13:
the identity (8.2) with the Ito-integral martingale `M_N[f]`, its continuity and square integrability, and
the `L^1` rate `t D / (2 sqrt N)` of the commutator remainder (packet P12a). -/
alias DGRHS.Original.prop_finiteNAdjointDuality.riesz_original_class :=
  DGRHS.Commutator.exists_sourceRiesz_original_class_finiteN_adjoint_duality

/-- prop:finiteNAdjointDuality (TeX 3859-3877), logarithmic `s = 0`, as printed in the class of Theorem 2.13
with the extended-energy hypothesis (packet P12a). -/
alias DGRHS.Original.prop_finiteNAdjointDuality.log_original_class :=
  DGRHS.Commutator.exists_sourceLog_original_class_finiteN_adjoint_duality

/-- rem:pathSpaceCLT (TeX 922-925): every subsequential limit of the path laws has the finite-dimensional
laws of the target, hence equals the target law when the tests are measure determining. -/
alias DGRHS.Original.rem_pathSpaceCLT.subsequential_limit_unique :=
  DGRHS.Original.sourcePath_clusterPt_eq

/-- rem:pathSpaceCLT (TeX 922-925), conditional path-law convergence: tightness (`IsTightMeasureSet`),
finite-dimensional convergence (the output of Theorem 2.13), measure-determining continuous evaluations,
and a limit law `G` with the prescribed finite-dimensional laws. -/
alias DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_of_fdd :=
  DGRHS.Original.sourcePath_tendsto_of_isTight_of_fdd

/-- rem:pathSpaceCLT (TeX 922-925), with the finite-dimensional limit given as the Gaussian family of
`eq:dynamicFluctuationCovariance` and the Gaussian path law `G` realising it. -/
alias DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_of_gaussian_fdd :=
  DGRHS.Original.sourcePath_tendsto_of_isTight_of_gaussian_fdd

/-- rem:pathSpaceCLT (TeX 922-925), Polish path space: the measure-determining property is proved from
countably many point-separating continuous evaluations. -/
alias DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_polish :=
  DGRHS.Original.sourcePath_tendsto_of_isTight_polish

/-- rem:pathSpaceCLT (TeX 922-925), concrete separable path space `C([0,T],E)`, `E` complete separable
normed, dense times and point-separating functionals. -/
alias DGRHS.Original.rem_pathSpaceCLT.continuous_paths :=
  DGRHS.Original.sourceContinuousPath_tendsto_of_isTight

/-- rem:pathSpaceCLT (TeX 922-925): the Gaussian path law is determined by its finite-dimensional laws. -/
alias DGRHS.Original.rem_pathSpaceCLT.gaussian_law_unique :=
  DGRHS.Original.sourcePath_gaussian_law_unique

#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_original_class_as_printed
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.riesz_original_class
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.log_original_class
#print axioms DGRHS.Original.rem_pathSpaceCLT.subsequential_limit_unique
#print axioms DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_of_fdd
#print axioms DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_of_gaussian_fdd
#print axioms DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_polish
#print axioms DGRHS.Original.rem_pathSpaceCLT.continuous_paths
#print axioms DGRHS.Original.rem_pathSpaceCLT.gaussian_law_unique
