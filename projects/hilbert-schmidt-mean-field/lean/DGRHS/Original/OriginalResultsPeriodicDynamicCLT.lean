import Batteries.Tactic.Alias
import DGRHS.Gaussian.PeriodicRieszDynamicTransfers
import DGRHS.Gaussian.PeriodicLogDynamicTransfers
import DGRHS.Gaussian.PeriodicProp82Terminal
import DGRHS.Gaussian.PeriodicProp82CF
import DGRHS.Gaussian.PeriodicRieszNamedDynamicCLT
import DGRHS.Gaussian.PeriodicLogNamedDynamicCLT
import DGRHS.Gaussian.PeriodicRieszOriginalDynamicCLT
import DGRHS.Gaussian.PeriodicLogOriginalDynamicCLT
import DGRHS.Gaussian.PeriodicRieszOriginalDynamicCLTDensity
import DGRHS.Gaussian.PeriodicLogOriginalDynamicCLTDensity

/-! Source-facing export (packet P11c) of the dynamical results on the flat torus `𝕋^d`
(Remark 2.1 `rem:torus-kinetic-variants`, TeX 492-496).

Each `alias` creates a new declaration with EXACTLY the type of an existing root declaration (no
premise added or removed).  The module is not imported by `Release.lean`; the coordinator wires it.

Lemma 8.1 (`lem:dynamicEntropyTransfers`, TeX 3771-3794) and Proposition 8.2
(`prop:finiteNAdjointDuality`, TeX 3859-3877, terminal representation and characteristic-function
comparison) for both torus kernels.  Printed hypotheses added: the uniform partition bounds (ii)
(`K_{N,β}(μ^t) ≤ Cpart`, `K_{N,2β}(μ^t) ≤ C₂`, TeX 877-881); the pair-log integrability and the lower
interaction energy of the torus LOG kernel are theorems, so the LOG statements carry no `J` or `c`. -/

/-- lem:dynamicEntropyTransfers (source 3771-3794), torus Riesz, `0 < s < d/2`. -/
alias DGRHS.Original.lem_dynamicEntropyTransfers.riesz_torus :=
  DGRHS.Periodic.periodicRieszDynamic_entropy_transfers

/-- lem:dynamicEntropyTransfers (source 3771-3794), torus LOG, `s = 0`. -/
alias DGRHS.Original.lem_dynamicEntropyTransfers.log_torus :=
  DGRHS.Periodic.periodicLogDynamic_entropy_transfers

/-- prop:finiteNAdjointDuality (source 3859-3877), terminal representation, torus Riesz. -/
alias DGRHS.Original.prop_finiteNAdjointDuality.riesz_torus :=
  DGRHS.Periodic.exists_periodicRiesz_finite_terminal_representation

/-- prop:finiteNAdjointDuality (source 3859-3877), terminal representation, torus LOG. -/
alias DGRHS.Original.prop_finiteNAdjointDuality.log_torus :=
  DGRHS.Periodic.exists_periodicLog_finite_terminal_representation

/-- prop:finiteNAdjointDuality (source 3859-3877 with 3952-4012), characteristic-function
comparison, torus Riesz. -/
alias DGRHS.Original.prop_finiteNAdjointDuality.riesz_torus_CF :=
  DGRHS.Periodic.exists_periodicRiesz_finite_terminal_CF_comparison

/-- prop:finiteNAdjointDuality (source 3859-3877 with 3952-4012), characteristic-function
comparison, torus LOG. -/
alias DGRHS.Original.prop_finiteNAdjointDuality.log_torus_CF :=
  DGRHS.Periodic.exists_periodicLog_finite_terminal_CF_comparison

/-- thm:dynamicLinearStatisticsCLT (source 862-914), torus Riesz `0 < s < d/2`, named propagator
`U^{r,t} φ`, lifted particle formulation, mean-field class in its time-tested form (conditional form; the
printed-class export, which derives this form, is `thm_dynamicLinearStatisticsCLT.riesz_torus_original_class`). -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus :=
  DGRHS.Periodic.exists_periodicRiesz_named_Uprop_dynamic_joint_CLT

/-- thm:dynamicLinearStatisticsCLT (source 862-914), torus LOG `s = 0`, named propagator `U^{r,t} φ`, lifted
particle formulation, mean-field class in its time-tested form (conditional form; the printed-class export,
which derives this form, is `thm_dynamicLinearStatisticsCLT.log_torus_original_class`); the extended-energy
hypothesis `eq:dynamicUniformLogEnergy` is a theorem on the torus. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus :=
  DGRHS.Periodic.exists_periodicLog_named_Uprop_dynamic_joint_CLT

/-! Packet P11e: Theorem 2.13 on the torus with the mean-field trajectory in the printed class (a narrowly
continuous path of bounded-density probability measures satisfying the mean-field equation (2.32) in its
symmetrized weak form `eq:dynamicMeanFieldWeakIdentity`, in the distributional sense against smooth tests; owner convention `OWNER_DECISIONS_20261006.md` 1.2).  The
time-tested form of the P11c exports is derived (`periodicMeanFieldWeak_timeTested`).  The `_of_density`
variants also derive the partition bounds (ii) from the density-uniform torus constants of packet P11a. -/

/-- thm:dynamicLinearStatisticsCLT (source 862-914), torus Riesz `0 < s < d/2`, mean-field trajectory in
the printed weak class (narrow continuity, distributional equation), named propagator `U^{r,t} φ`, lifted
particle formulation; the partition bounds (ii) are hypotheses. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus_original_class :=
  DGRHS.Periodic.exists_periodicRiesz_original_class_dynamic_joint_CLT

/-- thm:dynamicLinearStatisticsCLT (source 862-914), torus LOG `s = 0`, mean-field trajectory in the
printed weak class (narrow continuity, distributional equation), named propagator `U^{r,t} φ`, lifted
particle formulation; the partition bounds (ii) are hypotheses and the extended-energy hypothesis is a
theorem on the torus. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus_original_class :=
  DGRHS.Periodic.exists_periodicLog_original_class_dynamic_joint_CLT

/-- thm:dynamicLinearStatisticsCLT (source 862-914), torus Riesz, as `riesz_torus_original_class` with the
uniform partition bounds (ii) derived from the density-uniform torus constants. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus_original_class_of_density :=
  DGRHS.Periodic.exists_periodicRiesz_original_class_dynamic_joint_CLT_of_density

/-- thm:dynamicLinearStatisticsCLT (source 862-914), torus LOG, as `log_torus_original_class` with the
uniform partition bounds (ii) derived from the density-uniform torus constants. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus_original_class_of_density :=
  DGRHS.Periodic.exists_periodicLog_original_class_dynamic_joint_CLT_of_density

#print axioms DGRHS.Original.lem_dynamicEntropyTransfers.riesz_torus
#print axioms DGRHS.Original.lem_dynamicEntropyTransfers.log_torus
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.riesz_torus
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.log_torus
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.riesz_torus_CF
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.log_torus_CF
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus_original_class
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus_original_class
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus_original_class_of_density
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus_original_class_of_density
