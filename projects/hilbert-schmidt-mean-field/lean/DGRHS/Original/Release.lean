import Batteries.Tactic.Alias
import DGRHS.Original.OriginalResultsStatic
import DGRHS.Original.OriginalResultsCommutatorDynamics
import DGRHS.Original.OriginalResultsAttractive
import DGRHS.Original.OriginalResultsDynamicCLT
import DGRHS.Original.OriginalResultsPeriodic
import DGRHS.Original.OriginalResultsConcentration
import DGRHS.Original.OriginalResultsPeriodicRiesz
import DGRHS.Original.OriginalResultsT28Printed
import DGRHS.Original.OriginalResultsPeriodicLog
import DGRHS.Original.OriginalResultsPeriodicCommutator
import DGRHS.Original.OriginalResultsProp33
import DGRHS.Original.OriginalResultsPeriodicStatic
import DGRHS.Original.OriginalResultsPeriodicDynamics
import DGRHS.Original.OriginalResultsPeriodicDynamicCLT
import DGRHS.Original.OriginalResultsRemark32
import DGRHS.Original.OriginalResultsConditionalsClosed
import DGRHS.Dynamics.SourceLogMeasurableTimeCoefficients
import DGRHS.Dynamics.SourceRieszMeasurableTimeCoefficients
import DGRHS.Commutator.SourceRieszEntropicCommutator
import DGRHS.Commutator.SourceRieszEntropicCommutatorPrinted
import DGRHS.Commutator.SourceT28FullRange
import DGRHS.Commutator.SourceLogOriginalDynamicCLTNarrow
import DGRHS.Commutator.SourceRieszOriginalDynamicCLTNarrow
import DGRHS.Commutator.SourceLogOriginalExtendedEnergyCLT
import DGRHS.Commutator.SourceLogThermalSourceCollisionFree
import DGRHS.Commutator.SourceRieszThermalSourceCollisionFree
import DGRHS.Decoupling.Prop33AsUsed
import DGRHS.Commutator.SourceRieszTransportLocal
import DGRHS.Original.OneBodyExpIntegrability
import DGRHS.Original.OriginalResultsKineticPartition
import DGRHS.Original.OriginalResultsKineticGibbs

/-! # DGRHS Tier 1 release module (coordinator, Claude phase, 2026-10-06)

This module imports every source-facing alias module of the original results of
arXiv:2609.02743v1 on `ℝ^d` (Tier 1 of `CLAUDE_COMPLETION_PLAN_20261006.md`) and
adds aliases for the endpoints produced in the Claude phase. Each alias has
exactly the type of its target. Building this module through the registered
coordinator route is the development baseline for the release set; it is not
protected acceptance, which remains a separate gate. Correspondence records for
each result are under `handoff/claude-20261006T114712Z/reviews/`. -/

/-- thm:diffusiveMeanFieldConvergence (TeX 737–770), LOG `s = 0`, with coefficients
measurable in time (packet P1; replaces the superseded pointwise-choice export). -/
alias DGRHS.Original.thm_diffusiveMeanFieldConvergence.log_measurable_coefficients :=
  DGRHS.Dynamics.exists_sourceLog_measurable_diffusive_bound

/-- thm:diffusiveMeanFieldConvergence (TeX 737–770), positive Riesz `0 < s < d/2`,
coefficients measurable in time (packet P1). -/
alias DGRHS.Original.thm_diffusiveMeanFieldConvergence.riesz_measurable_coefficients :=
  DGRHS.Dynamics.exists_sourceRiesz_measurable_diffusive_bound

/-- thm:entropicCommutator (TeX 691–707), positive Riesz `0 < s < d/2`; the entropic
inequality is asserted for laws with finite relative entropy to the modulated Gibbs
law (owner decision 1.2, 2026-10-06); constants exactly as printed in Remark A.1
(packet P2b). -/
alias DGRHS.Original.thm_entropicCommutator.riesz_finite_entropy :=
  DGRHS.Commutator.exists_sourceRiesz_entropic_commutator_printed_constants

/-- Same theorem with a background-uniform `C_em` (the printed constant times
`e^{β I_μ}`), chosen before the background (packet P2). -/
alias DGRHS.Original.thm_entropicCommutator.riesz_finite_entropy_uniform_constant :=
  DGRHS.Commutator.exists_sourceRiesz_entropic_commutator

/-- thm:entropicCommutator (TeX 691–707), single statement for `0 ≤ s < d/2`
(packet P2). -/
alias DGRHS.Original.thm_entropicCommutator.full_range :=
  DGRHS.Commutator.exists_source_entropic_commutator_full_range

/-- prop:decoup (TeX 1095–1104) as used by the paper: the `k = 2` real-valued
moment form (Remark 3.4) and its Markov tail corollary for iid coordinates; the
printed general-`k` Banach tail inequality is not formalized (Tier 3); packet P6. -/
alias DGRHS.Original.prop_decoup.k2_real_tail_from_moment_iid :=
  DGRHS.Decoupling.decoupling_tail_from_moment_k2_iid

#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.log_measurable_coefficients
#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.riesz_measurable_coefficients
#print axioms DGRHS.Original.thm_entropicCommutator.riesz_finite_entropy
#print axioms DGRHS.Original.thm_entropicCommutator.riesz_finite_entropy_uniform_constant
#print axioms DGRHS.Original.thm_entropicCommutator.full_range
#print axioms DGRHS.Original.prop_decoup.k2_real_tail_from_moment_iid

/-- thm:dynamicLinearStatisticsCLT (TeX 862–914), LOG, trajectory class given as a
narrowly continuous probability path (owner convention (a); packet P3). -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_narrow_class :=
  DGRHS.Commutator.exists_sourceLog_original_class_narrow_dynamic_joint_CLT

/-- thm:dynamicLinearStatisticsCLT (TeX 862–914), positive Riesz, narrow path (packet P3). -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_narrow_class :=
  DGRHS.Commutator.exists_sourceRiesz_original_class_narrow_dynamic_joint_CLT

/-- cor:entropicCommutatorTemperatureInterpolation (TeX 3547–3565), LOG, pointwise
premise on collision-free configurations only (packet P3). -/
alias DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.log_collision_free :=
  DGRHS.Commutator.exists_sourceLog_thermal_minimum_source_collisionFree

/-- cor:entropicCommutatorTemperatureInterpolation (TeX 3547–3565), positive Riesz,
signed finite-entropy form, collision-free premise (packet P3). -/
alias DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.riesz_collision_free :=
  DGRHS.Commutator.sourceRieszCommon_thermal_minimum_source_collisionFree

#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_narrow_class
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_narrow_class
#print axioms DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.log_collision_free
#print axioms DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.riesz_collision_free

/-- thm:dynamicLinearStatisticsCLT (TeX 862–914), LOG, narrow path with the printed
extended-energy lower bound `inf_t I_{μ^t} ≥ -J` (TeX 871–874) in place of the separate
pair-integrability and background-energy inputs (owner convention 1.2; packet P3b).
This is the release form; `log_narrow_class` is retained as its intermediate. -/
alias DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_narrow_extended_energy_class :=
  DGRHS.Commutator.exists_sourceLog_original_class_extended_energy_dynamic_joint_CLT

#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_narrow_extended_energy_class

/-- lem:localNumeratorComm (TeX 3307–3318), positive Riesz `0 < s < d/2`, with the
printed bound `e + L` (packet P4). -/
alias DGRHS.Original.lem_localNumeratorComm.riesz :=
  DGRHS.Commutator.exists_sourceRieszTransport_local_numerator

#print axioms DGRHS.Original.lem_localNumeratorComm.riesz

-- thm:partitionFunctionBound (TeX 504-512) on the torus, Remark 2.1, positive Riesz:
-- uniform bound (packet P9c; aliases live in `OriginalResultsPeriodicRiesz`).
#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_uniform
#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_singular_uniform

-- thm:entropicCommutator full range with the printed Remark A.1 constants pinned (packet P2c;
-- aliases live in `OriginalResultsT28Printed`; `full_range` is kept as the witness-free corollary).
#print axioms DGRHS.Original.thm_entropicCommutator.full_range_printed
#print axioms DGRHS.Original.lem_rieszJensen

-- Torus (Remark 2.1) results, packets P9d-P9h: Theorem 2.2(ii) Riesz at the printed exponent for the
-- full range, LOG Theorem 2.2(i)-(ii), Proposition 2.11 both kernels, Theorem 2.8 and Corollary 2.3 both
-- kernels. Aliases live in OriginalResultsPeriodicRiesz / PeriodicLog / PeriodicCommutator.
#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_rate_full
#print axioms DGRHS.Original.prop_linearEmpiricalFluctuationCLT.riesz_torus
#print axioms DGRHS.Original.thm_partitionFunctionBound.log_torus_uniform
#print axioms DGRHS.Original.thm_partitionFunctionBound.log_torus_rate
#print axioms DGRHS.Original.prop_linearEmpiricalFluctuationCLT.log_torus
#print axioms DGRHS.Original.thm_entropicCommutator.riesz_torus
#print axioms DGRHS.Original.thm_entropicCommutator.log_torus
#print axioms DGRHS.Original.cor_equilibriumFreeEnergyCorrection.riesz_torus
#print axioms DGRHS.Original.cor_equilibriumFreeEnergyCorrection.log_torus

-- Proposition 3.3 as printed (general k, Banach values, tail-to-tail; packet P10).
#print axioms DGRHS.Original.prop_decoup.banach_tail_general_k
#print axioms DGRHS.Original.prop_decoup.banach_moment_general_k

-- Torus Remark 2.12 and Theorem 2.6 (packet P11b). The general-measure uniform bound of Theorem 2.6
-- is faithful for mu << Haar; the pointwise-kernel restatement for singular mu is follow-up P11d.
#print axioms DGRHS.Original.rem_staticCLTInterpretation.riesz_torus
#print axioms DGRHS.Original.rem_staticCLTInterpretation.log_torus

-- Torus Lemma 7.2, Corollary 7.3 and Theorem 2.9 (packet P11a).
#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.riesz_torus
#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.log_torus
#print axioms DGRHS.Original.lem_localNumeratorComm.riesz_torus
#print axioms DGRHS.Original.lem_localNumeratorComm.log_torus
#print axioms DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.riesz_torus
#print axioms DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.log_torus

-- Torus Lemma 8.1, Proposition 8.2 and Theorem 2.13 (packets P11c, P11e). The `_torus` Theorem 2.13
-- aliases are the superseded time-tested form; the as-printed forms are `_torus_original_class`
-- (printed weak mean-field class with narrow continuity, P11e).
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus
#print axioms DGRHS.Original.lem_dynamicEntropyTransfers.riesz_torus
#print axioms DGRHS.Original.lem_dynamicEntropyTransfers.log_torus
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.riesz_torus
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.log_torus
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_torus_original_class
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.log_torus_original_class

-- Remark 3.2 in the corrected form (owner decision: inequality; packet P12b): A <= ||h||, B^2 <= (N-1)||h||^2,
-- C^2 = N(N-1)||h||^2, D <= N ||T_h||, with equality for A when N >= 2 and for B^2 with the essential sup.
#print axioms DGRHS.Original.rem_Ustattail.inequality_form

-- Euclidean Proposition 8.2 as printed in the Theorem 2.13 class, both kernels; Theorem 2.13 Riesz and
-- Remark 2.15 relabelled (packet P12a). Canonical Theorem 2.13 Riesz alias remains riesz_narrow_class.
#print axioms DGRHS.Original.thm_dynamicLinearStatisticsCLT.riesz_original_class_as_printed
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.riesz_original_class
#print axioms DGRHS.Original.prop_finiteNAdjointDuality.log_original_class
#print axioms DGRHS.Original.rem_pathSpaceCLT.subsequential_limit_unique
#print axioms DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_of_fdd
#print axioms DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_of_gaussian_fdd
#print axioms DGRHS.Original.rem_pathSpaceCLT.tendsto_of_isTight_polish
#print axioms DGRHS.Original.rem_pathSpaceCLT.continuous_paths
#print axioms DGRHS.Original.rem_pathSpaceCLT.gaussian_law_unique
