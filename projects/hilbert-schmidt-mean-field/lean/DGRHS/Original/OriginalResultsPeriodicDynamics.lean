import Batteries.Tactic.Alias
import DGRHS.Gaussian.PeriodicLocalNumeratorExport
import DGRHS.Gaussian.PeriodicRieszThermalCollisionFree
import DGRHS.Gaussian.PeriodicLogThermalCollisionFree
import DGRHS.Dynamics.PeriodicRieszMeasurableTimeCoefficients
import DGRHS.Dynamics.PeriodicLogMeasurableTimeCoefficients

/-! Source-facing export (packet P11a) of Lemma 7.2, Corollary 7.3 and Theorem 2.9 on the flat torus
`𝕋^d` (Remark 2.1 `rem:torus-kinetic-variants`, TeX 492-496).

Each `alias` creates a new declaration with EXACTLY the type of an existing root declaration (no
premise added or removed).  The module is not imported by `Release.lean`; the coordinator wires it.

Unit 1: Lemma 7.2 (`lem:localNumeratorComm`, TeX 3307-3318), both kernels.
Unit 2: Corollary 7.3 (`cor:entropicCommutatorTemperatureInterpolation`, TeX 3547-3579), both
kernels, pointwise premise on collision-free configurations.
Unit 3: Theorem 2.9 (`thm:diffusiveMeanFieldConvergence`, TeX 737-770) with measurable time
coefficients, both kernels, and the uniform-in-time form of Remark 2.10 (`rem:uniform-generation-chaos`). -/

/-- lem:localNumeratorComm (source 3307-3318), torus Riesz `0 < s < d/2`, printed bound `e + L`;
matches `DGRHS.Commutator.exists_sourceRieszTransport_local_numerator` (packet P11a). -/
alias DGRHS.Original.lem_localNumeratorComm.riesz_torus :=
  DGRHS.Periodic.exists_periodicRieszTransport_local_numerator

/-- lem:localNumeratorComm (source 3307-3318), torus LOG, bound `e`; matches
`DGRHS.Commutator.exists_sourceLogTransport_local_numerator` without the Euclidean hypotheses
`0 < d` and `eq:logEnergyAssumption` (automatic on the torus; packet P11a). -/
alias DGRHS.Original.lem_localNumeratorComm.log_torus :=
  DGRHS.Periodic.exists_periodicLogTransport_local_numerator

/-- cor:entropicCommutatorTemperatureInterpolation (source 3547-3579), torus Riesz, finite-relative-
entropy competitors, pointwise premise on collision-free configurations; matches
`DGRHS.Commutator.sourceRieszCommon_thermal_minimum_source_collisionFree` except for the position of the
constants: as in the torus Theorem 2.8 export, `βloc` stands before `β`, `Cub, Cpf` after `ρ`, and the
printed `Cem` is built from `I_μ`, whereas the Euclidean export has `Cpf, Cem` before `K, v, ρ`
(this is the printed dependence `C_pf(β,μ)`, `C_em(β,μ,v,n)`; packet P11a, review section 4.1). -/
alias DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.riesz_torus :=
  DGRHS.Periodic.exists_periodicRiesz_thermal_minimum_collisionFree

/-- cor:entropicCommutatorTemperatureInterpolation (source 3547-3579), torus LOG, every probability
competitor, pointwise premise on collision-free configurations; matches
`DGRHS.Commutator.exists_sourceLog_thermal_minimum_source_collisionFree` without the Euclidean
hypotheses `0 < d` and pair integrability (automatic on the torus), and with two additional
partition-function conclusions (packet P11a). -/
alias DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.log_torus :=
  DGRHS.Periodic.exists_periodicLog_thermal_minimum_collisionFree

/-- thm:diffusiveMeanFieldConvergence (source 737-770), torus Riesz `0 < s < d/2`, measurable time
coefficients; matches `DGRHS.Dynamics.exists_sourceRiesz_measurable_diffusive_bound` (packet P11a). -/
alias DGRHS.Original.thm_diffusiveMeanFieldConvergence.riesz_torus :=
  DGRHS.Dynamics.exists_periodicRiesz_measurable_diffusive_bound

/-- thm:diffusiveMeanFieldConvergence (source 737-770), torus LOG, measurable time coefficients;
matches `DGRHS.Dynamics.exists_sourceLog_measurable_diffusive_bound` without the Euclidean hypotheses
`0 < K t`, pair integrability and the control `J` (all absent on the torus; packet P11a). -/
alias DGRHS.Original.thm_diffusiveMeanFieldConvergence.log_torus :=
  DGRHS.Dynamics.exists_periodicLog_measurable_diffusive_bound

/-- thm:diffusiveMeanFieldConvergence (TeX 737-804), torus Riesz, constant-coefficient case under uniform
scalar controls (packet P11a). This is NOT Remark 2.10's uniform-in-time statement: with a > 0 the
Gronwall factor A^t = e^{at} is unbounded (P11a review, issue 1). -/
alias DGRHS.Original.thm_diffusiveMeanFieldConvergence.riesz_torus_constant_coefficients :=
  DGRHS.Dynamics.exists_periodicRiesz_uniform_physical_diffusive_bound

/-- thm:diffusiveMeanFieldConvergence (TeX 737-804), torus LOG, constant-coefficient case under uniform
scalar controls; torus twin of `DGRHS.Dynamics.exists_sourceLog_uniform_physical_diffusive_bound`
(packet P11a). This is NOT Remark 2.10's uniform-in-time statement: with a > 0 the Gronwall factor
A^t = e^{at} is unbounded (P11a review, issue 1). -/
alias DGRHS.Original.thm_diffusiveMeanFieldConvergence.log_torus_constant_coefficients :=
  DGRHS.Dynamics.exists_periodicLog_uniform_physical_diffusive_bound

#print axioms DGRHS.Original.lem_localNumeratorComm.riesz_torus
#print axioms DGRHS.Original.lem_localNumeratorComm.log_torus
#print axioms DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.riesz_torus
#print axioms DGRHS.Original.cor_entropicCommutatorTemperatureInterpolation.log_torus
#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.riesz_torus
#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.log_torus
#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.riesz_torus_constant_coefficients
#print axioms DGRHS.Original.thm_diffusiveMeanFieldConvergence.log_torus_constant_coefficients
