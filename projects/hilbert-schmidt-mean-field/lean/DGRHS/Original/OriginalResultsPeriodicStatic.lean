import Batteries.Tactic.Alias
import DGRHS.Gaussian.PeriodicStaticRemark212
import DGRHS.Gaussian.PeriodicAttractiveLogPartition
import DGRHS.Gaussian.PeriodicAttractiveLogPartitionPointwise
import DGRHS.Gaussian.PeriodicAttractiveOriginalRate
import DGRHS.Gaussian.PeriodicAttractiveBoundedDensity

/-! Source-facing export (packet P11b) of Remark 2.12 and Theorem 2.6 on the flat torus `𝕋^d`
(Remark 2.1 `rem:torus-kinetic-variants`, TeX 492-496).

Each `alias` creates a new declaration with EXACTLY the type of an existing root declaration (no premise
added or removed).  The module is not imported by `Release.lean`; the coordinator wires it.

Remark 2.12 (`rem:staticCLTInterpretation`, TeX 832-861): two-sided covariance comparison with `T_μ ≥ 0`
and the equilibrium identification `Q_{N,β}(μ_β) = P_{N,β}`, for the periodic Riesz kernel `0 < s < d/2`
and the periodic LOG kernel.

Theorem 2.6 (`thm:attractive-log-small-beta-partition`, TeX 615-644): uniform bound and quantitative
determinant rate for the torus attractive LOG interaction `-g`. -/

/-- rem:staticCLTInterpretation (source 832-861), torus Riesz: covariance bounds
`‖φ̄‖²/(1+β‖T_μ‖) ≤ Σ_{β,μ}(φ,φ) ≤ ‖φ̄‖²`; matches `DGRHS.CLT.exists_sourceRieszCovarianceBounds`
(packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.riesz_torus :=
  DGRHS.Periodic.periodicRiesz_covarianceBounds

/-- rem:staticCLTInterpretation, torus Riesz: `Q_{N,β}(μ_β)` is the collision-zero canonical ensemble
for `N ≥ 1`, with proper weight and positive finite normalizer; matches
`DGRHS.CLT.sourceRiesz_equilibrium_canonical` (packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.riesz_torus_equilibrium_canonical :=
  DGRHS.Periodic.periodicRiesz_equilibrium_canonical

/-- rem:staticCLTInterpretation, torus Riesz: `Q_{N,β}(μ_β) = P_{N,β}` for every `N`; matches
`DGRHS.CLT.sourceRiesz_equilibrium_law_allN` (packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.riesz_torus_equilibrium_law :=
  DGRHS.Periodic.periodicRiesz_equilibrium_law_allN

/-- rem:staticCLTInterpretation, torus Riesz: the static CLT for the original canonical ensemble with the
printed full-`L²` covariance bounds; matches `DGRHS.CLT.exists_sourceRieszCanonicalStatic` (packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.riesz_torus_canonical_static :=
  DGRHS.Periodic.exists_periodicRieszCanonicalStatic

/-- rem:staticCLTInterpretation (source 832-861), torus LOG: covariance bounds; matches
`DGRHS.CLT.exists_sourceLogCovarianceBounds` (packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.log_torus :=
  DGRHS.Periodic.periodicLog_covarianceBounds

/-- rem:staticCLTInterpretation, torus LOG: `Q_{N,β}(μ_β)` is the canonical ensemble for `N ≥ 1`; matches
`DGRHS.CLT.sourceLog_equilibrium_canonical` (packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.log_torus_equilibrium_canonical :=
  DGRHS.Periodic.periodicLog_equilibrium_canonical

/-- rem:staticCLTInterpretation, torus LOG: `Q_{N,β}(μ_β) = P_{N,β}` for every `N`; matches
`DGRHS.CLT.sourceLog_equilibrium_law_allN` (packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.log_torus_equilibrium_law :=
  DGRHS.Periodic.periodicLog_equilibrium_law_allN

/-- rem:staticCLTInterpretation, torus LOG: the static CLT for the original canonical ensemble with the
printed full-`L²` covariance bounds; matches `DGRHS.CLT.exists_sourceLogCanonicalStatic` (packet P11b). -/
alias DGRHS.Original.rem_staticCLTInterpretation.log_torus_canonical_static :=
  DGRHS.Periodic.exists_periodicLogCanonicalStatic

/-- thm:attractive-log-small-beta-partition (source 615-630), torus: uniform bound
`sup_N K^att_{N,β} ≤ C_ub^att(β,μ)` with the explicit constant of TeX 2586-2594; matches
`DGRHS.Attractive.attractiveLogPartition_uniform` (packet P11b).  The kernel is the a.e.-class representative
`periodicLogKernel`: this form is faithful for `μ ≪ Haar` only (review P11b section 5); the form for the
pointwise kernel valid for every probability measure is `uniform_torus_pointwise`. -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_torus :=
  DGRHS.Periodic.periodicAttractiveLogPartition_uniform

/-- thm:attractive-log-small-beta-partition (source 615-630), torus: uniform bound for
`0 ≤ β < β_0 = 1/(C_* C_mom)`; matches `DGRHS.Attractive.attractiveLogPartition_uniform_threshold`
(packet P11b).  The kernel is the a.e.-class representative `periodicLogKernel`: this form is faithful for
`μ ≪ Haar` only (review P11b section 5); the form for the pointwise kernel valid for every probability
measure is `uniform_threshold_torus_pointwise`. -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_threshold_torus :=
  DGRHS.Periodic.periodicAttractiveLogPartition_uniform_threshold

/-- thm:attractive-log-small-beta-partition (source 631-644), torus: the quantitative determinant limit
`|K_{N,β}^att - K_{∞,β}^att| ≤ C (e+N)^{-c}` for `0 < β < β_q`, bounded background density; matches
`DGRHS.Attractive.exists_attractiveLog_original_quantitative_rate`.  The singular pair-`L¹` hypothesis and
`e^{4β h_μ^att} ∈ L¹(μ)` are automatic on the torus and not assumed (packet P11b). -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.quantitative_rate_torus :=
  DGRHS.Periodic.exists_periodicAttractiveLog_original_quantitative_rate

/-- thm:attractive-log-small-beta-partition (source 631-644), torus: the same with the two printed
hypotheses restated literally (unused; packet P11b). -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.quantitative_rate_torus_printed :=
  DGRHS.Periodic.exists_periodicAttractiveLog_original_quantitative_rate_printed

/-- thm:attractive-log-small-beta-partition, torus, uniform bound for every bounded background density with
no moment, pair-integrability or exponential-integrability hypothesis (`C_mom` is the explicit torus constant
`periodicRowConstant ι M`); supplement of packet P11b to the clause `uniform_threshold_torus`. -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_torus_density :=
  DGRHS.Periodic.periodicAttractiveLogPartition_uniform_density

/-- thm:attractive-log-small-beta-partition, torus, quantitative rate for every bounded background density
with no moment, pair-integrability or exponential-integrability hypothesis; supplement of packet P11b to the
clause `quantitative_rate_torus`. -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.quantitative_rate_torus_density :=
  DGRHS.Periodic.exists_periodicAttractiveLog_quantitative_rate_density

#print axioms DGRHS.Original.rem_staticCLTInterpretation.riesz_torus
#print axioms DGRHS.Original.rem_staticCLTInterpretation.riesz_torus_equilibrium_canonical
#print axioms DGRHS.Original.rem_staticCLTInterpretation.riesz_torus_equilibrium_law
#print axioms DGRHS.Original.rem_staticCLTInterpretation.riesz_torus_canonical_static
#print axioms DGRHS.Original.rem_staticCLTInterpretation.log_torus
#print axioms DGRHS.Original.rem_staticCLTInterpretation.log_torus_equilibrium_canonical
#print axioms DGRHS.Original.rem_staticCLTInterpretation.log_torus_equilibrium_law
#print axioms DGRHS.Original.rem_staticCLTInterpretation.log_torus_canonical_static
#print axioms DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_torus
#print axioms DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_threshold_torus
#print axioms DGRHS.Original.thm_attractive_log_small_beta_partition.quantitative_rate_torus
#print axioms DGRHS.Original.thm_attractive_log_small_beta_partition.quantitative_rate_torus_printed
#print axioms DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_torus_density
#print axioms DGRHS.Original.thm_attractive_log_small_beta_partition.quantitative_rate_torus_density

/-- thm:attractive-log-small-beta-partition (source 615-630), torus, pointwise kernel: uniform bound
`sup_N K^att_{N,β} ≤ C_ub^att(β,μ)` for every probability measure `μ` on `𝕋^d`, with the attractive
interaction `-g_d` written with the pointwise representative `periodicLogPairFun` of the periodic LOG kernel
(even, measurable, smooth off `0`, Haar-a.e. equal to `periodicLogKernel`); same hypotheses and constants as
`uniform_torus`, which is the `μ ≪ Haar` form; matches `DGRHS.Attractive.attractiveLogPartition_uniform`
(packet P11d). -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_torus_pointwise :=
  DGRHS.Periodic.periodicAttractiveLogPartitionPw_uniform

/-- thm:attractive-log-small-beta-partition (source 615-630), torus, pointwise kernel: uniform bound for
`0 ≤ β < β_0 = 1/(C_* C_mom)` for every probability measure `μ` on `𝕋^d`; same hypotheses and constants as
`uniform_threshold_torus`; matches `DGRHS.Attractive.attractiveLogPartition_uniform_threshold`
(packet P11d). -/
alias DGRHS.Original.thm_attractive_log_small_beta_partition.uniform_threshold_torus_pointwise :=
  DGRHS.Periodic.periodicAttractiveLogPartitionPw_uniform_threshold
