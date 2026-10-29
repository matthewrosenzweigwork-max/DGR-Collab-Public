import Batteries.Tactic.Alias
import DGRHS.Gaussian.PeriodicLogTheorem22i
import DGRHS.Gaussian.PeriodicLogTheorem22ii
import DGRHS.Gaussian.PeriodicLogTheorem211

/-! Source-facing export of Theorem 2.2(i) (`thm:partitionFunctionBound`, TeX 504-512) for the
LOG kernel on the torus `𝕋^d` (Remark 2.1, TeX 492-496), packet P9e.

Each `alias` creates a new declaration with EXACTLY the type of an existing root declaration (no
premise added or removed).  The torus kernel is `periodicLogKernel` (Fourier coefficients
`ĝ(k) = c_d/(2π)^d ‖k‖^{-d}`, `ĝ(0) = 0`, the exact `s → 0` analogue of the periodic Riesz kernel); the
hypotheses are those of the Euclidean `sourceLogSingularPartition_uniform` (`0 ≤ β`, probability
density `ρ ≤ M` a.e.), the pair-integrability hypothesis `hpair` being automatic on the torus.  The
`e^{-4βh_μ}` tail (part (ii)) is not assumed in the part (i) aliases; part (ii) and Proposition 2.11 are
covered by the packet P9g aliases appended below.  The module is not
imported by `Release.lean`; the coordinator wires it (new file, to avoid colliding with the P9d
append-only edits of `OriginalResultsPeriodicRiesz.lean`). -/

/-- thm:partitionFunctionBound(i) (source 504–512), torus LOG kernel: collision-free iid sample, one
constant `C` with `K_{N,β}(μ) ≤ C` for all `N ≥ 1`, real identification and positivity (packet P9e). -/
alias DGRHS.Original.thm_partitionFunctionBound.log_torus_uniform :=
  DGRHS.Periodic.periodicLog_partitionFunctionBound_collisionFree

/-- thm:partitionFunctionBound(i), torus LOG kernel, singular-partition form matching
`DGRHS.CLT.sourceLogSingularPartition_uniform` (packet P9e). -/
alias DGRHS.Original.thm_partitionFunctionBound.log_torus_singular_uniform :=
  DGRHS.Periodic.periodicLogSingularPartition_uniform

/-- thm:partitionFunctionBound(i), torus LOG kernel, modulated-integrand form matching
`DGRHS.CLT.sourceLogPartition_uniform` (packet P9e). -/
alias DGRHS.Original.thm_partitionFunctionBound.log_torus_integrand_uniform :=
  DGRHS.Periodic.periodicLogPartition_uniform

#print axioms DGRHS.Original.thm_partitionFunctionBound.log_torus_uniform
#print axioms DGRHS.Original.thm_partitionFunctionBound.log_torus_singular_uniform
#print axioms DGRHS.Original.thm_partitionFunctionBound.log_torus_integrand_uniform

/-! ### Packet P9g additions (append only)

Theorem 2.2(ii) (LOG branch) and Proposition 2.11 on the torus for the LOG gas (Remark 2.1).  The
printed LOG rate exponent `c_log(β,μ) > 0` is unspecified, so the heat-shift truncation covers EVERY
dimension; no range restriction is needed.  The two extra part-(ii) hypotheses
`∫ e^{-4βh_μ} dμ < ∞` and `g̃ ∈ L²(μ⊗μ)` are automatic on the torus class; `log_torus_rate` omits them
(the printed statement with them discharged), `log_torus_rate_printed` restates them as unused
hypotheses. -/

/-- thm:partitionFunctionBound(ii) (source 504-529), torus LOG kernel: `K_{N,β} → e^{βI_μ} det₂^{-1/2}`
with the power rate `(e+N)^{-c_log}`, `0 < c_log ≤ 1/2`, together with the Jensen lower bound and the
log-form rate; matches the union of the conclusions of `DGRHS.CLT.sourceLogSingularPartition_original_rate`
and `DGRHS.CLT.sourceLogSingularPartition_original_log_rate` (packet P9g). -/
alias DGRHS.Original.thm_partitionFunctionBound.log_torus_rate :=
  DGRHS.Periodic.periodicLogSingularPartition_original_rate

/-- thm:partitionFunctionBound(ii), torus LOG kernel, with the printed hypotheses
`eq:logRateExtraAssumptions` restated literally (unused; automatic on the torus; packet P9g). -/
alias DGRHS.Original.thm_partitionFunctionBound.log_torus_rate_printed :=
  DGRHS.Periodic.periodicLogSingularPartition_original_rate_printed

/-- prop:linearEmpiricalFluctuationCLT (source 805-831), torus LOG kernel, literal singular Gibbs law;
matches `DGRHS.CLT.exists_sourceLogSingularStatic` (packet P9g). -/
alias DGRHS.Original.prop_linearEmpiricalFluctuationCLT.log_torus :=
  DGRHS.Periodic.exists_periodicLogSingularStatic

/-- prop:linearEmpiricalFluctuationCLT, torus LOG kernel, physical canonical tilt; matches
`DGRHS.CLT.exists_sourceLogStatic` (packet P9g). -/
alias DGRHS.Original.prop_linearEmpiricalFluctuationCLT.log_torus_physical :=
  DGRHS.Periodic.exists_periodicLogStatic

#print axioms DGRHS.Original.thm_partitionFunctionBound.log_torus_rate
#print axioms DGRHS.Original.thm_partitionFunctionBound.log_torus_rate_printed
#print axioms DGRHS.Original.prop_linearEmpiricalFluctuationCLT.log_torus
#print axioms DGRHS.Original.prop_linearEmpiricalFluctuationCLT.log_torus_physical
