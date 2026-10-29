import Batteries.Tactic.Alias
import DGRHS.Gaussian.PeriodicRieszSingularPartition
import DGRHS.Gaussian.PeriodicRieszTheorem22i
import DGRHS.Gaussian.PeriodicRieszTheorem22ii
import DGRHS.Gaussian.PeriodicRieszTheorem211
import DGRHS.Gaussian.PeriodicRieszLowerCutTheorem22ii

/-! Source-facing export of Theorem 2.2(i) (`thm:partitionFunctionBound`, TeX 504-512) for the
positive Riesz kernel on the torus `𝕋^d` (Remark 2.1, TeX 492-496), packet P9c.

Each `alias` creates a new declaration with EXACTLY the type of an existing root declaration (no
premise added or removed). Conventions follow `OriginalResultsPeriodic.lean`. The torus kernel is
the spectral periodic Riesz kernel `periodicRieszKernel` (`ĝ(k) = A_s ‖k‖^{s-d}`, `ĝ(0) = 0`) of
Remark 2.1; the proof follows the Lean route of the Euclidean endpoint (physical heat-time
band), not the printed Fourier-cutoff Lemma 4.3(i) route. The module is not imported by
`Release.lean`; the coordinator wires it. Part (ii) of the theorem (Riesz branch) is covered by the
packet P9d and P9f additions appended below; the LOG torus Theorem 2.2 is in
`OriginalResultsPeriodicLog.lean`. -/

/-- thm:partitionFunctionBound(i) (source 504–512), torus Riesz `0 < s < d/2`: collision-free
iid sample, one constant `C` with `K_{N,β}(μ) ≤ C` for all `N ≥ 1`, real identification and
positivity (packet P9c). -/
alias DGRHS.Original.thm_partitionFunctionBound.riesz_torus_uniform :=
  DGRHS.Periodic.periodicRiesz_partitionFunctionBound_collisionFree

/-- thm:partitionFunctionBound(i) (source 504–512), torus Riesz, singular-partition form matching
`DGRHS.CLT.sourceRieszSingularPartition_uniform` (packet P9c). -/
alias DGRHS.Original.thm_partitionFunctionBound.riesz_torus_singular_uniform :=
  DGRHS.Periodic.periodicRieszSingularPartition_uniform

/-- thm:partitionFunctionBound(i) (source 504–512), torus Riesz, modulated-integrand form matching
`DGRHS.CLT.sourceRieszPartition_uniform` (packet P9b). -/
alias DGRHS.Original.thm_partitionFunctionBound.riesz_torus_integrand_uniform :=
  DGRHS.Periodic.periodicRieszPartition_uniform

#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_uniform
#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_singular_uniform
#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_integrand_uniform

/-! ### Packet P9d additions (append only)

Theorem 2.2(ii) (Riesz branch) and Proposition 2.11 on the torus.  RANGE RESTRICTION of the rate
(superseded by the packet P9f section below): `riesz_torus_rate` carries the extra hypothesis
`d - 2s < 4` (the heat-shift truncation reaches the printed exponent `(d-2s)/(2s)` only there);
`riesz_torus_rate_saturated` gives the exponent `2/s` for `d - 2s > 4`.  The statement without any
range restriction is `riesz_torus_rate_full` below.  The LOG torus Theorem 2.2(i)
(`log_torus_uniform`) is delivered in `OriginalResultsPeriodicLog.lean`. -/

/-- thm:partitionFunctionBound(ii) (source 504-529), torus Riesz `0 < s < d/2` with `d - 2s < 4`:
`K_{N,β} → e^{βI_μ} det₂^{-1/2}` with rate `(log(e+N))^{-(d-2s)/(2s)}`, matching
`DGRHS.CLT.sourceRieszSingularPartition_original_rate` plus the hypothesis `d - 2s < 4`
(packet P9d).  Superseded by `riesz_torus_rate_full` (same conclusion, no range restriction). -/
alias DGRHS.Original.thm_partitionFunctionBound.riesz_torus_rate :=
  DGRHS.Periodic.periodicRieszSingularPartition_original_rate

/-- thm:partitionFunctionBound(ii), torus Riesz with `d - 2s > 4`: rate exponent `2/s`
(heat-shift saturation; weaker than the printed exponent; packet P9d).  Superseded by
`riesz_torus_rate_full`, which implies it. -/
alias DGRHS.Original.thm_partitionFunctionBound.riesz_torus_rate_saturated :=
  DGRHS.Periodic.periodicRieszSingularPartition_rate_saturated

/-- prop:linearEmpiricalFluctuationCLT (source 805-831), torus Riesz `0 < s < d/2`, literal
singular Gibbs law; matches `DGRHS.CLT.exists_sourceRieszSingularStatic` (packet P9d). -/
alias DGRHS.Original.prop_linearEmpiricalFluctuationCLT.riesz_torus :=
  DGRHS.Periodic.exists_periodicRieszSingularStatic

/-- prop:linearEmpiricalFluctuationCLT, torus Riesz, physical canonical tilt form matching
`DGRHS.CLT.exists_sourceRieszStatic` (packet P9d). -/
alias DGRHS.Original.prop_linearEmpiricalFluctuationCLT.riesz_torus_physical :=
  DGRHS.Periodic.exists_periodicRieszStatic

#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_rate
#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_rate_saturated
#print axioms DGRHS.Original.prop_linearEmpiricalFluctuationCLT.riesz_torus
#print axioms DGRHS.Original.prop_linearEmpiricalFluctuationCLT.riesz_torus_physical

/-! ### Packet P9f additions (append only)

Theorem 2.2(ii) (Riesz branch) on the torus at the PRINTED exponent `(d-2s)/(2s)` for the full range
`0 < s < d/2`, including `d - 2s = 4` and `d - 2s > 4` (the lower-cut Mellin truncation of
`eq:HCRStruncDef`).  `riesz_torus_rate_full` is the statement of `riesz_torus_rate` without the
extra hypothesis `d - 2s < 4`; it supersedes `riesz_torus_rate` (which stays as the first export) and
makes `riesz_torus_rate_saturated` redundant. -/

/-- thm:partitionFunctionBound(ii) (source 504-529), torus Riesz `0 < s < d/2`, FULL range: 
`K_{N,β} → e^{βI_μ} det₂^{-1/2}` with rate `(log(e+N))^{-(d-2s)/(2s)}`, matching
`DGRHS.CLT.sourceRieszSingularPartition_original_rate` with no extra hypothesis (packet P9f). -/
alias DGRHS.Original.thm_partitionFunctionBound.riesz_torus_rate_full :=
  DGRHS.Periodic.periodicRieszSingularPartition_original_rate_full

#print axioms DGRHS.Original.thm_partitionFunctionBound.riesz_torus_rate_full
