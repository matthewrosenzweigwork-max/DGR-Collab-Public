# Conditional uniform partition bound

The public theorem is `LogGasPaper.main_with_domain : PaperTheoremWithDomain` in
`../lean/PaperDomainSolution.lean`. Its separate specification is
`../lean/PaperDomainChallenge.lean`. It is a corollary of the original frozen
`LogGasPaper.main : PaperTheorem`; the original frozen statements are preserved.

For dimension `d ≥ 2`, `0 < B ≤ 2d`, and `0 ≤ β₀ < B`, there is a finite
`C = C(d, B, β₀)` such that `Z(N, β) ≤ C` for every `N ≥ 2` and `0 ≤ β ≤ β₀`,
for every normalized logarithmic kernel satisfying `LogHLSWithDomain g B`.
The constant is chosen before the kernel representative, particle number and coupling.

The space is the unit torus with Haar probability measure. The kernel is measurable
and integrable, has zero mean, and has Fourier coefficients
`c_d / (2π|k|)^d` for nonzero integer frequencies, where
`c_d = 2^(d-1) π^(d/2) Γ(d/2)`. The Fourier convention is `exp(-2π i k·x)`.
Kernel representatives agreeing almost everywhere give the same partition function.
The partition function is the extended nonnegative integral of
`exp(β/(2N) Σ_{i≠j} g(x_i-x_j))`; pairs are ordered and the sign is attractive.
Its upper bound by a finite constant genuinely excludes divergence.

`LogHLSWithDomain` assumes, for every nonnegative probability density of finite
entropy, absolute integrability of `g(x-y)(ρ(x)-1)(ρ(y)-1)` and the inequality
`(B/2) ∬ g(x-y)(ρ(x)-1)(ρ(y)-1) ≤ ∫ ρ log ρ`.
This explicit integrability condition is stronger than the totalized-integral
`LogHLS` hypothesis used by the original theorem. The implication between these
hypotheses is proved in the frozen specification. The new corollary makes no
claim that the stronger hypothesis has been established for any positive B.

The companion `LogGasPaper.kernel_exists` proves existence of a kernel with the
specified Fourier coefficients. It does not prove that the log-HLS hypothesis
is satisfiable. The release therefore certifies a conditional implication; no
unconditional positive-coupling instantiation is claimed.

The short draft's uniform partition bound is the primary correspondence target.
The canonical Part I order-one bound requires the additional macroscopic input
and threshold identification described in that manuscript. This release does
not formalize those inputs, the threshold identity, determinant asymptotics,
fluctuations, transported-reference results, or all of Part I or Part II.
The local asymptotic `g(x) = -log|x| + O(1)` is not an additional certified
conclusion. The ambient product metric and the separately defined Euclidean
radius are implementation choices; the public partition-bound statement
depends on the Fourier characterization and measure.

Reference TeX snapshots are retained under `reference/` for audit. They are
historical statement references, not replacements for the project's current
working manuscript. Historical comments inside frozen Lean files and earlier
verification records describe their original dates and scopes.

The original four targets remain checked alongside the public corollary:
`LogGasPaper.main`, `LogGasPaper.kernel_exists`, `LogGasChallenge.principal`,
and `LogGasChallenge.bulk`. The earlier H1/H2 targets have their own explicit
hypotheses; their inclusion does not enlarge the public theorem.

Machine checks, AI fidelity reviews, author scope decisions and publication
approval are distinct. Conversation decisions approving scope are recorded in
`author-decisions.json`; they do not represent completed independent human
certification or approval of every assertion in the accompanying manuscripts.
