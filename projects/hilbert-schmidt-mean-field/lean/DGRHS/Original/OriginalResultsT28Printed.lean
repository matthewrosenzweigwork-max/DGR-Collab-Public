import Batteries.Tactic.Alias
import DGRHS.Commutator.SourceT28FullRangePrinted
import DGRHS.Commutator.SourceRieszJensen

/-! Source-facing aliases for packet P2c (Theorem 2.8 full range with the printed constants
of Remark A.1, and the standalone Riesz Jensen lower bound `eq:KlowerJensen`).

Each `alias` creates a new declaration with EXACTLY the type of its target (no premise added or
removed). The module is not imported by `Release.lean`; the coordinator wires it. -/

/-- thm:entropicCommutator (TeX 691-707), single statement for `0 ≤ s < d/2`, with the printed
constants of Remark A.1 (`eq:CemLargeBetaDef`) pinned in the statement: Riesz
`e+L` / `e^{-βI_μ}(e+L)^{1/2}C_ub^{1/2}`, LOG `e^{-βI_μ}(e+L)` / `e^{-βI_μ}(e+L)^{1/2}C_ub^{1/2}`,
and `ε = 1`, `C_em = 1` for a zero Lipschitz constant at `s = 0`.  Two qualifications (packet P2c review):
for `0 < s` and a zero Lipschitz constant the Riesz branch carries the `K > 0` row (`ε = 1`, `C_em ≥ 1`)
rather than the printed `C_em = 1`, and the LOG `ε` is pinned in printed form only, since `C_sr` is
existential (packet P2c). -/
alias DGRHS.Original.thm_entropicCommutator.full_range_printed :=
  DGRHS.Commutator.exists_sourceT28_full_range_printed

/-- Jensen lower bound (TeX 432-436, `eq:KlowerJensen`) for the literal collision-zero Riesz
modulated partition function: `K_{N,β}(μ) ≥ exp(β I_μ)`, `0 < s < d/2`, `μ` a probability density
bounded by `M`, `β ≥ 0`, `N ≥ 1` (packet P2c). -/
alias DGRHS.Original.lem_rieszJensen :=
  DGRHS.Commutator.sourceRieszJensen_singularPartition

#print axioms DGRHS.Original.thm_entropicCommutator.full_range_printed
#print axioms DGRHS.Original.lem_rieszJensen
