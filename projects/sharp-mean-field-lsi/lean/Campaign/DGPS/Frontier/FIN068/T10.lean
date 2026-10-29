import Mathlib
import DGPS.Frontier.FIN068.T26

/-!
Task id and title: FIN068.10, Value remainder and negative second derivative (module
`DGPS.Frontier.FIN068.T10`).

Provides:
* `DGPS.Frontier.FIN068.fin068_10_value_remainder_negative_second_derivative`: for `q` that is
  `C^∞` on an open set `U` containing a closed symmetric interval `Set.Icc (-δ) δ`, with
  `0 ≤ M` and `|q'''| ≤ M` on that interval, `q'(0) = 0`, `q''(0) = -2 c₄`, and every `y` with
  `y ^ 2` in the interval: (1) `|q(y²) - q 0 + c₄ (y²)²| ≤ M |y|⁶ / 6`; (2)
  `φ''(y) ≤ -12 c₄ y² + 5 M y⁴` for `φ(t) = q(t²)`; (3) if `y² ≤ 6 c₄ / (5 max(1, M))`, then
  `φ''(y) ≤ -6 c₄ y²`.

This is an assembly. The component arguments are the FIN068.25 scalar Taylor bounds and the
FIN068.26 composition formula with its bounds, which are proved there. The main declaration is
FIN068.26's bounds theorem with the identity conjunct removed.

R5 notes:
* Imports: `Mathlib` and `DGPS.Frontier.FIN068.T26` only. T26 imports T25. No legacy module is
  imported.
* `q 0` stands in for `ψ(w₋)` in the value bound (1). This is a non-literal reading. The
  identification `q 0 = ψ(w₋)` is the conclusion of FIN068.09
  (`fin068_09_reduced_quartic_coefficient`, item `q 0 = ψ(w₋)`). That file is not imported here,
  because it imports the legacy module `DGPS.FiniteN.QuarticSaddle`, which is not built in this
  worktree. The identification is therefore not re-proved in this file. A parameter
  `psiWm : ℝ` with hypothesis `q 0 = psiWm` would be equivalent. It is not added, because the
  specification does not list that hypothesis.
* Domain: `q` is `C^∞` on an open set `U ⊆ ℝ` with `Set.Icc (-δ) δ ⊆ U`, as in FIN068.25 and
  FIN068.26. The bound `|q'''| ≤ M` is required only on the closed interval. No particular domain
  such as the rectangle of FIN068.04 or the interval of FIN068.09 is fixed.
* "Sufficiently small closed interval" is read as the closed interval `Set.Icc (-δ) δ` on which
  the hypotheses hold. No size condition on `δ` is imposed, because the three inequalities hold
  for every such `δ`. For `δ < 0` the statement is vacuous.
* The variable `y` ranges over `ℝ`, with the hypothesis `y ^ 2 ∈ Set.Icc (-δ) δ`. The statement
  for `φ` is for every such `y`; `φ` is not required to be smooth elsewhere.
* "Thus on any smaller interval with `y² ≤ 6c₄/[5 max(1,M_q)]`" is read pointwise in `y`, on the
  set of `y` satisfying both `y² ∈ [-δ, δ]` and `y² ≤ 6 c₄ / (5 max(1, M))`. This is the
  conclusion (3). It is the same as a statement on the interval `{y : y² ≤ r}` for the radius
  `r = 6 c₄ / (5 max(1, M))`.
* `c₄` has no sign hypothesis. The positivity `c₄ = bd/(10240A) > 0` of the packet is not
  assumed. Conclusion (3) is vacuous when `c₄ < 0`, because then no `y` satisfies its hypothesis.
* `M_q ≥ 0` is included as `hM0`, as in the specification. It is used only through FIN068.26.
* `q'''` is read as `deriv (deriv (deriv q))`, `q'` as `deriv q`, `q''` as `deriv (deriv q)`, and
  `φ''(y)` as `deriv (deriv (fun t => q (t ^ 2))) y`, as in FIN068.25 and FIN068.26.
* The specification's chain-rule identity `φ''(y) = 2q'(y²) + 4y²q''(y²)` is used inside the
  proof of FIN068.26. It is not part of this file's statement.
-/

open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- FIN068.10. For `q` that is `C^∞` on an open `U` containing `[-δ, δ]`, with `0 ≤ M`,
`|q'''| ≤ M` on `[-δ, δ]`, `q'(0) = 0` and `q''(0) = -2 c₄`, and every `y` with `y²` in
`[-δ, δ]`: the value remainder bound for `q(y²)`, the bound
`φ''(y) ≤ -12 c₄ y² + 5 M y⁴` for `φ(t) = q(t²)`, and, when `y² ≤ 6 c₄ / (5 max(1, M))`,
the bound `φ''(y) ≤ -6 c₄ y²`. -/
theorem fin068_10_value_remainder_negative_second_derivative (q : ℝ → ℝ) (U : Set ℝ)
    (hU : IsOpen U) (δ c₄ M : ℝ) (hsub : Set.Icc (-δ) δ ⊆ U) (hq : ContDiffOn ℝ ∞ q U)
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Set.Icc (-δ) δ, |deriv (deriv (deriv q)) t| ≤ M)
    (hq1 : deriv q 0 = 0) (hq2 : deriv (deriv q) 0 = -2 * c₄) :
    ∀ y : ℝ, y ^ 2 ∈ Set.Icc (-δ) δ →
      |q (y ^ 2) - q 0 + c₄ * (y ^ 2) ^ 2| ≤ M * |y| ^ 6 / 6 ∧
      deriv (deriv (fun t => q (t ^ 2))) y ≤ -12 * c₄ * y ^ 2 + 5 * M * y ^ 4 ∧
      (y ^ 2 ≤ 6 * c₄ / (5 * max 1 M) →
        deriv (deriv (fun t => q (t ^ 2))) y ≤ -6 * c₄ * y ^ 2) := by
  intro y hy
  obtain ⟨_, h2, h3, h4⟩ :=
    fin068_26_composition_negative_curvature q U hU δ c₄ M hsub hq hM0 hM hq1 hq2 y hy
  exact ⟨h2, h3, h4⟩

end DGPS.Frontier.FIN068
