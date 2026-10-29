import DGPS.Frontier.LIP032.T34
import Mathlib.Topology.ContinuousMap.Compact

/-!
# LIP032.07: Lipschitz approximation of continuous tests

Task id and title: LIP032.07, "Lipschitz approximation of continuous tests" (node LIP032,
contractibility of the minimizer set; leaf formalization, verification level V1). The statement
uses no positive-rate or flow hypothesis, so the defect FD-001 of the isolated frozen LIP032
sentence is not touched by this unit.

## Provides
* `DGPS.Frontier.LIP032.lip032_07_lipschitz_approximation_continuous_tests` : for a continuous real
  `φ` on a compact metric space `X` and every `ε > 0`, there are `L ≥ 0` and a function
  `φε : X → ℝ` that is `L`-Lipschitz (`LipschitzWith L.toNNReal φε`) with `|φ x - φε x| ≤ ε` for
  every `x`, which is the bound `‖φ - φε‖∞ ≤ ε`.
* `DGPS.Frontier.LIP032.lip032_07_lipschitz_approximation_continuous_tests_sup` : the same
  conclusion with the sup-norm bound stated literally in `C(X, ℝ)`: `φε` is a continuous map
  `ψ : C(X, ℝ)`, `L`-Lipschitz, and `‖⟨φ, hφ⟩ - ψ‖ ≤ ε`.
* `DGPS.Frontier.LIP032.pointwise_nonempty_LIP03207` : helper, the pointwise conclusion of the main
  statement on a nonempty compact metric space. Its witness is the real infimum `infConv_LIP03233`
  of LIP032.33 at the constant `L = (2 * ‖φ‖∞ + ε) / δ`, with `δ` from LIP032.34; no minimizing
  point is chosen or exported.

## R5 notes
* Ambient space: a general `MetricSpace X` with `CompactSpace X`, as in LIP032.33 and LIP032.34.
  The campaign instance (the torus with its quotient metric) is a special case, so nothing is
  specialised. Nonemptiness is not assumed in the statement: the empty case is handled directly
  (`L = 0`, `φε = φ`, all bounds vacuous), and the nonempty case uses the prerequisite.
* "Continuous real `φ` on `X`" is `φ : X → ℝ` with `Continuous φ`. "Every `ε > 0`" is the
  hypothesis `0 < ε`. Both are the only hypotheses of the main statements.
* "There exist `L ≥ 0`" is `∃ L : ℝ, 0 ≤ L`, and "`L`-Lipschitz" is `LipschitzWith L.toNNReal`,
  which equals `L` as a real constant because `L ≥ 0`. The function `φε` is only required to be
  `L`-Lipschitz; continuity of `φε` follows from that and is not assumed separately.
* "`‖φ - φε‖∞ ≤ ε`": the pointwise form `∀ x, |φ x - φε x| ≤ ε` is stated as the primary
  conclusion. On a compact space this is the same as the sup-norm bound. The `_sup` form states
  the norm bound literally in `C(X, ℝ)`, and is derived from the pointwise form through
  `ContinuousMap.norm_le`.
* The specification's "choose `δ`" is realised by uniform continuity of `φ` on the compact space,
  through `lip032_34_uniform_lipschitz_approximation_bound_exists`. The bound `M = ‖φ‖∞` used there
  is the sup norm of `φ` as an element of `C(X, ℝ)`.
* Choice: the approximating function is the explicit real infimum `infConv_LIP03233 φ L` of
  LIP032.33. The main statements are existential, so no minimizing point is carried as part of an
  exported function.
* This unit does not use any LIP031 output, any flow, or any conditional hypothesis. The
  conditional branch of LIP032 is not invoked and no hypothesis of it is added.
-/

namespace DGPS.Frontier.LIP032

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Helper: the pointwise approximation on a nonempty compact metric space. The witness is the
real infimum of LIP032.33 at the constant `L = (2 * ‖φ‖∞ + ε) / δ`, where `δ` comes from uniform
continuity of `φ` (LIP032.34). -/
theorem pointwise_nonempty_LIP03207 [Nonempty X] {φ : X → ℝ} (hφ : Continuous φ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ φε : X → ℝ,
      LipschitzWith L.toNNReal φε ∧ ∀ x, |φ x - φε x| ≤ ε := by
  obtain ⟨δ, hδ, -, -, -, hab⟩ :=
    lip032_34_uniform_lipschitz_approximation_bound_exists hφ hε
  have hL : 0 ≤ (2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ := by positivity
  refine ⟨_, hL, _, (lip032_33_compact_minimum_produces_lipschitz_function hφ hL).2.2, fun x => ?_⟩
  rw [abs_sub_comm]
  exact hab x

/-- Lipschitz approximation of continuous tests: for a continuous real `φ` on a compact metric
space and `ε > 0`, there are `L ≥ 0` and an `L`-Lipschitz real `φε` with `‖φ - φε‖∞ ≤ ε`, stated
pointwise. -/
theorem lip032_07_lipschitz_approximation_continuous_tests {φ : X → ℝ} (hφ : Continuous φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ φε : X → ℝ,
      LipschitzWith L.toNNReal φε ∧ ∀ x, |φ x - φε x| ≤ ε := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨0, le_rfl, φ, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  · exact pointwise_nonempty_LIP03207 hφ hε

/-- Lipschitz approximation of continuous tests, sup-norm form in `C(X, ℝ)`: for a continuous real
`φ` on a compact metric space and `ε > 0`, there are `L ≥ 0` and an `L`-Lipschitz continuous map
`ψ : X → ℝ` with `‖φ - ψ‖∞ ≤ ε`. -/
theorem lip032_07_lipschitz_approximation_continuous_tests_sup {φ : X → ℝ} (hφ : Continuous φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ ψ : C(X, ℝ),
      LipschitzWith L.toNNReal ⇑ψ ∧ ‖(⟨φ, hφ⟩ : C(X, ℝ)) - ψ‖ ≤ ε := by
  obtain ⟨L, hL, φε, hlip, hb⟩ := lip032_07_lipschitz_approximation_continuous_tests hφ hε
  refine ⟨L, hL, ⟨φε, hlip.continuous⟩, hlip, ?_⟩
  refine (ContinuousMap.norm_le _ hε.le).mpr fun x => ?_
  show ‖φ x - φε x‖ ≤ ε
  rw [Real.norm_eq_abs]
  exact hb x

end DGPS.Frontier.LIP032
