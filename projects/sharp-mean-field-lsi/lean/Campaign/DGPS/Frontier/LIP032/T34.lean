import DGPS.Frontier.LIP032.T33
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# LIP032.34: Uniform Lipschitz approximation bound

Task id and title: LIP032.34, "Uniform Lipschitz approximation bound" (node LIP032, contractibility
of the minimizer set; leaf formalization). No positive-rate or flow hypothesis is used here, so the
defect FD-001 of the isolated frozen LIP032 sentence is not touched by this unit.

## Provides
* `DGPS.Frontier.LIP032.lip032_34_uniform_lipschitz_approximation_bound` : for `φ` continuous on a
  nonempty compact metric space, `ε`, a radius `δ > 0` with
  `dist x y < δ → |φ x - φ y| < ε`, and a bound `M` with `|φ x| ≤ M`, the function `a_L` of
  LIP032.33 with `L = (2 * M + ε) / δ` satisfies `φ x - ε ≤ a_L x ≤ φ x` and
  `|a_L x - φ x| ≤ ε` for every `x`.
* `DGPS.Frontier.LIP032.lip032_34_uniform_lipschitz_approximation_bound_sup` : the same data with
  `M` the sup norm of `φ`; `a_L` is `L`-Lipschitz (hence continuous) and the sup-norm distance
  between `a_L` and `φ` in `C(X, ℝ)` is at most `ε`.
* `DGPS.Frontier.LIP032.lip032_34_uniform_lipschitz_approximation_bound_exists` : existence form
  with `δ` produced from uniform continuity of `φ` on the compact space, for every `ε > 0`.

## R5 notes
* Ambient space: a general `MetricSpace X` with `CompactSpace X` and `Nonempty X`, as in
  LIP032.33; the campaign torus is a special case, so nothing is specialised.
* The specification says "choose `δ` such that ..." and puts `M = ‖φ‖∞`. The main theorem takes
  `δ` as a parameter with `0 < δ` and the strict closeness property, and `M` as any real bound with
  `|φ x| ≤ M`; this is slightly more general than `M = ‖φ‖∞`. The hypothesis `0 ≤ ε` is not
  assumed: it follows from the closeness property at `x = y` (nonemptiness of `X`). The `_sup`
  form instantiates `M` with the sup norm of `φ` as an element of `C(X, ℝ)`, and the `_exists`
  form supplies `δ` from compact uniform continuity, for `ε > 0`.
* `a_L` is `infConv_LIP03233 φ L` from LIP032.33, a real infimum; the lower bound is proved
  against every candidate `φ y + L * dist x y`, which then bounds the infimum, so no choice of
  minimizing point is used. The upper bound is taken from LIP032.33.
* The uniform norm statement is given both pointwise (`|a_L x - φ x| ≤ ε` for all `x`) and as the
  norm bound in `C(X, ℝ)`, where `a_L` is made a continuous map using its Lipschitz property.
-/

namespace DGPS.Frontier.LIP032

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

omit [CompactSpace X] in
/-- Nonnegativity of `ε` and `M` from the hypotheses (nonempty space). -/
theorem eps_M_nonneg_LIP03234 {φ : X → ℝ} {ε δ M : ℝ} (hδ : 0 < δ)
    (hcont : ∀ x y, dist x y < δ → |φ x - φ y| < ε) (hM : ∀ x, |φ x| ≤ M) :
    0 ≤ ε ∧ 0 ≤ M := by
  obtain ⟨x⟩ := ‹Nonempty X›
  refine ⟨?_, le_trans (abs_nonneg _) (hM x)⟩
  have := hcont x x (by simpa using hδ)
  simp only [sub_self, abs_zero] at this
  exact this.le

omit [CompactSpace X] in
/-- Each candidate in the minimum is at least `φ x - ε`. -/
theorem candidate_ge_LIP03234 {φ : X → ℝ} {ε δ M : ℝ} (hδ : 0 < δ)
    (hcont : ∀ x y, dist x y < δ → |φ x - φ y| < ε) (hM : ∀ x, |φ x| ≤ M) (x y : X) :
    φ x - ε ≤ φ y + (2 * M + ε) / δ * dist x y := by
  obtain ⟨hε, hM0⟩ := eps_M_nonneg_LIP03234 hδ hcont hM
  have hd : 0 ≤ dist x y := dist_nonneg
  have h0 : 0 ≤ (2 * M + ε) / δ := by positivity
  by_cases h : dist x y < δ
  · have := abs_lt.mp (hcont x y h)
    have hL : 0 ≤ (2 * M + ε) / δ * dist x y := mul_nonneg h0 hd
    linarith [this.2]
  · have hδd : δ ≤ dist x y := not_lt.mp h
    have hLδ : 2 * M + ε ≤ (2 * M + ε) / δ * dist x y := by
      calc 2 * M + ε = (2 * M + ε) / δ * δ := by field_simp
        _ ≤ (2 * M + ε) / δ * dist x y := mul_le_mul_of_nonneg_left hδd h0
    have h1 := abs_le.mp (hM x)
    have h2 := abs_le.mp (hM y)
    linarith [h1.2, h2.1]

/-- Uniform Lipschitz approximation bound: with `L = (2 * M + ε) / δ`, the function `a_L` of
LIP032.33 satisfies `φ - ε ≤ a_L ≤ φ` and `|a_L - φ| ≤ ε` pointwise. -/
theorem lip032_34_uniform_lipschitz_approximation_bound
    {φ : X → ℝ} (hφ : Continuous φ) {ε δ M : ℝ} (hδ : 0 < δ)
    (hcont : ∀ x y, dist x y < δ → |φ x - φ y| < ε) (hM : ∀ x, |φ x| ≤ M) :
    (∀ x, φ x - ε ≤ infConv_LIP03233 φ ((2 * M + ε) / δ) x) ∧
      (∀ x, infConv_LIP03233 φ ((2 * M + ε) / δ) x ≤ φ x) ∧
      (∀ x, |infConv_LIP03233 φ ((2 * M + ε) / δ) x - φ x| ≤ ε) := by
  obtain ⟨hε, hM0⟩ := eps_M_nonneg_LIP03234 hδ hcont hM
  have hL : 0 ≤ (2 * M + ε) / δ := by positivity
  have hlow : ∀ x, φ x - ε ≤ infConv_LIP03233 φ ((2 * M + ε) / δ) x := fun x =>
    le_ciInf fun y => candidate_ge_LIP03234 hδ hcont hM x y
  have hup : ∀ x, infConv_LIP03233 φ ((2 * M + ε) / δ) x ≤ φ x := fun x =>
    (lip032_33_compact_minimum_produces_lipschitz_function hφ hL).2.1 x
  refine ⟨hlow, hup, fun x => ?_⟩
  rw [abs_le]
  constructor <;> linarith [hlow x, hup x]

/-- The same bound with `M` the sup norm of `φ` in `C(X, ℝ)`: `a_L` is `L`-Lipschitz with
`L = (2 * ‖φ‖ + ε) / δ`, and its sup-norm distance to `φ` is at most `ε`. -/
theorem lip032_34_uniform_lipschitz_approximation_bound_sup
    {φ : X → ℝ} (hφ : Continuous φ) {ε δ : ℝ} (hδ : 0 < δ)
    (hcont : ∀ x y, dist x y < δ → |φ x - φ y| < ε) :
    ∃ ha : Continuous (infConv_LIP03233 φ ((2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ)),
      LipschitzWith ((2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ).toNNReal
          (infConv_LIP03233 φ ((2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ)) ∧
        ‖(⟨_, ha⟩ : C(X, ℝ)) - ⟨φ, hφ⟩‖ ≤ ε := by
  have hM : ∀ x, |φ x| ≤ ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ := fun x => by
    simpa using ContinuousMap.norm_coe_le_norm (⟨φ, hφ⟩ : C(X, ℝ)) x
  obtain ⟨hε, hM0⟩ := eps_M_nonneg_LIP03234 hδ hcont hM
  have hL : 0 ≤ (2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ := by positivity
  have hlip := (lip032_33_compact_minimum_produces_lipschitz_function hφ hL).2.2
  obtain ⟨-, -, hab⟩ := lip032_34_uniform_lipschitz_approximation_bound hφ hδ hcont hM
  refine ⟨hlip.continuous, hlip, ?_⟩
  refine (ContinuousMap.norm_le _ hε).mpr fun x => ?_
  simpa using hab x

/-- Existence form: every continuous `φ` on a nonempty compact metric space and every `ε > 0`
have some `δ > 0` with the strict closeness property, and then the approximation bound holds with
`M = ‖φ‖∞`. -/
theorem lip032_34_uniform_lipschitz_approximation_bound_exists
    {φ : X → ℝ} (hφ : Continuous φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ x y, dist x y < δ → |φ x - φ y| < ε) ∧
      (∀ x, φ x - ε ≤ infConv_LIP03233 φ ((2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ) x) ∧
      (∀ x, infConv_LIP03233 φ ((2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ) x ≤ φ x) ∧
      (∀ x, |infConv_LIP03233 φ ((2 * ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ + ε) / δ) x - φ x| ≤ ε) := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hφ) ε hε
  have hcont : ∀ x y, dist x y < δ → |φ x - φ y| < ε := fun x y hxy => by
    simpa [Real.dist_eq] using h hxy
  have hM : ∀ x, |φ x| ≤ ‖(⟨φ, hφ⟩ : C(X, ℝ))‖ := fun x => by
    simpa using ContinuousMap.norm_coe_le_norm (⟨φ, hφ⟩ : C(X, ℝ)) x
  exact ⟨δ, hδ, hcont, lip032_34_uniform_lipschitz_approximation_bound hφ hδ hcont hM⟩

end DGPS.Frontier.LIP032
