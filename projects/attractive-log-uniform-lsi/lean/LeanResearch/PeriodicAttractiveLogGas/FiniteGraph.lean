import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The finite reversible ground-state identity

This is the algebraic identity in `eq:occupation-ground-state` of the supplied
manuscript. The state space and the positive test function are arbitrary; no
occupation-specific drift estimate is asserted here. Both the energy and the
remainder use one half of the sum over directed edges. The measure weights need
not have mass one.
-/

noncomputable section

open scoped BigOperators

namespace PeriodicAttractiveLogGas.FiniteGraph

variable {State : Type*} [Fintype State]

/-- The finite-state jump generator, with zero rates encoding suppressed moves. -/
def generator (r : State → State → ℝ) (F : State → ℝ) (x : State) : ℝ :=
  ∑ y, r x y * (F y - F x)

/-- The energy is half the weighted sum over all directed edges. -/
def energy (μ : State → ℝ) (r : State → State → ℝ) (F : State → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, ∑ y, μ x * r x y * (F y - F x) ^ 2

/-- The ground-state potential `-L V / V`; the results below assume `V > 0`. -/
def groundStatePotential (r : State → State → ℝ) (V : State → ℝ) (x : State) : ℝ :=
  -generator r V x / V x

theorem groundStatePotential_eq_sum
    (r : State → State → ℝ) (V : State → ℝ) (hV : ∀ x, 0 < V x) (x : State) :
    groundStatePotential r V x = ∑ y, r x y * (1 - V y / V x) := by
  unfold groundStatePotential
  apply (div_eq_iff (ne_of_gt (hV x))).2
  unfold generator
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  field_simp [ne_of_gt (hV x)]
  ring

/-- Detailed balance gives the exact identity for every real observable.
Nonnegativity is only needed for the subsequent coercivity inequality. -/
theorem groundState_identity
    (μ : State → ℝ) (r : State → State → ℝ)
    (hbalance : ∀ x y, μ x * r x y = μ y * r y x)
    (V : State → ℝ) (hV : ∀ x, 0 < V x) (F : State → ℝ) :
    energy μ r F - ∑ x, μ x * (F x) ^ 2 * groundStatePotential r V x =
      (1 / 2 : ℝ) * ∑ x, ∑ y,
        μ x * r x y * V x * V y * (F x / V x - F y / V y) ^ 2 := by
  have hpot :
      (∑ x, μ x * (F x) ^ 2 * groundStatePotential r V x) =
        ∑ x, ∑ y, μ x * r x y * (F x) ^ 2 * (1 - V y / V x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [groundStatePotential_eq_sum r V hV x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hswap :
      (∑ x, ∑ y, μ x * r x y * (F y) ^ 2 * (1 - V x / V y)) =
        ∑ x, ∑ y, μ x * r x y * (F x) ^ 2 * (1 - V y / V x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hbalance y x]
  calc
    energy μ r F - ∑ x, μ x * (F x) ^ 2 * groundStatePotential r V x =
        (1 / 2 : ℝ) * ∑ x, ∑ y,
          (μ x * r x y * (F y - F x) ^ 2
            - μ x * r x y * (F x) ^ 2 * (1 - V y / V x)
            - μ x * r x y * (F y) ^ 2 * (1 - V x / V y)) := by
      simp only [Finset.sum_sub_distrib]
      rw [energy, hpot, hswap]
      ring
    _ = _ := by
      apply congrArg (fun s : ℝ ↦ (1 / 2 : ℝ) * s)
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      field_simp [ne_of_gt (hV x), ne_of_gt (hV y)]
      ring

/-- The potential term is controlled by the energy for nonnegative reversible
weights and rates. No normalization or centering of the observable is required. -/
theorem groundState_coercivity
    (μ : State → ℝ) (r : State → State → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hr : ∀ x y, 0 ≤ r x y)
    (hbalance : ∀ x y, μ x * r x y = μ y * r y x)
    (V : State → ℝ) (hV : ∀ x, 0 < V x) (F : State → ℝ) :
    (∑ x, μ x * (F x) ^ 2 * groundStatePotential r V x) ≤ energy μ r F := by
  apply sub_nonneg.mp
  rw [groundState_identity μ r hbalance V hV F]
  apply mul_nonneg (div_nonneg zero_le_one zero_le_two)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (hμ x) (hr x y))
        (le_of_lt (hV x)))
      (le_of_lt (hV y)))
    (sq_nonneg _)

end PeriodicAttractiveLogGas.FiniteGraph
