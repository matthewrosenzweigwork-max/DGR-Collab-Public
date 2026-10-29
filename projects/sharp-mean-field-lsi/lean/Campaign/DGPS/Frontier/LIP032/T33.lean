import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# LIP032.33: Compact minimum produces a Lipschitz function

Task id and title: LIP032.33, "Compact minimum produces a Lipschitz function" (node LIP032,
contractibility of the minimizer set; leaf formalization, no positive-rate or flow hypothesis is
used, so the defect FD-001 of the isolated frozen LIP032 sentence is not touched by this unit).

## Provides
* `DGPS.Frontier.LIP032.infConv_LIP03233` : the function
  `a_L(x) = ⨅ y, φ y + L * dist x y` (the real infimum, as a definition).
* `DGPS.Frontier.LIP032.lip032_33_compact_minimum_produces_lipschitz_function` : for a continuous
  real `φ` on a nonempty compact metric space and `L ≥ 0`, the infimum defining `a_L x` is
  attained at some point for every `x`, `a_L x ≤ φ x`, and `a_L` is `L`-Lipschitz
  (`LipschitzWith L.toNNReal`).
* `DGPS.Frontier.LIP032.lip032_33_compact_minimum_produces_lipschitz_function_dist` : the same
  Lipschitz estimate in the form `|a_L x - a_L x'| ≤ L * dist x x'`.

## R5 notes
* Ambient space: a general `MetricSpace X` with `CompactSpace X` and `Nonempty X`. The
  specification says "nonempty compact `X`"; the campaign instance (the torus with its quotient
  metric) is a special case, so nothing is specialised. The metric is `dist`.
* `a_L` is defined as a real infimum `⨅ y, ...` (junk value excluded because the family is
  bounded below and nonempty); the statement "the minimum exists" is the attainment clause
  `∃ y, a_L x = φ y + L * dist x y`, together with the minimality property
  `∀ y', φ y + L * dist x y ≤ φ y' + L * dist x y'` of that point. No continuous selection of the
  minimizing point is used or claimed.
* `L : ℝ` with `0 ≤ L`; the Lipschitz constant is `Real.toNNReal L`, which equals `L` since
  `L ≥ 0`.
-/

namespace DGPS.Frontier.LIP032

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

/-- The function `a_L(x) = min_y (φ y + L * dist x y)`, written as a real infimum. -/
noncomputable def infConv_LIP03233 (φ : X → ℝ) (L : ℝ) (x : X) : ℝ :=
  ⨅ y, (φ y + L * dist x y)

omit [CompactSpace X] [Nonempty X] in
/-- The function inside the infimum is continuous in `y`. -/
theorem continuous_aux_LIP03233 {φ : X → ℝ} (hφ : Continuous φ) (L : ℝ) (x : X) :
    Continuous (fun y => φ y + L * dist x y) :=
  hφ.add (continuous_const.mul (continuous_const.dist continuous_id))

/-- Attainment of the minimum at a fixed point, and equality with the infimum. -/
theorem exists_min_LIP03233 {φ : X → ℝ} (hφ : Continuous φ) (L : ℝ) (x : X) :
    ∃ y, infConv_LIP03233 φ L x = φ y + L * dist x y ∧
      ∀ y', φ y + L * dist x y ≤ φ y' + L * dist x y' := by
  obtain ⟨y, -, hy⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty (continuous_aux_LIP03233 hφ L x).continuousOn
  have hy' : ∀ y', φ y + L * dist x y ≤ φ y' + L * dist x y' := fun y' =>
    hy (Set.mem_univ y')
  refine ⟨y, le_antisymm ?_ (le_ciInf hy'), hy'⟩
  exact ciInf_le ⟨φ y + L * dist x y, by rintro _ ⟨y', rfl⟩; exact hy' y'⟩ y

/-- One-sided Lipschitz estimate: `a_L x' ≤ a_L x + L * dist x x'`. -/
theorem le_add_LIP03233 {φ : X → ℝ} (hφ : Continuous φ) {L : ℝ} (hL : 0 ≤ L) (x x' : X) :
    infConv_LIP03233 φ L x' ≤ infConv_LIP03233 φ L x + L * dist x x' := by
  obtain ⟨y, hxy, -⟩ := exists_min_LIP03233 hφ L x
  obtain ⟨y', hx'y', hmin⟩ := exists_min_LIP03233 hφ L x'
  have h1 : φ y' + L * dist x' y' ≤ φ y + L * dist x' y := hmin y
  have h2 : dist x' y ≤ dist x x' + dist x y := by
    calc dist x' y ≤ dist x' x + dist x y := dist_triangle _ _ _
      _ = dist x x' + dist x y := by rw [dist_comm x' x]
  have h3 : L * dist x' y ≤ L * (dist x x' + dist x y) := mul_le_mul_of_nonneg_left h2 hL
  rw [hx'y', hxy]
  nlinarith

/-- The absolute-value form of the Lipschitz estimate. -/
theorem lip032_33_compact_minimum_produces_lipschitz_function_dist
    {φ : X → ℝ} (hφ : Continuous φ) {L : ℝ} (hL : 0 ≤ L) (x x' : X) :
    |infConv_LIP03233 φ L x - infConv_LIP03233 φ L x'| ≤ L * dist x x' := by
  have h1 := le_add_LIP03233 hφ hL x x'
  have h2 := le_add_LIP03233 hφ hL x' x
  rw [dist_comm x' x] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Compact minimum produces a Lipschitz function: for `φ` continuous on a nonempty compact
metric space and `L ≥ 0`, the minimum defining `a_L x` is attained, `a_L x ≤ φ x`, and `a_L` is
`L`-Lipschitz. -/
theorem lip032_33_compact_minimum_produces_lipschitz_function
    {φ : X → ℝ} (hφ : Continuous φ) {L : ℝ} (hL : 0 ≤ L) :
    (∀ x, ∃ y, infConv_LIP03233 φ L x = φ y + L * dist x y ∧
        ∀ y', φ y + L * dist x y ≤ φ y' + L * dist x y') ∧
      (∀ x, infConv_LIP03233 φ L x ≤ φ x) ∧
      LipschitzWith L.toNNReal (infConv_LIP03233 φ L) := by
  refine ⟨fun x => exists_min_LIP03233 hφ L x, fun x => ?_, ?_⟩
  · obtain ⟨y, hxy, hmin⟩ := exists_min_LIP03233 hφ L x
    have := hmin x
    rw [hxy]
    simpa using this
  · refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have h := lip032_33_compact_minimum_produces_lipschitz_function_dist hφ hL x x'
    rw [Real.dist_eq, Real.coe_toNNReal L hL]
    exact h

end DGPS.Frontier.LIP032
