import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData

/-!
# The angular rate parameter along the retained ordinary branches

Continuity of the same three rate coordinates gives one interval on which the
coefficient in the weighted root Hessian lies between zero and three halves.
-/

open Filter Topology
open scoped ContDiff

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The angular coefficient in the actual root Hessian is bounded on one common
interval for the SAME three branches. No form inequality is a premise. -/
theorem ordinaryRoot_angular_parameter_bounds (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, |h| < δ → ∀ j : Fin 3,
      0 ≤ 1 + h ^ 2 * D.Z j h 2 ∧ 1 + h ^ 2 * D.Z j h 2 ≤ 3 / 2 := by
  have hcont : ∀ j : Fin 3, ContinuousAt (fun h : ℝ => 1 + h ^ 2 * D.Z j h 2) 0 := by
    intro j
    have hz : ContinuousAt (D.Z j) 0 :=
      (D.smoothZ j).continuousOn.continuousAt
        (Ioo_mem_nhds (by linarith [D.radius_pos]) D.radius_pos)
    exact continuousAt_const.add ((continuousAt_id.pow 2).mul
      ((continuous_apply 2).continuousAt.comp hz))
  have hev : ∀ j : Fin 3, ∀ᶠ h in 𝓝 (0 : ℝ),
      1 + h ^ 2 * D.Z j h 2 ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2) := by
    intro j
    apply (hcont j).eventually
    exact isOpen_Ioo.mem_nhds (by norm_num)
  have hall : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ j : Fin 3,
      1 + h ^ 2 * D.Z j h 2 ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2) :=
    Filter.eventually_all.2 hev
  obtain ⟨ε, hε, hεall⟩ := Metric.eventually_nhds_iff.1 hall
  refine ⟨min ε D.radius, lt_min hε D.radius_pos, min_le_right _ _, fun h hh j => ?_⟩
  have hj := hεall (by rw [Real.dist_eq, sub_zero]; exact hh.trans_le (min_le_left _ _)) j
  constructor <;> linarith [hj.1, hj.2]

end DGPS.Examples.ThreeSpeciesCircle
