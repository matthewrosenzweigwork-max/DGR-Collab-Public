import LeanResearch.PeriodicAttractiveLogGas.GreenRegularity
import LeanResearch.PeriodicAttractiveLogGas.LogBounds
import LeanResearch.PeriodicAttractiveLogGas.QuadraticPotential
import LeanResearch.PeriodicAttractiveLogGas.TorusDistance
import Mathlib.Analysis.Normed.Group.Bounded

/-! Ordinary local derivative identities and quantitative local Green bounds.

The logarithmic expansion holds on a punctured open chart. Equality on a
neighborhood, rather than equality just at the evaluation point, identifies
the ordinary first and second Fréchet derivatives. Compactness bounds the
actual smooth remainder and its derivatives on the closed quarter ball.
-/

noncomputable section

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas

theorem closedBall_quarter_subset_centeredOpenBox :
    closedBall (0 : PlanarSpace) (1 / 4 : ℝ) ⊆
      euclideanOpenBox (centeredBoxAnchor 0) := by
  intro x hx
  apply mem_centeredOpenBox_of_norm_lt_half
  have hnorm := mem_closedBall_zero_iff.mp hx
  linarith

theorem contDiffOn_fderiv_smoothGreenLogRemainder :
    ContDiffOn ℝ ∞ (fderiv ℝ smoothGreenLogRemainder)
      (euclideanOpenBox (centeredBoxAnchor 0)) :=
  contDiffOn_smoothGreenLogRemainder.fderiv_of_isOpen
    (isOpen_euclideanOpenBox _) (by simp)

theorem contDiffOn_hessian_smoothGreenLogRemainder :
    ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ smoothGreenLogRemainder))
      (euclideanOpenBox (centeredBoxAnchor 0)) :=
  contDiffOn_fderiv_smoothGreenLogRemainder.fderiv_of_isOpen
    (isOpen_euclideanOpenBox _) (by simp)

theorem smoothGreenLift_eventuallyEq_local_expansion {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    smoothGreenLift =ᶠ[𝓝 x] (fun y ↦
      planarLogKernel y + planarGreenQuadratic y + smoothGreenLogRemainder y) := by
  filter_upwards [(isOpen_euclideanOpenBox _).mem_nhds hx,
    eventually_ne_nhds hne] with y hy hyne
  exact smoothGreenLift_local_expansion hy hyne

theorem fderiv_smoothGreenLift_local_split {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    fderiv ℝ smoothGreenLift x = fderiv ℝ planarLogKernel x +
      fderiv ℝ planarGreenQuadratic x + fderiv ℝ smoothGreenLogRemainder x := by
  have hL := (contDiffAt_planarLogKernel hne).differentiableAt (by simp)
  have hQ := contDiff_planarGreenQuadratic.differentiable (by simp) x
  have hH := (contDiffOn_smoothGreenLogRemainder.contDiffAt
    ((isOpen_euclideanOpenBox _).mem_nhds hx)).differentiableAt (by simp)
  rw [(smoothGreenLift_eventuallyEq_local_expansion hx hne).fderiv_eq]
  exact ((hL.hasFDerivAt.add hQ.hasFDerivAt).add hH.hasFDerivAt).fderiv

/-- The full first derivative, with the exact logarithmic and quadratic normalizations. -/
theorem fderiv_smoothGreenLift_local {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    fderiv ℝ smoothGreenLift x = -(‖x‖ ^ 2)⁻¹ • innerSL ℝ x +
      Real.pi • innerSL ℝ x + fderiv ℝ smoothGreenLogRemainder x := by
  rw [fderiv_smoothGreenLift_local_split hx hne,
    fderiv_planarLogKernel hne, fderiv_planarGreenQuadratic]

theorem fderiv_fderiv_smoothGreenLift_local_split {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    fderiv ℝ (fderiv ℝ smoothGreenLift) x =
      fderiv ℝ (fderiv ℝ planarLogKernel) x +
      fderiv ℝ (fderiv ℝ planarGreenQuadratic) x +
      fderiv ℝ (fderiv ℝ smoothGreenLogRemainder) x := by
  have heq : fderiv ℝ smoothGreenLift =ᶠ[𝓝 x] (fun y ↦
      fderiv ℝ planarLogKernel y + fderiv ℝ planarGreenQuadratic y +
        fderiv ℝ smoothGreenLogRemainder y) := by
    filter_upwards [(isOpen_euclideanOpenBox _).mem_nhds hx,
      eventually_ne_nhds hne] with y hy hyne
    exact fderiv_smoothGreenLift_local_split hy hyne
  have hL := ((contDiffAt_planarLogKernel hne).fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  have hQ : DifferentiableAt ℝ (fderiv ℝ planarGreenQuadratic) x :=
    (contDiff_planarGreenQuadratic.contDiffAt.fderiv_right
    (m := ∞) (by simp)).differentiableAt (by simp)
  have hH := (contDiffOn_fderiv_smoothGreenLogRemainder.contDiffAt
    ((isOpen_euclideanOpenBox _).mem_nhds hx)).differentiableAt (by simp)
  rw [heq.fderiv_eq]
  exact ((hL.hasFDerivAt.add hQ.hasFDerivAt).add hH.hasFDerivAt).fderiv

/-- The full ordinary Hessian evaluated on two arbitrary vectors. -/
theorem fderiv_fderiv_smoothGreenLift_local_apply {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0)
    (u v : PlanarSpace) :
    fderiv ℝ (fderiv ℝ smoothGreenLift) x u v =
      2 * (‖x‖ ^ 2)⁻¹ ^ 2 * inner ℝ x u * inner ℝ x v -
        (‖x‖ ^ 2)⁻¹ * inner ℝ u v + Real.pi * inner ℝ u v +
          fderiv ℝ (fderiv ℝ smoothGreenLogRemainder) x u v := by
  simp only [fderiv_fderiv_smoothGreenLift_local_split hx hne,
    add_apply, fderiv_fderiv_planarLogKernel_apply hne,
    fderiv_fderiv_planarGreenQuadratic, smul_apply, smul_eq_mul]
  rfl

/-- A single positive finite constant bounds the smooth remainder and its first
two ordinary derivatives on a compact set strictly inside its smooth domain. -/
theorem exists_smoothGreenLogRemainder_quarter_bounds :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ closedBall (0 : PlanarSpace) (1 / 4 : ℝ),
      |smoothGreenLogRemainder x| ≤ M ∧
      ‖fderiv ℝ smoothGreenLogRemainder x‖ ≤ M ∧
      ‖fderiv ℝ (fderiv ℝ smoothGreenLogRemainder) x‖ ≤ M := by
  have hc : IsCompact (closedBall (0 : PlanarSpace) (1 / 4 : ℝ)) := isCompact_closedBall _ _
  obtain ⟨C0, h0⟩ := hc.exists_bound_of_continuousOn (f := smoothGreenLogRemainder)
    (contDiffOn_smoothGreenLogRemainder.continuousOn.mono
      closedBall_quarter_subset_centeredOpenBox)
  obtain ⟨C1, h1⟩ := hc.exists_bound_of_continuousOn (f := fderiv ℝ smoothGreenLogRemainder)
    (contDiffOn_fderiv_smoothGreenLogRemainder.continuousOn.mono
      closedBall_quarter_subset_centeredOpenBox)
  obtain ⟨C2, h2⟩ := hc.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ smoothGreenLogRemainder))
    (contDiffOn_hessian_smoothGreenLogRemainder.continuousOn.mono
      closedBall_quarter_subset_centeredOpenBox)
  refine ⟨|C0| + |C1| + |C2| + 1, by positivity, ?_⟩
  intro x hx
  have h0x : |smoothGreenLogRemainder x| ≤ C0 := by
    simpa only [Real.norm_eq_abs] using h0 x hx
  refine ⟨h0x.trans ?_, (h1 x hx).trans ?_, (h2 x hx).trans ?_⟩ <;>
    linarith [le_abs_self C0, le_abs_self C1, le_abs_self C2,
      abs_nonneg C0, abs_nonneg C1, abs_nonneg C2]

theorem quadratic_jet_bounds {x : PlanarSpace} (hx : ‖x‖ ≤ 1) :
    ‖planarGreenQuadratic x‖ ≤ Real.pi ∧
      ‖fderiv ℝ planarGreenQuadratic x‖ ≤ Real.pi ∧
      ‖fderiv ℝ (fderiv ℝ planarGreenQuadratic) x‖ ≤ Real.pi := by
  have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hQ : 0 ≤ planarGreenQuadratic x := by
    unfold planarGreenQuadratic
    positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg hQ, planarGreenQuadratic]
    have h := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ Real.pi / 2)
    nlinarith [Real.pi_pos]
  · rw [fderiv_planarGreenQuadratic, norm_smul, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, innerSL_apply_norm]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx Real.pi_pos.le
  · apply ContinuousLinearMap.opNorm_le_bound _ Real.pi_pos.le
    intro u
    rw [fderiv_fderiv_planarGreenQuadratic, smul_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, innerSL_apply_norm]

/-- Local logarithmic, gradient and Hessian bounds for the actual smooth Green
lift. The norms on the derivatives are the continuous-linear-map operator norms. -/
theorem exists_smoothGreenLift_quarter_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ closedBall (0 : PlanarSpace) (1 / 4 : ℝ), x ≠ 0 →
      |smoothGreenLift x + Real.log ‖x‖| ≤ C ∧
      ‖fderiv ℝ smoothGreenLift x‖ ≤ C / ‖x‖ ∧
      ‖fderiv ℝ (fderiv ℝ smoothGreenLift) x‖ ≤ C / (‖x‖ ^ 2) := by
  obtain ⟨M, hM, hb⟩ := exists_smoothGreenLogRemainder_quarter_bounds
  let C : ℝ := 3 + Real.pi + M
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x hx hne
  have hxbox := closedBall_quarter_subset_centeredOpenBox hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hne
  have hr1 : ‖x‖ ≤ 1 := by
    have h := mem_closedBall_zero_iff.mp hx
    linarith
  have hr2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith
  have hi1 : 1 ≤ ‖x‖⁻¹ := (one_le_inv₀ hr).2 hr1
  have hi2 : 1 ≤ (‖x‖ ^ 2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hr)).2 hr2
  obtain ⟨hH0, hH1, hH2⟩ := hb x hx
  obtain ⟨hQ0, hQ1, hQ2⟩ := quadratic_jet_bounds hr1
  have hP : 0 ≤ Real.pi + M := add_nonneg Real.pi_pos.le hM.le
  have hvalue : smoothGreenLift x + Real.log ‖x‖ =
      planarGreenQuadratic x + smoothGreenLogRemainder x := by
    rw [smoothGreenLift_local_expansion hxbox hne, planarLogKernel]
    ring
  have hd : ‖fderiv ℝ smoothGreenLift x‖ ≤ ‖x‖⁻¹ + Real.pi + M := by
    rw [fderiv_smoothGreenLift_local_split hxbox hne]
    calc
      ‖fderiv ℝ planarLogKernel x + fderiv ℝ planarGreenQuadratic x +
          fderiv ℝ smoothGreenLogRemainder x‖ ≤
          ‖fderiv ℝ planarLogKernel x + fderiv ℝ planarGreenQuadratic x‖ +
            ‖fderiv ℝ smoothGreenLogRemainder x‖ := norm_add_le _ _
      _ ≤ (‖fderiv ℝ planarLogKernel x‖ + ‖fderiv ℝ planarGreenQuadratic x‖) +
          ‖fderiv ℝ smoothGreenLogRemainder x‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖x‖⁻¹ + Real.pi + M := by
        rw [norm_fderiv_planarLogKernel hne]
        exact add_le_add (add_le_add le_rfl hQ1) hH1
  have hdd : ‖fderiv ℝ (fderiv ℝ smoothGreenLift) x‖ ≤
      3 * (‖x‖ ^ 2)⁻¹ + Real.pi + M := by
    rw [fderiv_fderiv_smoothGreenLift_local_split hxbox hne]
    calc
      ‖fderiv ℝ (fderiv ℝ planarLogKernel) x +
          fderiv ℝ (fderiv ℝ planarGreenQuadratic) x +
          fderiv ℝ (fderiv ℝ smoothGreenLogRemainder) x‖ ≤
          ‖fderiv ℝ (fderiv ℝ planarLogKernel) x +
            fderiv ℝ (fderiv ℝ planarGreenQuadratic) x‖ +
          ‖fderiv ℝ (fderiv ℝ smoothGreenLogRemainder) x‖ :=
        norm_add_le (fderiv ℝ (fderiv ℝ planarLogKernel) x +
          fderiv ℝ (fderiv ℝ planarGreenQuadratic) x)
          (fderiv ℝ (fderiv ℝ smoothGreenLogRemainder) x)
      _ ≤ (‖fderiv ℝ (fderiv ℝ planarLogKernel) x‖ +
          ‖fderiv ℝ (fderiv ℝ planarGreenQuadratic) x‖) +
          ‖fderiv ℝ (fderiv ℝ smoothGreenLogRemainder) x‖ :=
        add_le_add (norm_add_le (fderiv ℝ (fderiv ℝ planarLogKernel) x)
          (fderiv ℝ (fderiv ℝ planarGreenQuadratic) x)) le_rfl
      _ ≤ 3 * (‖x‖ ^ 2)⁻¹ + Real.pi + M :=
        add_le_add (add_le_add (norm_hessian_planarLogKernel_le hne) hQ2) hH2
  refine ⟨?_, ?_, ?_⟩
  · rw [hvalue]
    have hQabs : |planarGreenQuadratic x| ≤ Real.pi := by
      simpa only [Real.norm_eq_abs] using hQ0
    calc
      |planarGreenQuadratic x + smoothGreenLogRemainder x| ≤
          |planarGreenQuadratic x| + |smoothGreenLogRemainder x| := abs_add_le _ _
      _ ≤ Real.pi + M := add_le_add hQabs hH0
      _ ≤ C := by dsimp [C]; linarith
  · apply hd.trans
    rw [div_eq_mul_inv]
    have h := mul_le_mul_of_nonneg_left hi1 hP
    dsimp [C]
    nlinarith
  · apply hdd.trans
    rw [div_eq_mul_inv]
    have h := mul_le_mul_of_nonneg_left hi2 hP
    dsimp [C]
    nlinarith

end PeriodicAttractiveLogGas
