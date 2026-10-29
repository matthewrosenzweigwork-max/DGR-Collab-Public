import FullLabeledLSI.Examples.E01h2_UintPoly
import FullLabeledLSI.Examples.E01h3_Trig
import SharpSymmetricLSI.Paper.DensMeasure

/-!
# Lane D, Task C (E01g1): convolution of a smooth kernel with a finite measure is smooth
-/

open MeasureTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem continuous_lift1 : Continuous lift1 := by
  unfold lift1
  refine continuous_pi fun i => ?_
  exact (AddCircle.continuous_mk' (1 : ℝ))

/-- Derivative of `s ↦ ∫ g (lift1 s - y) dν(y)`. -/
theorem hasDerivAt_conv {g : Torus 1 → ℝ} (hg : IsSmoothT g) (ν : Measure (Torus 1))
    [IsFiniteMeasure ν] (t : ℝ) :
    HasDerivAt (fun s => ∫ y, g (lift1 s - y) ∂ν) (∫ y, dT g (lift1 t - y) ∂ν) t := by
  have hg1 : ContDiff ℝ ∞ (fun s : ℝ => g (lift1 s)) := isSmoothT_iff_lift1.1 hg
  have hgd : ContDiff ℝ ∞ (deriv fun s : ℝ => g (lift1 s)) := (contDiff_infty_iff_deriv.1 hg1).2
  have hc0 : Continuous g := continuous_of_smooth hg
  have hc1 : Continuous (dT g) := continuous_of_smooth (isSmoothT_dT hg)
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hc1.continuousOn
  have hy0 : ∀ s : ℝ, Continuous (fun y : Torus 1 => g (lift1 s - y)) := fun s =>
    hc0.comp (continuous_sub_left (lift1 s))
  have hy1 : ∀ s : ℝ, Continuous (fun y : Torus 1 => dT g (lift1 s - y)) := fun s =>
    hc1.comp (continuous_sub_left (lift1 s))
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun s y => g (lift1 s - y)) (F' := fun s y => dT g (lift1 s - y)) (x₀ := t)
    (bound := fun _ => M) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun s => (hy0 s).aestronglyMeasurable)
    (integrable_of_cont (hy0 t) ν)
    (hy1 t).aestronglyMeasurable
    (Eventually.of_forall fun y s _ => by simpa using hM (lift1 s - y) (Set.mem_univ _))
    (integrable_const M)
    (Eventually.of_forall fun y s _ => by
      obtain ⟨a, rfl⟩ := exists_lift1 y
      have e : (fun s' : ℝ => g (lift1 s' - lift1 a)) = fun s' => g (lift1 (s' - a)) := by
        funext s'; rw [lift1_sub]
      rw [e]
      have h1 : HasDerivAt (fun s' : ℝ => g (lift1 s')) (deriv (fun s' : ℝ => g (lift1 s')) (s - a)) (s - a) :=
        ((hg1.differentiable (by simp)) (s - a)).hasDerivAt
      have h2 := h1.comp_sub_const s a
      have e2 : dT g (lift1 s - lift1 a) = deriv (fun s' : ℝ => g (lift1 s')) (s - a) := by
        rw [← lift1_sub, dT_lift1]
      rw [e2]; exact h2)
  exact this.2

theorem contDiff_conv_nat (n : ℕ) : ∀ {g : Torus 1 → ℝ}, IsSmoothT g → ∀ (ν : Measure (Torus 1)) [IsFiniteMeasure ν],
    ContDiff ℝ n (fun s : ℝ => ∫ y, g (lift1 s - y) ∂ν) := by
  induction n with
  | zero =>
    intro g hg ν _
    have hc0 : Continuous g := continuous_of_smooth hg
    exact contDiff_zero.2 ((continuous_conv hc0 ν).comp continuous_lift1)
  | succ n ih =>
    intro g hg ν _
    have hn : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hn, contDiff_succ_iff_deriv]
    refine ⟨fun s => (hasDerivAt_conv hg ν s).differentiableAt, by simp, ?_⟩
    have : deriv (fun s : ℝ => ∫ y, g (lift1 s - y) ∂ν) = fun s => ∫ y, dT g (lift1 s - y) ∂ν :=
      funext fun s => (hasDerivAt_conv hg ν s).deriv
    rw [this]
    exact ih (isSmoothT_dT hg) ν

theorem isSmoothT_conv {g : Torus 1 → ℝ} (hg : IsSmoothT g) (ν : Measure (Torus 1))
    [IsFiniteMeasure ν] : IsSmoothT (fun x => ∫ y, g (x - y) ∂ν) := by
  rw [isSmoothT_iff_lift1]
  exact contDiff_infty.2 fun n => contDiff_conv_nat n hg ν

theorem dT_conv {g : Torus 1 → ℝ} (hg : IsSmoothT g) (ν : Measure (Torus 1)) [IsFiniteMeasure ν]
    (x : Torus 1) : dT (fun x => ∫ y, g (x - y) ∂ν) x = ∫ y, dT g (x - y) ∂ν := by
  rw [dT_apply]
  have := (hasDerivAt_conv hg ν (rep x)).deriv
  simp only [lift1_rep] at this ⊢
  exact this

end SharpLSI.FL.Ex.LaneD
