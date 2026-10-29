import SharpSymmetricLSI.Paper.AppAWeak2

/-!
# The weak formulation (3): heat-smoothed Lipschitz test functions

A smooth flat-`1`-Lipschitz function has `|∇φ| ≤ 1` (`sum_dpart_sq_le_one`), and the heat flow
preserves flat-`1`-Lipschitz functions (`flatLipschitz_heatT`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem norm_coe_unitAddCircle_le (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [UnitAddCircle.norm_eq]; simpa using round_le x 0

theorem flatDist_liftT_le (a b : ι → ℝ) :
    flatDist (liftT a) (liftT b) ≤ Real.sqrt (∑ k, (a k - b k) ^ 2) := by
  unfold flatDist
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  have e : (liftT a) k - (liftT b) k = ((a k - b k : ℝ) : UnitAddCircle) := by
    simp [liftT]
  rw [e, ← sq_abs (a k - b k)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_coe_unitAddCircle_le _) 2

theorem flatDist_sub_right (x y z : UnitAddTorus ι) : flatDist (x - z) (y - z) = flatDist x y := by
  unfold flatDist
  congr 1; refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.sub_apply, sub_sub_sub_cancel_right]

/-- **A smooth flat-`1`-Lipschitz function has `|∇φ| ≤ 1`.** -/
theorem sum_dpart_sq_le_one {φ : UnitAddTorus ι → ℝ} (hφ : IsSmoothT φ)
    (hL : FlatLipschitzWith 1 φ) (y : UnitAddTorus ι) : ∑ j, dpart_appA φ j y ^ 2 ≤ 1 := by
  set f := φ ∘ liftT with hf
  set x := secT y
  have hd : DifferentiableAt ℝ f x := (hφ.differentiable (by simp)).differentiableAt
  set L := fderiv ℝ f x
  set v : ι → ℝ := fun j => L (Pi.single j 1)
  have hv : ∀ j, dpart_appA φ j y = v j := fun j => rfl
  simp_rw [hv]
  set S := ∑ j, v j ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hLv : L v = S := by
    have : v = ∑ j, v j • (Pi.single j 1 : ι → ℝ) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    rw [map_sum]; simp only [map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the slope bound
  have hg : HasDerivAt (fun h : ℝ => f (x + h • v)) (L v) 0 := by
    have h1 : HasDerivAt (fun h : ℝ => x + h • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hd0 : HasFDerivAt f L (x + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
    exact hd0.comp_hasDerivAt (0 : ℝ) h1
  have hslope := hg.tendsto_slope_zero_right
  have hle : L v ≤ Real.sqrt S := by
    refine le_of_tendsto hslope (eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => ?_)
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have hlip := hL (liftT (x + h • v)) (liftT x)
    have hd' := flatDist_liftT_le (x + h • v) x
    have e : ∑ k, ((x + h • v) k - x k) ^ 2 = h ^ 2 * S := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, mul_pow, S,
        Finset.mul_sum]
    rw [e, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le] at hd'
    have : f (x + h • v) - f x ≤ h * Real.sqrt S := by
      have := (le_abs_self _).trans hlip
      simp only [one_mul] at this
      exact this.trans hd'
    rw [inv_mul_le_iff₀ hh]; exact this
  rw [hLv] at hle
  by_contra hc
  push Not at hc
  have : Real.sqrt S < S := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  linarith

/-- **The heat flow preserves flat-`1`-Lipschitz functions.** -/
theorem flatLipschitz_heatT {t : ℝ} (ht : 0 < t) {φ : UnitAddTorus ι → ℝ} (hc : Continuous φ)
    (hL : FlatLipschitzWith 1 φ) : FlatLipschitzWith 1 (heatT t φ) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hi : ∀ x, Integrable (fun y : ι → ℝ => φ (x - liftT y) * heatKernel t y) := fun x =>
    (integrable_heatKernel ht).bdd_mul (c := C)
      (hc.comp ((continuous_const (y := x)).sub continuous_liftT)).aestronglyMeasurable
      (Eventually.of_forall fun y => hC _ (mem_univ _))
  intro x x'
  unfold heatT
  rw [← integral_sub (hi x) (hi x'), one_mul]
  calc |∫ y, (φ (x - liftT y) * heatKernel t y - φ (x' - liftT y) * heatKernel t y)|
      ≤ ∫ y, |φ (x - liftT y) * heatKernel t y - φ (x' - liftT y) * heatKernel t y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, flatDist x x' * heatKernel t y := by
        refine integral_mono ((hi x).sub (hi x')).abs
          ((integrable_heatKernel ht).const_mul _) fun y => ?_
        rw [← sub_mul, abs_mul, abs_of_pos (heatKernel_pos ht y)]
        refine mul_le_mul_of_nonneg_right ?_ (heatKernel_pos ht y).le
        have := hL (x - liftT y) (x' - liftT y)
        rwa [one_mul, flatDist_sub_right] at this
    _ = flatDist x x' := by rw [integral_const_mul, integral_heatKernel ht, mul_one]

end SharpLSI
