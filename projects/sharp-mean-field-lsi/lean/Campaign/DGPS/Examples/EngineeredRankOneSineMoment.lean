import DGPS.Examples.EngineeredRankOneNormalization

/-!
# A uniform sine moment for the actual engineered reference

The central annulus `[1/(2 sqrt h), 1/sqrt h]` has uniformly positive mass:
its potential is bounded, and the normalizer is at most a constant times
`1/sqrt h`. The sine square there is at least a constant divided by h.
-/

open MeasureTheory Real Set
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne

/-- The actual engineered angular reference has sine second moment at least
`c/h`, with one positive constant independent of the field. -/
theorem engineered_sine_second_moment_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℝ, 2 ≤ h →
      c / h ≤ ∫ θ, Real.Angle.sin θ ^ 2 * qAng h θ ∂angHaar := by
  let C0 : ℝ := (2 * π)⁻¹ * √(π / (2 / π ^ 2))
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  let c := exp (-16) / (4 * π ^ 3 * C0)
  refine ⟨c, by dsimp [c]; positivity, fun h hh => ?_⟩
  have hp : 0 < h := by linarith
  have hs : 0 < √h := Real.sqrt_pos.2 hp
  let r := (√h)⁻¹
  have hr : 0 < r := inv_pos.2 hs
  have hr2 : r ^ 2 = h⁻¹ := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hp.le]
  have hhr : h * r ^ 2 = 1 := by rw [hr2]; exact mul_inv_cancel₀ hp.ne'
  have hr1 : r ≤ 1 := by
    have : r ^ 2 ≤ 1 := by rw [hr2]; exact inv_le_one_of_one_le₀ (by linarith)
    nlinarith
  have hZ : Zh h ≤ C0 * r := Zh_le h hp
  have hZpos := Zh_pos h hp
  have hZinv : (C0 * r)⁻¹ ≤ (Zh h)⁻¹ := inv_anti₀ hZpos hZ
  let F : ℝ → ℝ := fun t => Real.sin t ^ 2 * qAng h (t : AngCircle)
  have hfc : Continuous F :=
    (Real.continuous_sin.pow 2).mul ((continuous_qAng h hp).comp Real.Angle.continuous_coe)
  have hF0 (t : ℝ) : 0 ≤ F t := mul_nonneg (sq_nonneg _) (qAng_pos h hp _).le
  have hpoint (t : ℝ) (ht : t ∈ Icc (r / 2) r) :
      (r / π) ^ 2 * ((Zh h)⁻¹ * exp (-16)) ≤ F t := by
    have ht0 : 0 ≤ t := (show 0 ≤ r / 2 by positivity).trans ht.1
    have htpi : t ≤ π / 2 := ht.2.trans (hr1.trans (by linarith [Real.pi_gt_three]))
    have hsin : r / π ≤ Real.sin t := by
      calc r / π = 2 / π * (r / 2) := by ring
        _ ≤ 2 / π * t := mul_le_mul_of_nonneg_left ht.1 (by positivity)
        _ ≤ Real.sin t := Real.mul_le_sin ht0 htpi
    have hsin2 := pow_le_pow_left₀ (by positivity : 0 ≤ r / π) hsin 2
    have ht2 : t ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
    have hu : (1 - Real.cos t) ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [Real.cos_le_one t], by linarith [Real.neg_one_le_cos t]⟩
    have hhu : h * (1 - Real.cos t) ≤ 1 / 2 := by
      have htcos := Real.one_sub_sq_div_two_le_cos (x := t)
      have hmul := mul_le_mul_of_nonneg_left ht2 hp.le
      nlinarith
    have hc := corr_le_fifteen hh hu (by linarith)
    have he : exp (-16) ≤ exp (logq h (t : AngCircle)) := by
      apply exp_le_exp.2
      unfold logq
      rw [Uang_coe_eq]
      linarith
    have hq : (Zh h)⁻¹ * exp (-16) ≤ qAng h (t : AngCircle) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hZpos.le)
    exact mul_le_mul hsin2 hq (by positivity) (sq_nonneg _)
  have hmain : (r / 2) * ((r / π) ^ 2 * ((Zh h)⁻¹ * exp (-16))) ≤
      ∫ t in (-π)..π, F t := by
    calc
      _ = ∫ t in (r / 2)..r, (r / π) ^ 2 * ((Zh h)⁻¹ * exp (-16)) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ t in (r / 2)..r, F t :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          (hfc.intervalIntegrable _ _) hpoint
      _ ≤ ∫ t in (-π)..π, F t :=
        intervalIntegral.integral_mono_interval (by linarith [Real.pi_pos])
          (by linarith) (by linarith [Real.pi_gt_three])
          (Filter.Eventually.of_forall hF0) (hfc.intervalIntegrable _ _)
  rw [integral_angHaar_eq_interval]
  change c / h ≤ (2 * π)⁻¹ * ∫ t in (-π)..π, F t
  calc
    c / h = (2 * π)⁻¹ * ((r / 2) * ((r / π) ^ 2 * ((C0 * r)⁻¹ * exp (-16)))) := by
      calc c / h = c * r ^ 2 := by rw [hr2]; ring
        _ = _ := by
          dsimp [c]
          field_simp [hr.ne', hC0.ne', Real.pi_pos.ne']
          ring
    _ ≤ (2 * π)⁻¹ * ((r / 2) * ((r / π) ^ 2 * ((Zh h)⁻¹ * exp (-16)))) := by
      gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)

end DGPS.Examples
