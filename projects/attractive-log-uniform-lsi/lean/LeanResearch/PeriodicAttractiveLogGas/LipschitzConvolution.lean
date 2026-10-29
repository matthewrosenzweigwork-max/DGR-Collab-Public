import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Convolution facts used in the Lipschitz approximation and smooth clipping
arguments of source Proposition 2.6. Nonnegative probability kernels preserve
the exact Lipschitz bound. These statements do not yet assert membership in
the weighted ambient form domain. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Convolution Topology NNReal

namespace PeriodicAttractiveLogGas

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {ρ f : E → ℝ} {K : ℝ≥0}

theorem lipschitzWith_probability_convolution (hρc : HasCompactSupport ρ)
    (hρi : Integrable ρ μ) (hρ : ∀ x, 0 ≤ ρ x) (hρm : ∫ x, ρ x ∂μ = 1)
    (hf : LipschitzWith K f) :
    LipschitzWith K (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  have hc : ∀ x, Integrable (fun z ↦ ρ z * f (x - z)) μ :=
    hρc.convolutionExists_left_of_continuous_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hρi.locallyIntegrable hf.continuous
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (∫ z, ρ z * f (x - z) ∂μ) (∫ z, ρ z * f (y - z) ∂μ) ≤ _
  rw [dist_eq_norm, ← integral_sub (hc x) (hc y)]
  calc
    ‖∫ z, (ρ z * f (x - z) - ρ z * f (y - z)) ∂μ‖ ≤
        ∫ z, ρ z * ((K : ℝ) * dist x y) ∂μ := by
      apply norm_integral_le_of_norm_le (hρi.mul_const _)
      exact Eventually.of_forall (fun z ↦ by
        rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hρ z)]
        apply mul_le_mul_of_nonneg_left _ (hρ z)
        simpa only [← dist_eq_norm, dist_sub_right] using hf.dist_le_mul (x - z) (y - z))
    _ = (K : ℝ) * dist x y := by rw [integral_mul_const, hρm, one_mul]

theorem norm_fderiv_probability_convolution_le [NormedSpace ℝ E]
    (hρc : HasCompactSupport ρ) (hρi : Integrable ρ μ) (hρ : ∀ x, 0 ≤ ρ x)
    (hρm : ∫ x, ρ x ∂μ = 1) (hf : LipschitzWith K f) (x : E) :
    ‖fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x‖ ≤ (K : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_probability_convolution hρc hρi hρ hρm hf)

theorem dist_probability_convolution_le (hρc : HasCompactSupport ρ)
    (hρi : Integrable ρ μ) (hρ : ∀ x, 0 ≤ ρ x) (hρm : ∫ x, ρ x ∂μ = 1)
    (hf : LipschitzWith K f) {r : ℝ} (_hr : 0 ≤ r)
    (hs : Function.support ρ ⊆ closedBall (0 : E) r) (x : E) :
    dist ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x) (f x) ≤ (K : ℝ) * r := by
  have hc : Integrable (fun z ↦ ρ z * f (x - z)) μ :=
    hρc.convolutionExists_left_of_continuous_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hρi.locallyIntegrable hf.continuous x
  have hconst : f x = ∫ z, ρ z * f x ∂μ := by rw [integral_mul_const, hρm, one_mul]
  change dist (∫ z, ρ z * f (x - z) ∂μ) (f x) ≤ _
  rw [hconst, dist_eq_norm, ← integral_sub hc (hρi.mul_const (f x))]
  calc
    ‖∫ z, (ρ z * f (x - z) - ρ z * f x) ∂μ‖ ≤ ∫ z, ρ z * ((K : ℝ) * r) ∂μ := by
      apply norm_integral_le_of_norm_le (hρi.mul_const _)
      refine Eventually.of_forall (fun z ↦ ?_)
      by_cases hz : z ∈ Function.support ρ
      · rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hρ z)]
        apply mul_le_mul_of_nonneg_left _ (hρ z)
        have hzr : ‖z‖ ≤ r := by simpa only [mem_closedBall_zero_iff] using hs hz
        have hd : dist (x - z) x = ‖z‖ := by simp
        have hfx : ‖f (x - z) - f x‖ ≤ (K : ℝ) * ‖z‖ := by
          simpa only [← dist_eq_norm, hd] using hf.dist_le_mul (x - z) x
        exact hfx.trans (mul_le_mul_of_nonneg_left hzr K.coe_nonneg)
      · have hz0 : ρ z = 0 := Function.notMem_support.mp hz
        simp only [hz0, zero_mul, sub_zero, norm_zero, le_refl]
    _ = (K : ℝ) * r := by rw [integral_mul_const, hρm, one_mul]

theorem tendstoUniformly_probability_convolution {ι : Type*} {l : Filter ι}
    (ρs : ι → E → ℝ) (rs : ι → ℝ) (hρc : ∀ i, HasCompactSupport (ρs i))
    (hρi : ∀ i, Integrable (ρs i) μ) (hρ : ∀ i x, 0 ≤ ρs i x)
    (hρm : ∀ i, ∫ x, ρs i x ∂μ = 1) (hf : LipschitzWith K f)
    (hr : ∀ i, 0 ≤ rs i) (hs : ∀ i, Function.support (ρs i) ⊆ closedBall (0 : E) (rs i))
    (ht : Tendsto rs l (𝓝 0)) :
    TendstoUniformly (fun i ↦ ρs i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) f l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  have he : Tendsto (fun i ↦ (K : ℝ) * rs i) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  filter_upwards [he.eventually (gt_mem_nhds hη)] with i hi x
  simpa only [dist_comm] using
    (dist_probability_convolution_le (hρc i) (hρi i) (hρ i) (hρm i)
      hf (hr i) (hs i) x).trans_lt hi

end PeriodicAttractiveLogGas
