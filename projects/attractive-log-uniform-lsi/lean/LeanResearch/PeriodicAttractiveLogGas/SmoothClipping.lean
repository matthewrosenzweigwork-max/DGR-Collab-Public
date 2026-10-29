import LeanResearch.PeriodicAttractiveLogGas.MollifierDerivativeLimit
import LeanResearch.PeriodicAttractiveLogGas.SmoothContraction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual smooth approximations of the normal clipping contraction used in
source Proposition 2.6. A nonnegative normalized compact real kernel is
dilated with its actual inverse-dimensional normalization. Its convolutions
with clipping are smooth, retain Lipschitz constant one, and converge
uniformly with explicit error at most the scale. The final lemma passes this
uniform approximation to scalar L2 composition for every finite measure. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff Convolution NNReal

namespace PeriodicAttractiveLogGas

def normalClip (t : ℝ) : ℝ := min 1 (max 0 t)

theorem normalClip_nonneg (t : ℝ) : 0 ≤ normalClip t :=
  le_min zero_le_one (le_max_left _ _)

theorem normalClip_le_one (t : ℝ) : normalClip t ≤ 1 := min_le_left _ _

theorem norm_normalClip_le_one (t : ℝ) : ‖normalClip t‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (normalClip_nonneg t)]
  exact normalClip_le_one t

theorem normalClip_lipschitz : LipschitzWith 1 normalClip :=
  (LipschitzWith.id.const_max 0).const_min 1

def clippingUnitBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def clippingKernel : ℝ → ℝ := clippingUnitBump.normed volume

theorem clippingKernel_nonneg (x : ℝ) : 0 ≤ clippingKernel x :=
  clippingUnitBump.nonneg_normed x

theorem contDiff_clippingKernel : ContDiff ℝ ∞ clippingKernel :=
  clippingUnitBump.contDiff_normed

theorem hasCompactSupport_clippingKernel : HasCompactSupport clippingKernel :=
  clippingUnitBump.hasCompactSupport_normed

theorem integral_clippingKernel : (∫ x : ℝ, clippingKernel x) = 1 :=
  clippingUnitBump.integral_normed

theorem tsupport_clippingKernel_subset : tsupport clippingKernel ⊆ closedBall (0 : ℝ) 1 := by
  have h := clippingUnitBump.tsupport_normed_eq (μ := volume)
  change tsupport (clippingUnitBump.normed volume) ⊆ _
  rw [h]
  exact closedBall_subset_closedBall (by norm_num [clippingUnitBump])

def smoothClip (ε : ℝ) : ℝ → ℝ :=
  mollifierDilate clippingKernel ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] normalClip

theorem smoothClip_smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (smoothClip ε) :=
  contDiff_mollifierDilate_convolution volume hasCompactSupport_clippingKernel
    contDiff_clippingKernel normalClip_lipschitz.continuous hε

theorem smoothClip_lipschitz {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (smoothClip ε) := by
  apply lipschitzWith_probability_convolution
    (hasCompactSupport_mollifierDilate hasCompactSupport_clippingKernel hε)
    ((contDiff_mollifierDilate contDiff_clippingKernel ε).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifierDilate hasCompactSupport_clippingKernel hε))
    (fun x ↦ mollifierDilate_nonneg clippingKernel_nonneg hε x)
    (by rw [integral_mollifierDilate volume hε, integral_clippingKernel])
    normalClip_lipschitz

theorem abs_deriv_smoothClip_le_one {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |deriv (smoothClip ε) t| ≤ 1 := by
  simpa only [Real.norm_eq_abs, NNReal.coe_one] using
    (norm_deriv_le_of_lipschitz (smoothClip_lipschitz hε) (x₀ := t))

theorem dist_smoothClip_normalClip_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    dist (smoothClip ε t) (normalClip t) ≤ ε := by
  have hs : Function.support (mollifierDilate clippingKernel ε) ⊆ closedBall (0 : ℝ) ε := by
    exact (subset_tsupport _).trans
      (by simpa only [mul_one] using
        tsupport_mollifierDilate_subset hε tsupport_clippingKernel_subset)
  simpa only [smoothClip, NNReal.coe_one, one_mul] using!
    dist_probability_convolution_le
      (hasCompactSupport_mollifierDilate hasCompactSupport_clippingKernel hε)
      ((contDiff_mollifierDilate contDiff_clippingKernel ε).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_mollifierDilate hasCompactSupport_clippingKernel hε))
      (fun x ↦ mollifierDilate_nonneg clippingKernel_nonneg hε x)
      (by rw [integral_mollifierDilate volume hε, integral_clippingKernel])
      normalClip_lipschitz hε.le hs t

def clippingScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem clippingScale_pos (n : ℕ) : 0 < clippingScale n := by
  unfold clippingScale
  positivity

theorem tendsto_clippingScale : Tendsto clippingScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

section ScalarL2
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem memLp_normalClip (f : Lp ℝ 2 μ) : MemLp (fun x ↦ normalClip (f x)) 2 μ :=
  MemLp.of_bound
    (normalClip_lipschitz.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) 1
    (Eventually.of_forall (fun x ↦ norm_normalClip_le_one (f x)))

def normalClipL2 (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (memLp_normalClip f).toLp (fun x ↦ normalClip (f x))

theorem normalClipL2_coe (f : Lp ℝ 2 μ) :
    normalClipL2 f =ᵐ[μ] (fun x ↦ normalClip (f x)) := (memLp_normalClip f).coeFn_toLp

/-- The uniform approximation becomes a strong L2 approximation without any
pointwise assumption on the L2 representative. -/
theorem tendsto_smoothClip_composition_L2 (f : Lp ℝ 2 μ) :
    Tendsto (fun n ↦ smoothContractionValueL2 (smoothClip (clippingScale n))
      (smoothClip_smooth (clippingScale_pos n))
      (abs_deriv_smoothClip_le_one (clippingScale_pos n)) f) atTop
      (𝓝 (normalClipL2 f)) := by
  let oneL2 : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ : α ↦ (1 : ℝ))
  have hone : oneL2 =ᵐ[μ] (fun _ : α ↦ (1 : ℝ)) := (memLp_const (1 : ℝ)).coeFn_toLp
  let V : ℕ → Lp ℝ 2 μ := fun n ↦ smoothContractionValueL2 (smoothClip (clippingScale n))
    (smoothClip_smooth (clippingScale_pos n))
    (abs_deriv_smoothClip_le_one (clippingScale_pos n)) f
  have hb (n : ℕ) : ‖V n - normalClipL2 f‖ ≤ clippingScale n * ‖oneL2‖ := by
    have hcmp : ‖V n - normalClipL2 f‖ ≤ ‖clippingScale n • oneL2‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_sub (V n) (normalClipL2 f),
        smoothContractionValueL2_coe (smoothClip (clippingScale n))
          (smoothClip_smooth (clippingScale_pos n))
          (abs_deriv_smoothClip_le_one (clippingScale_pos n)) f,
        normalClipL2_coe f, Lp.coeFn_smul (clippingScale n) oneL2, hone]
        with x hs hv hc hm ho
      rw [hs, hm]
      change ‖V n x - normalClipL2 f x‖ ≤ ‖clippingScale n • oneL2 x‖
      rw [hv, hc, ho, smul_eq_mul, mul_one, Real.norm_of_nonneg (clippingScale_pos n).le]
      simpa only [dist_eq_norm] using dist_smoothClip_normalClip_le (clippingScale_pos n) (f x)
    simpa only [norm_smul, Real.norm_of_nonneg (clippingScale_pos n).le] using hcmp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n ↦ norm_nonneg _) hb
  simpa only [zero_mul] using tendsto_clippingScale.mul_const ‖oneL2‖

end ScalarL2
end PeriodicAttractiveLogGas
