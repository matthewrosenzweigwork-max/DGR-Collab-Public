import LeanResearch.PeriodicAttractiveLogGas.SmoothRepresentation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Actual smooth probability kernels on the Euclidean configuration cover,
and their descended convolutions with continuous configuration functions.

Source: the smooth approximation construction in Proposition 2.6. The kernel
uses Mathlib's normalized `ContDiffBump` on `Gradient N`, whose norm is the
genuine Euclidean norm on the `2 * N` labelled coordinates. Its rescaling has
the exact inverse-dimension factor, and its mass is computed using ordinary
Lebesgue volume. All natural particle counts are allowed, including the
zero-dimensional case; only the smoothing scale must be positive.

The quotient integral is explicit. Its Euclidean lift equals the actual
kernel-first convolution, so ordinary convolution smoothness and the open
quotient map prove smoothness of the lift and continuity of the descended
function. Lipschitz bounds and gradient convergence are separate results.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff Convolution Topology

namespace PeriodicAttractiveLogGas

theorem finrank_configurationGradient (N : ℕ) :
    Module.finrank ℝ (Gradient N) = 2 * N := by
  simp [Gradient, Nat.mul_comm]

/-- A fixed bump whose topological support is compactly inside the unit ball. -/
def configurationUnitBump (N : ℕ) : ContDiffBump (0 : Gradient N) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The normalization is by the actual integral with respect to Euclidean volume. -/
def configurationMollifier (N : ℕ) : Gradient N → ℝ :=
  (configurationUnitBump N).normed volume

theorem configurationMollifier_nonneg (N : ℕ) (x : Gradient N) :
    0 ≤ configurationMollifier N x :=
  (configurationUnitBump N).nonneg_normed x

theorem contDiff_configurationMollifier (N : ℕ) :
    ContDiff ℝ ∞ (configurationMollifier N) :=
  (configurationUnitBump N).contDiff_normed

theorem integrable_configurationMollifier (N : ℕ) :
    Integrable (configurationMollifier N) volume :=
  (configurationUnitBump N).integrable_normed

theorem integral_configurationMollifier (N : ℕ) :
    (∫ x : Gradient N, configurationMollifier N x) = 1 :=
  (configurationUnitBump N).integral_normed

theorem support_configurationMollifier (N : ℕ) :
    Function.support (configurationMollifier N) =
      ball (0 : Gradient N) (1 / 2 : ℝ) :=
  (configurationUnitBump N).support_normed_eq

theorem tsupport_configurationMollifier (N : ℕ) :
    tsupport (configurationMollifier N) =
      closedBall (0 : Gradient N) (1 / 2 : ℝ) :=
  (configurationUnitBump N).tsupport_normed_eq

theorem hasCompactSupport_configurationMollifier (N : ℕ) :
    HasCompactSupport (configurationMollifier N) :=
  (configurationUnitBump N).hasCompactSupport_normed

theorem tsupport_configurationMollifier_subset_unitBall (N : ℕ) :
    tsupport (configurationMollifier N) ⊆ ball (0 : Gradient N) 1 := by
  rw [tsupport_configurationMollifier]
  intro x hx
  have hx' : ‖x‖ ≤ (1 / 2 : ℝ) := mem_closedBall_zero_iff.mp hx
  exact mem_ball_zero_iff.mpr (by linarith)

theorem configurationMollifier_neg (N : ℕ) (x : Gradient N) :
    configurationMollifier N (-x) = configurationMollifier N x :=
  (configurationUnitBump N).normed_neg x

/-- Exact inverse-dimensional dilation of the one fixed probability kernel. -/
def scaledConfigurationMollifier (N : ℕ) (ε : ℝ) (x : Gradient N) : ℝ :=
  (ε ^ (2 * N))⁻¹ * configurationMollifier N (ε⁻¹ • x)

theorem scaledConfigurationMollifier_eq_finrank (N : ℕ) (ε : ℝ)
    (x : Gradient N) :
    scaledConfigurationMollifier N ε x =
      (ε ^ Module.finrank ℝ (Gradient N))⁻¹ * configurationMollifier N (ε⁻¹ • x) := by
  simp only [scaledConfigurationMollifier, finrank_configurationGradient]

theorem scaledConfigurationMollifier_argument_apply (N : ℕ) (ε : ℝ)
    (x : Gradient N) (j : Fin N × Fin 2) :
    (ε⁻¹ • x) j = x j / ε := by
  change ε⁻¹ * x j = x j / ε
  rw [div_eq_mul_inv, mul_comm]

theorem scaledConfigurationMollifier_nonneg (N : ℕ) (ε : ℝ) (x : Gradient N) :
    0 ≤ scaledConfigurationMollifier N ε x := by
  have hp : 0 ≤ ε ^ (2 * N) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg ε) N
  exact mul_nonneg (inv_nonneg.mpr hp) (configurationMollifier_nonneg N _)

theorem contDiff_scaledConfigurationMollifier (N : ℕ) (ε : ℝ) :
    ContDiff ℝ ∞ (scaledConfigurationMollifier N ε) := by
  unfold scaledConfigurationMollifier
  exact contDiff_const.mul
    ((contDiff_configurationMollifier N).comp
      (by
        convert (ε⁻¹ • ContinuousLinearMap.id ℝ (Gradient N)).contDiff using 1
        ext x
        rfl))

theorem scaledConfigurationMollifier_neg (N : ℕ) (ε : ℝ) (x : Gradient N) :
    scaledConfigurationMollifier N ε (-x) = scaledConfigurationMollifier N ε x := by
  simp only [scaledConfigurationMollifier, smul_neg, configurationMollifier_neg]

theorem support_scaledConfigurationMollifier_subset (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Function.support (scaledConfigurationMollifier N ε) ⊆
      ball (0 : Gradient N) (ε / 2) := by
  intro x hx
  have hf : configurationMollifier N (ε⁻¹ • x) ≠ 0 := by
    intro hf
    exact hx (by simp only [scaledConfigurationMollifier, hf, mul_zero])
  have hb : ε⁻¹ • x ∈ ball (0 : Gradient N) (1 / 2 : ℝ) := by
    rw [← support_configurationMollifier]
    exact hf
  have hn : ε⁻¹ * ‖x‖ < (1 / 2 : ℝ) := by
    simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)] using hb
  have hn' := mul_lt_mul_of_pos_left hn hε
  rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at hn'
  rw [mem_ball_zero_iff]
  simpa only [div_eq_mul_inv, one_mul] using hn'

theorem tsupport_scaledConfigurationMollifier_subset_closedBall
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    tsupport (scaledConfigurationMollifier N ε) ⊆
      closedBall (0 : Gradient N) (ε / 2) :=
  closure_minimal
    ((support_scaledConfigurationMollifier_subset N ε hε).trans ball_subset_closedBall)
    isClosed_closedBall

theorem tsupport_scaledConfigurationMollifier_subset_ball
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    tsupport (scaledConfigurationMollifier N ε) ⊆ ball (0 : Gradient N) ε := by
  intro x hx
  have hx' := tsupport_scaledConfigurationMollifier_subset_closedBall N ε hε hx
  rw [mem_closedBall_zero_iff] at hx'
  exact mem_ball_zero_iff.mpr (by linarith)

theorem support_scaledConfigurationMollifier_subset_scale
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Function.support (scaledConfigurationMollifier N ε) ⊆
      closedBall (0 : Gradient N) ε := by
  intro x hx
  have hx' : ‖x‖ < ε / 2 :=
    mem_ball_zero_iff.mp (support_scaledConfigurationMollifier_subset N ε hε hx)
  exact mem_closedBall_zero_iff.mpr (by linarith)

theorem hasCompactSupport_scaledConfigurationMollifier
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (scaledConfigurationMollifier N ε) :=
  (isCompact_closedBall (0 : Gradient N) (ε / 2)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_scaledConfigurationMollifier_subset_closedBall N ε hε)

theorem integrable_scaledConfigurationMollifier (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (scaledConfigurationMollifier N ε) volume :=
  (contDiff_scaledConfigurationMollifier N ε).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledConfigurationMollifier N ε hε)

/-- Inverse dilation contributes exactly `ε ^ (2 * N)` to Lebesgue volume. -/
theorem integral_configurationMollifier_inv_smul (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∫ x : Gradient N, configurationMollifier N (ε⁻¹ • x)) = ε ^ (2 * N) := by
  simpa only [finrank_configurationGradient, integral_configurationMollifier,
    smul_eq_mul, mul_one] using
    (Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Gradient N))
      (configurationMollifier N) hε.le)

theorem integral_scaledConfigurationMollifier (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∫ x : Gradient N, scaledConfigurationMollifier N ε x) = 1 := by
  simp only [scaledConfigurationMollifier, integral_const_mul,
    integral_configurationMollifier_inv_smul N ε hε]
  exact inv_mul_cancel₀ (pow_ne_zero (2 * N) hε.ne')

/-- The convolution is genuinely integrable at every point of the Euclidean cover. -/
theorem configurationMollification_convolutionExists {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) :
    ConvolutionExists (scaledConfigurationMollifier N ε)
      (fun x : Gradient N ↦ f (configurationQuotient N x))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  (hasCompactSupport_scaledConfigurationMollifier N ε hε).convolutionExists_left_of_continuous_right
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (integrable_scaledConfigurationMollifier N ε hε).locallyIntegrable
    (f.continuous.comp (continuous_configurationQuotient N))

/-- Smoothness is obtained from the actual compact-kernel convolution theorem. -/
theorem contDiff_configurationMollification_convolution {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) :
    ContDiff ℝ ∞ ((scaledConfigurationMollifier N ε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun x : Gradient N ↦ f (configurationQuotient N x))) := by
  have hf : LocallyIntegrable (fun x : Gradient N ↦ f (configurationQuotient N x)) volume :=
    (f.continuous.comp (continuous_configurationQuotient N)).locallyIntegrable
  exact (hasCompactSupport_scaledConfigurationMollifier N ε hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (contDiff_scaledConfigurationMollifier N ε) hf

/-- The descended integral, using the quotient translation of each Euclidean displacement. -/
def configurationMollificationValue {N : ℕ} (ε : ℝ) (f : C(Configuration N, ℝ))
    (x : Configuration N) : ℝ :=
  ∫ y : Gradient N, scaledConfigurationMollifier N ε y * f (x - configurationQuotient N y)

@[simp]
theorem configurationMollificationValue_quotient {N : ℕ} (ε : ℝ)
    (f : C(Configuration N, ℝ)) (x : Gradient N) :
    configurationMollificationValue ε f (configurationQuotient N x) =
      ((scaledConfigurationMollifier N ε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y : Gradient N ↦ f (configurationQuotient N y))) x := by
  simp only [configurationMollificationValue, convolution, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, configurationQuotient_sub]

/-- In particular, the actual Euclidean convolution is invariant on quotient fibers. -/
theorem configurationMollification_convolution_eq_of_quotient_eq {N : ℕ} (ε : ℝ)
    (f : C(Configuration N, ℝ)) {x y : Gradient N}
    (hxy : configurationQuotient N x = configurationQuotient N y) :
    ((scaledConfigurationMollifier N ε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun z : Gradient N ↦ f (configurationQuotient N z))) x =
      ((scaledConfigurationMollifier N ε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun z : Gradient N ↦ f (configurationQuotient N z))) y := by
  rw [← configurationMollificationValue_quotient ε f x,
    ← configurationMollificationValue_quotient ε f y, hxy]

theorem configurationMollification_integrand_integrable {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) (x : Configuration N) :
    Integrable (fun y : Gradient N ↦
      scaledConfigurationMollifier N ε y * f (x - configurationQuotient N y)) volume := by
  obtain ⟨z, rfl⟩ := configurationQuotient_surjective N x
  simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    configurationQuotient_sub] using configurationMollification_convolutionExists ε hε f z

theorem contDiff_configurationMollificationValue_lift {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) :
    ContDiff ℝ ∞ (fun x : Gradient N ↦
      configurationMollificationValue ε f (configurationQuotient N x)) := by
  simpa only [configurationMollificationValue_quotient] using
    contDiff_configurationMollification_convolution ε hε f

theorem continuous_configurationMollificationValue {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) :
    Continuous (configurationMollificationValue ε f) := by
  apply (isOpenQuotientMap_configurationQuotient N).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def] using
    (contDiff_configurationMollificationValue_lift ε hε f).continuous

/-- Actual continuous configuration function with a globally smooth Euclidean lift. -/
def configurationMollification {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (f : C(Configuration N, ℝ)) : C(Configuration N, ℝ) :=
  ⟨configurationMollificationValue ε f, continuous_configurationMollificationValue ε hε f⟩

@[simp]
theorem configurationMollification_apply {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (f : C(Configuration N, ℝ)) (x : Configuration N) :
    configurationMollification ε hε f x = configurationMollificationValue ε f x := rfl

@[simp]
theorem configurationMollification_lift {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (f : C(Configuration N, ℝ)) (x : Gradient N) :
    configurationMollification ε hε f (configurationQuotient N x) =
      ((scaledConfigurationMollifier N ε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y : Gradient N ↦ f (configurationQuotient N y))) x :=
  configurationMollificationValue_quotient ε f x

theorem contDiff_configurationMollification_lift {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) :
    ContDiff ℝ ∞ (fun x : Gradient N ↦
      configurationMollification ε hε f (configurationQuotient N x)) :=
  contDiff_configurationMollificationValue_lift ε hε f

/-- Each mollification lies in the actual full ambient smooth core. -/
def configurationMollifiedSmoothPair {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (f : C(Configuration N, ℝ)) : SmoothPair N :=
  SmoothPair.ofContDiffLift (configurationMollification ε hε f)
    (contDiff_configurationMollification_lift ε hε f)

@[simp]
theorem configurationMollifiedSmoothPair_value {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (f : C(Configuration N, ℝ)) :
    (configurationMollifiedSmoothPair ε hε f).value = configurationMollification ε hε f := rfl

end PeriodicAttractiveLogGas
