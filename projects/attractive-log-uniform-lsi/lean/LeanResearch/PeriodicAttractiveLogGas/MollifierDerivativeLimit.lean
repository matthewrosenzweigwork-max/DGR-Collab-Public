import LeanResearch.PeriodicAttractiveLogGas.LipschitzConvolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The pointwise derivative-convergence ingredient in the Lipschitz
approximation paragraph of source Proposition 2.6.

Differentiation first falls on the smooth compact kernel, using Mathlib's
ordinary differentiation-under-the-integral theorem. Convolution of an affine
function has exactly the same derivative when the kernel has mass one. Their
difference is estimated by the actual first-order Taylor remainder. A family
lemma records the shrinking-support and radius-times-L1-derivative hypotheses;
the subsequent dilation lemmas discharge both for a fixed compact smooth
kernel with the exact inverse-dimension normalization.

No weak-gradient convolution formula, almost-everywhere differentiability
theorem, or weighted form-domain membership is assumed here. This supplies
the convergence at each point of ordinary Frechet differentiability.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Convolution Topology ContDiff NNReal

namespace PeriodicAttractiveLogGas

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {ρ f : E → ℝ}

/-- The derivative-kernel integrand is genuinely integrable, including its
operator norm. Compact support belongs to the differentiated kernel. -/
theorem integrable_mollifier_fderiv_integrand
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hf : Continuous f) (x : E) :
    Integrable (fun t ↦ f (x - t) • fderiv ℝ ρ t) μ := by
  exact ((hf.comp (continuous_const.sub continuous_id)).smul
    (hρ.continuous_fderiv (by simp))).integrable_of_hasCompactSupport
      (hρc.fderiv ℝ).smul_left

theorem integrable_norm_fderiv_mollifier
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ) :
    Integrable (fun t ↦ ‖fderiv ℝ ρ t‖) μ :=
  ((hρ.continuous_fderiv (by simp)).integrable_of_hasCompactSupport
    (hρc.fderiv ℝ)).norm

/-- Ordinary differentiation of the compact-kernel convolution. This formula
puts the derivative on the kernel, without presupposing a derivative of `f`. -/
theorem fderiv_mollifier_convolution_eq_integral
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hf : Continuous f) (x : E) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x =
      ∫ t, f (x - t) • fderiv ℝ ρ t ∂μ := by
  rw [(hρc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hρ.of_le (by simp)) hf.locallyIntegrable x).fderiv]
  unfold convolution
  apply integral_congr_ae
  filter_upwards with t
  ext v
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply,
    smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The finite first moment needed to compute an affine convolution exists
because its kernel has compact support. -/
theorem integrable_mollifier_linear_moment
    (hρc : HasCompactSupport ρ) (hρ : Continuous ρ) (L : E →L[ℝ] ℝ) :
    Integrable (fun t ↦ ρ t * L t) μ :=
  (hρ.mul L.continuous).integrable_of_hasCompactSupport hρc.mul_right

theorem mollifier_convolution_affine
    (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hmass : ∫ t, ρ t ∂μ = 1) (c : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (fun z ↦ c + L z)) x =
      c + L x - ∫ t, ρ t * L t ∂μ := by
  have hi : Integrable ρ μ := hρ.integrable_of_hasCompactSupport hρc
  change (∫ t, ρ t * (c + L (x - t)) ∂μ) = _
  calc
    (∫ t, ρ t * (c + L (x - t)) ∂μ) =
        ∫ t, (ρ t * (c + L x) - ρ t * L t) ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [map_sub]
      ring
    _ = (∫ t, ρ t * (c + L x) ∂μ) - ∫ t, ρ t * L t ∂μ :=
      integral_sub (hi.mul_const _) (integrable_mollifier_linear_moment μ hρc hρ L)
    _ = c + L x - ∫ t, ρ t * L t ∂μ := by
      rw [integral_mul_const, hmass, one_mul]

/-- Mass one reproduces the derivative of every affine function. No vanishing
first moment or radiality assumption is needed. -/
theorem hasFDerivAt_mollifier_convolution_affine
    (hρc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hmass : ∫ t, ρ t ∂μ = 1) (c : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (fun z ↦ c + L z)) L x := by
  have heq : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (fun z ↦ c + L z)) =
      (fun z ↦ c + L z - ∫ t, ρ t * L t ∂μ) :=
    funext (mollifier_convolution_affine μ hρc hρ hmass c L)
  rw [heq]
  simpa only [zero_add, sub_zero] using!
    ((hasFDerivAt_const c x).add L.hasFDerivAt).sub
      (hasFDerivAt_const (∫ t, ρ t * L t ∂μ) x)

/-- An exact Taylor-remainder identity for the derivative error, as an
ordinary Bochner integral with values in continuous linear maps. -/
theorem fderiv_mollifier_convolution_sub_eq_integral_remainder
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hmass : ∫ t, ρ t ∂μ = 1) (hf : Continuous f)
    (x : E) (L : E →L[ℝ] ℝ) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - L =
      ∫ t, (f (x - t) - f x - L (-t)) • fderiv ℝ ρ t ∂μ := by
  let A : E → ℝ := fun z ↦ (f x - L x) + L z
  have hA : Continuous A := continuous_const.add L.continuous
  have hiF := integrable_mollifier_fderiv_integrand μ hρc hρ hf x
  have hiA := integrable_mollifier_fderiv_integrand μ hρc hρ hA x
  have hderA : (∫ t, A (x - t) • fderiv ℝ ρ t ∂μ) = L := by
    rw [← fderiv_mollifier_convolution_eq_integral μ hρc hρ hA x]
    exact (hasFDerivAt_mollifier_convolution_affine μ hρc hρ.continuous
      hmass (f x - L x) L x).fderiv
  calc
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - L =
        (∫ t, f (x - t) • fderiv ℝ ρ t ∂μ) -
          ∫ t, A (x - t) • fderiv ℝ ρ t ∂μ :=
      congrArg₂ (fun a b : E →L[ℝ] ℝ ↦ a - b)
        (fderiv_mollifier_convolution_eq_integral μ hρc hρ hf x) hderA.symm
    _ = ∫ t, (f (x - t) - f x - L (-t)) • fderiv ℝ ρ t ∂μ := by
      rw [← integral_sub hiF hiA]
      apply integral_congr_ae
      filter_upwards with t
      rw [← sub_smul]
      congr 1
      dsimp [A]
      rw [map_sub, map_neg]
      ring

theorem norm_fderiv_mollifier_convolution_sub_le
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hmass : ∫ t, ρ t ∂μ = 1) (hf : Continuous f)
    (x : E) (L : E →L[ℝ] ℝ) {b : ℝ}
    (hrem : ∀ t ∈ tsupport ρ, ‖f (x - t) - f x - L (-t)‖ ≤ b) :
    ‖fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - L‖ ≤
      b * ∫ t, ‖fderiv ℝ ρ t‖ ∂μ := by
  rw [fderiv_mollifier_convolution_sub_eq_integral_remainder μ hρc hρ hmass hf]
  calc
    ‖∫ t, (f (x - t) - f x - L (-t)) • fderiv ℝ ρ t ∂μ‖ ≤
        ∫ t, b * ‖fderiv ℝ ρ t‖ ∂μ := by
      apply norm_integral_le_of_norm_le ((integrable_norm_fderiv_mollifier μ hρc hρ).const_mul b)
      refine Eventually.of_forall (fun t ↦ ?_)
      by_cases ht : t ∈ tsupport ρ
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hrem t ht) (norm_nonneg _)
      · simp only [fderiv_of_notMem_tsupport ℝ ht, smul_zero, norm_zero, mul_zero, le_refl]
    _ = b * ∫ t, ‖fderiv ℝ ρ t‖ ∂μ := integral_const_mul _ _

/-- A family version with explicit analytic hypotheses. The later dilation
theorems verify these hypotheses for one fixed compact kernel. Nonnegativity
is unnecessary for this derivative-convergence assertion. -/
theorem tendsto_fderiv_mollifier_family
    {ι : Type*} {l : Filter ι} (ρs : ι → E → ℝ) (r : ι → ℝ)
    (hρc : ∀ i, HasCompactSupport (ρs i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρs i))
    (hmass : ∀ i, ∫ t, ρs i t ∂μ = 1)
    (hs : ∀ i, tsupport (ρs i) ⊆ closedBall (0 : E) (r i))
    (_hr : ∀ i, 0 ≤ r i) (hrt : Tendsto r l (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hder : ∀ i, r i * (∫ t, ‖fderiv ℝ (ρs i) t‖ ∂μ) ≤ C)
    (hf : Continuous f) {x : E} {L : E →L[ℝ] ℝ} (hfx : HasFDerivAt f L x) :
    Tendsto (fun i ↦ fderiv ℝ (ρs i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x)
      l (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let δ : ℝ := η / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hη hden
  have hsmall := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hfx).bound hδ
  obtain ⟨a, ha, hlocal⟩ := Metric.eventually_nhds_iff.mp hsmall
  filter_upwards [hrt.eventually (gt_mem_nhds ha)] with i hi
  have hbound : ∀ t ∈ tsupport (ρs i),
      ‖f (x - t) - f x - L (-t)‖ ≤ δ * r i := by
    intro t ht
    have ht' : ‖t‖ ≤ r i := mem_closedBall_zero_iff.mp (hs i ht)
    have hdist : dist (-t) (0 : E) < a := by
      simpa only [dist_zero_right, norm_neg] using ht'.trans_lt hi
    have hrem := hlocal hdist
    simp only [← sub_eq_add_neg, norm_neg] at hrem
    exact hrem.trans (mul_le_mul_of_nonneg_left ht' hδ.le)
  calc
    dist (fderiv ℝ (ρs i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x) L =
        ‖fderiv ℝ (ρs i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x - L‖ := dist_eq_norm _ _
    _ ≤ (δ * r i) * ∫ t, ‖fderiv ℝ (ρs i) t‖ ∂μ :=
      norm_fderiv_mollifier_convolution_sub_le μ (hρc i) (hρ i) (hmass i) hf x L hbound
    _ ≤ δ * C := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hder i) hδ.le
    _ < η := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith

/-- Exact inverse-dimension dilation of one fixed kernel. -/
def mollifierDilate (ρ : E → ℝ) (ε : ℝ) (x : E) : ℝ :=
  (ε ^ Module.finrank ℝ E)⁻¹ * ρ (ε⁻¹ • x)

theorem contDiff_mollifierDilate (hρ : ContDiff ℝ ∞ ρ) (ε : ℝ) :
    ContDiff ℝ ∞ (mollifierDilate ρ ε) := by
  unfold mollifierDilate
  exact contDiff_const.mul (hρ.comp
    (show ContDiff ℝ ∞ (fun x : E ↦ ε⁻¹ • x) from
      (contDiff_id : ContDiff ℝ ∞ (id : E → E)).const_smul _))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mollifierDilate_nonneg (hρ : ∀ t, 0 ≤ ρ t) {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 ≤ mollifierDilate ρ ε x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (hρ _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem tsupport_mollifierDilate_subset
    {R ε : ℝ} (hε : 0 < ε) (hs : tsupport ρ ⊆ closedBall (0 : E) R) :
    tsupport (mollifierDilate ρ ε) ⊆ closedBall (0 : E) (ε * R) := by
  apply closure_minimal _ isClosed_closedBall
  intro t ht
  have hρt : ρ (ε⁻¹ • t) ≠ 0 := by
    intro hz
    exact ht (by simp only [mollifierDilate, hz, mul_zero])
  have hb := hs (subset_tsupport ρ hρt)
  have hn : ε⁻¹ * ‖t‖ ≤ R := by
    simpa only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)] using hb
  have hm := mul_le_mul_of_nonneg_left hn hε.le
  rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at hm
  exact mem_closedBall_zero_iff.mpr hm

theorem hasCompactSupport_mollifierDilate
    (hρc : HasCompactSupport ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifierDilate ρ ε) := by
  obtain ⟨R, hR⟩ := hρc.isBounded.subset_closedBall (0 : E)
  exact (isCompact_closedBall (0 : E) (ε * R)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_mollifierDilate_subset hε hR)

theorem integral_mollifierDilate {ε : ℝ} (hε : 0 < ε) :
    (∫ t, mollifierDilate ρ ε t ∂μ) = ∫ t, ρ t ∂μ := by
  unfold mollifierDilate
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg μ ρ hε.le,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hε.ne'), one_mul]

/-- Both factors in the scaling derivative are explicit: one inverse power
for the volume normalization and one inverse scale for the ordinary chain rule. -/
theorem fderiv_mollifierDilate (hρ : ContDiff ℝ ∞ ρ) (ε : ℝ) (x : E) :
    fderiv ℝ (mollifierDilate ρ ε) x =
      ((ε ^ Module.finrank ℝ E)⁻¹ * ε⁻¹) • fderiv ℝ ρ (ε⁻¹ • x) := by
  have hlin : HasFDerivAt (fun y : E ↦ ε⁻¹ • y)
      (ε⁻¹ • ContinuousLinearMap.id ℝ E) x := (hasFDerivAt_id x).const_smul _
  have hd := (((hρ.differentiable (by simp)) (ε⁻¹ • x)).hasFDerivAt.comp x hlin).const_smul
    ((ε ^ Module.finrank ℝ E)⁻¹)
  have hmap : (ε ^ Module.finrank ℝ E)⁻¹ •
      (fderiv ℝ ρ (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ E) =
        ((ε ^ Module.finrank ℝ E)⁻¹ * ε⁻¹) • fderiv ℝ ρ (ε⁻¹ • x) := by
    ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul]
  rw [hmap] at hd
  simpa only [mollifierDilate, Function.comp_def, Pi.smul_apply, smul_eq_mul] using! hd.fderiv

/-- The derivative-kernel L1 norm scales as exactly the inverse radius.
This is an actual Haar change of variables, not an assumed mollifier bound. -/
theorem integral_norm_fderiv_mollifierDilate
    (hρ : ContDiff ℝ ∞ ρ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t, ‖fderiv ℝ (mollifierDilate ρ ε) t‖ ∂μ) =
      ε⁻¹ * ∫ t, ‖fderiv ℝ ρ t‖ ∂μ := by
  simp only [fderiv_mollifierDilate hρ, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (inv_nonneg.mpr hε.le)),
    integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg μ (fun t ↦ ‖fderiv ℝ ρ t‖) hε.le,
    smul_eq_mul]
  field_simp [hε.ne']

theorem radius_mul_integral_norm_fderiv_mollifierDilate
    (hρ : ContDiff ℝ ∞ ρ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    (ε * R) * (∫ t, ‖fderiv ℝ (mollifierDilate ρ ε) t‖ ∂μ) =
      R * ∫ t, ‖fderiv ℝ ρ t‖ ∂μ := by
  rw [integral_norm_fderiv_mollifierDilate μ hρ hε]
  field_simp [hε.ne']

/-- Derivative convergence for the actual inverse-dimension dilations of an
arbitrary fixed smooth compact mass-one kernel. The scale is positive and
converges to zero along any filter. -/
theorem tendsto_fderiv_mollifierDilate_convolution
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hεt : Tendsto ε l (𝓝 0))
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hmass : ∫ t, ρ t ∂μ = 1) (hf : Continuous f)
    {x : E} {L : E →L[ℝ] ℝ} (hfx : HasFDerivAt f L x) :
    Tendsto (fun i ↦
      fderiv ℝ (mollifierDilate ρ (ε i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x)
      l (𝓝 L) := by
  obtain ⟨R, hR, hs⟩ := hρc.isBounded.subset_closedBall_lt 0 (0 : E)
  apply tendsto_fderiv_mollifier_family μ (fun i ↦ mollifierDilate ρ (ε i)) (fun i ↦ ε i * R)
    (fun i ↦ hasCompactSupport_mollifierDilate hρc (hε i))
    (fun i ↦ contDiff_mollifierDilate hρ (ε i))
    (fun i ↦ (integral_mollifierDilate μ (hε i)).trans hmass)
    (fun i ↦ tsupport_mollifierDilate_subset (hε i) hs)
    (fun i ↦ mul_nonneg (hε i).le hR.le)
    (by simpa only [zero_mul] using hεt.mul_const R)
    (C := R * ∫ t, ‖fderiv ℝ ρ t‖ ∂μ)
    (mul_nonneg hR.le (integral_nonneg (fun t ↦ norm_nonneg _)))
    (fun i ↦ (radius_mul_integral_norm_fderiv_mollifierDilate μ hρ (hε i) R).le)
    hf hfx

/-- Exact Lipschitz-constant preservation for the same scaled kernels. -/
theorem lipschitzWith_mollifierDilate_convolution {K : ℝ≥0}
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hρnonneg : ∀ t, 0 ≤ ρ t) (hmass : ∫ t, ρ t ∂μ = 1)
    (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith K (mollifierDilate ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) := by
  exact lipschitzWith_probability_convolution (hasCompactSupport_mollifierDilate hρc hε)
    ((contDiff_mollifierDilate hρ ε).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifierDilate hρc hε))
    (mollifierDilate_nonneg hρnonneg hε) ((integral_mollifierDilate μ hε).trans hmass) hf

theorem norm_fderiv_mollifierDilate_convolution_le {K : ℝ≥0}
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hρnonneg : ∀ t, 0 ≤ ρ t) (hmass : ∫ t, ρ t ∂μ = 1)
    (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (mollifierDilate ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x‖ ≤ (K : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ
    (lipschitzWith_mollifierDilate_convolution μ hρc hρ hρnonneg hmass hf hε)

theorem contDiff_mollifierDilate_convolution
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (mollifierDilate ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) :=
  (hasCompactSupport_mollifierDilate hρc hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (contDiff_mollifierDilate hρ ε) hf.locallyIntegrable

end FiniteDimensional

/-- The requested Euclidean specialization, including smoothness at every
positive scale, the original Lipschitz bound, and the genuine pointwise
ordinary-derivative limit at every differentiability point. -/
theorem euclidean_mollifier_derivative_limit
    {J : Type*} [Fintype J] {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    {ρ f : EuclideanSpace ℝ J → ℝ} {K : ℝ≥0}
    (hε : ∀ i, 0 < ε i) (hεt : Tendsto ε l (𝓝 0))
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ)
    (hρnonneg : ∀ t, 0 ≤ ρ t) (hmass : ∫ t, ρ t = 1) (hf : LipschitzWith K f) :
    (∀ i, ContDiff ℝ ∞
      (mollifierDilate ρ (ε i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)) ∧
    (∀ i x, ‖fderiv ℝ
      (mollifierDilate ρ (ε i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖ ≤ (K : ℝ)) ∧
    ∀ x, DifferentiableAt ℝ f x →
      Tendsto (fun i ↦ fderiv ℝ
        (mollifierDilate ρ (ε i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x)
        l (𝓝 (fderiv ℝ f x)) := by
  refine ⟨fun i ↦ contDiff_mollifierDilate_convolution volume hρc hρ hf.continuous (hε i),
    fun i x ↦ norm_fderiv_mollifierDilate_convolution_le volume hρc hρ hρnonneg hmass hf (hε i) x,
    ?_⟩
  intro x hx
  exact tendsto_fderiv_mollifierDilate_convolution volume hε hεt hρc hρ hmass hf.continuous
    hx.hasFDerivAt

end PeriodicAttractiveLogGas
