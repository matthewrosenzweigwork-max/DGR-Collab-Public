import LeanResearch.PeriodicAttractiveLogGas.ConfigurationRademacher
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationMollifier
import LeanResearch.PeriodicAttractiveLogGas.MollifierDerivativeLimit
import LeanResearch.PeriodicAttractiveLogGas.GreenAmbientDomain
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The Lipschitz-inclusion paragraph of source Proposition 2.6.

The explicit sequence of smooth configuration convolutions uses scales
`1 / (n + 1)`. Its scalar error is bounded by `K` times the scale, and each
ordinary Euclidean gradient is bounded by the original Lipschitz constant
`K`. Rademacher, the actual derivative-convolution limit, and absolute
continuity give almost-everywhere gradient convergence. Dominated convergence
of squared errors then gives strong convergence of the actual scalar and
vector L2 classes for every finite measure absolutely continuous with respect
to the reference measure.

The Lipschitz hypothesis is explicitly on the ordinary lift to `Gradient N`,
with its Euclidean norm on all `2 * N` coordinates. It is the condition for
the intended Euclidean quotient Lipschitz bound. It is not stated using, or
identified with, the existing default Pi supremum metric on `Configuration N`.

This constructs a member of the actual closed smooth gradient graph. For the
specified subcritical Green probability law, the previously proved ambient
weak-gradient theorem identifies its gradient under the unweighted reference
measure. The pointwise gradient is the physical Riesz vector on `Gradient N`;
the energy is the unscaled sum of the `2 * N` coordinate squares. This file
does not assert the Markov property or the logarithmic Sobolev inequality.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff Convolution BigOperators

namespace PeriodicAttractiveLogGas

/-- A bounded-error version of dominated convergence for genuine L2 classes.
The explicit AE representative equalities keep all quotient identifications
separate from the pointwise convergence argument. -/
theorem tendsto_L2_of_bounded_pointwise_error
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {F : ℕ → α → E} {g : α → E} {U : ℕ → Lp E 2 μ} {v : Lp E 2 μ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hg : AEStronglyMeasurable g μ)
    (hU : ∀ n, U n =ᵐ[μ] F n) (hv : v =ᵐ[μ] g)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x - g x‖ ≤ B)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (g x))) :
    Tendsto U atTop (𝓝 v) := by
  have hdct : Tendsto (fun n ↦ ∫ x, ‖F n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x ↦ ‖F n x - g x‖ ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ B ^ 2)
      (fun n ↦ ((hF n).sub hg).norm.pow 2) (integrable_const _)
      (fun n ↦ (hbound n).mono (fun x hx ↦ by
        change |‖F n x - g x‖ ^ 2| ≤ B ^ 2
        rw [abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_sq₀ (norm_nonneg _) hB).mpr hx))
      (ht.mono (fun x hx ↦ by
        simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
          ((hx.sub (tendsto_const_nhds :
            Tendsto (fun _ : ℕ ↦ g x) atTop (𝓝 (g x)))).norm.pow 2)))
    simpa only [integral_zero] using h
  have heq (n : ℕ) : ‖U n - v‖ ^ 2 = ∫ x, ‖F n x - g x‖ ^ 2 ∂μ := by
    have hi : (∫ x, ‖(U n - v) x‖ ^ 2 ∂μ) = ‖U n - v‖ ^ 2 := by
      simpa only [L2.inner_def, real_inner_self_eq_norm_sq] using real_inner_self_eq_norm_sq (U n - v)
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U n) v, hU n, hv] with x hsub h1 h2
    simp only [hsub, Pi.sub_apply, h1, h2]
  have hsq : Tendsto (fun n ↦ ‖U n - v‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq] using hdct
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

def configurationSmoothingScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem configurationSmoothingScale_pos (n : ℕ) : 0 < configurationSmoothingScale n := by
  unfold configurationSmoothingScale
  positivity

theorem configurationSmoothingScale_le_one (n : ℕ) : configurationSmoothingScale n ≤ 1 := by
  unfold configurationSmoothingScale
  apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem tendsto_configurationSmoothingScale :
    Tendsto configurationSmoothingScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def configurationLipschitzSmoothApprox {N : ℕ} (f : C(Configuration N, ℝ))
    (n : ℕ) : SmoothPair N :=
  configurationMollifiedSmoothPair (configurationSmoothingScale n)
    (configurationSmoothingScale_pos n) f

/-- The concrete configuration kernel is exactly the inverse-dimension
dilation to which the checked Taylor-remainder theorem applies. -/
theorem scaledConfigurationMollifier_eq_mollifierDilate (N : ℕ) (ε : ℝ) :
    scaledConfigurationMollifier N ε = mollifierDilate (configurationMollifier N) ε := by
  funext x
  simp only [scaledConfigurationMollifier, mollifierDilate, finrank_configurationGradient]

theorem configurationMollifiedSmoothPair_gradient_eq_riesz {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) (X : Configuration N) :
    (configurationMollifiedSmoothPair ε hε f).gradient X =
      (InnerProductSpace.toDual ℝ (Gradient N)).symm
        (fderiv ℝ (scaledConfigurationMollifier N ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun y ↦ f (configurationQuotient N y))) (configurationCenteredLift X)) := by
  have h := (configurationMollifiedSmoothPair ε hε f).gradient_configurationQuotient_eq_riesz
    (configurationCenteredLift X)
  simpa only [configurationQuotient_centeredLift, configurationMollifiedSmoothPair_value,
    configurationMollification_lift] using h

theorem norm_configurationMollifiedSmoothPair_gradient_le {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) (X : Configuration N) :
    ‖(configurationMollifiedSmoothPair ε hε f).gradient X‖ ≤ (K : ℝ) := by
  rw [configurationMollifiedSmoothPair_gradient_eq_riesz,
    (InnerProductSpace.toDual ℝ (Gradient N)).symm.norm_map]
  exact norm_fderiv_probability_convolution_le
    (hasCompactSupport_scaledConfigurationMollifier N ε hε)
    (integrable_scaledConfigurationMollifier N ε hε)
    (scaledConfigurationMollifier_nonneg N ε) (integral_scaledConfigurationMollifier N ε hε)
    hf (configurationCenteredLift X)

theorem norm_configurationMollifiedSmoothPair_value_sub_le {N : ℕ}
    (ε : ℝ) (hε : 0 < ε) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) (X : Configuration N) :
    ‖(configurationMollifiedSmoothPair ε hε f).value X - f X‖ ≤ (K : ℝ) * ε := by
  have h := dist_probability_convolution_le
    (hasCompactSupport_scaledConfigurationMollifier N ε hε)
    (integrable_scaledConfigurationMollifier N ε hε)
    (scaledConfigurationMollifier_nonneg N ε) (integral_scaledConfigurationMollifier N ε hε)
    hf hε.le (support_scaledConfigurationMollifier_subset_scale N ε hε)
    (configurationCenteredLift X)
  simpa only [← configurationMollification_lift ε hε f, configurationQuotient_centeredLift,
    dist_eq_norm, configurationMollifiedSmoothPair_value] using h

theorem tendsto_configurationLipschitzSmoothApprox_value {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) (X : Configuration N) :
    Tendsto (fun n ↦ (configurationLipschitzSmoothApprox f n).value X) atTop (𝓝 (f X)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ norm_configurationMollifiedSmoothPair_value_sub_le _
      (configurationSmoothingScale_pos n) f hf X)
  simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_configurationSmoothingScale

theorem tendsto_configurationLipschitzSmoothApprox_gradient_at {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) {X : Configuration N}
    (hX : DifferentiableAt ℝ (fun y ↦ f (configurationQuotient N y))
      (configurationCenteredLift X)) :
    Tendsto (fun n ↦ (configurationLipschitzSmoothApprox f n).gradient X) atTop
      (𝓝 (descendedLiftGradient f X)) := by
  have hder := (euclidean_mollifier_derivative_limit configurationSmoothingScale_pos
    tendsto_configurationSmoothingScale (hasCompactSupport_configurationMollifier N)
    (contDiff_configurationMollifier N) (configurationMollifier_nonneg N)
    (integral_configurationMollifier N) hf).2.2 (configurationCenteredLift X) hX
  have hder' : Tendsto (fun n ↦ fderiv ℝ
      (scaledConfigurationMollifier N (configurationSmoothingScale n)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun y ↦ f (configurationQuotient N y))) (configurationCenteredLift X)) atTop
      (𝓝 (fderiv ℝ (fun y ↦ f (configurationQuotient N y)) (configurationCenteredLift X))) := by
    simpa only [scaledConfigurationMollifier_eq_mollifierDilate] using hder
  have ht := ((InnerProductSpace.toDual ℝ (Gradient N)).symm.continuous.tendsto
    (fderiv ℝ (fun y ↦ f (configurationQuotient N y)) (configurationCenteredLift X))).comp hder'
  simpa only [Function.comp_def, configurationLipschitzSmoothApprox,
    configurationMollifiedSmoothPair_gradient_eq_riesz, descendedLiftGradient_eq_riesz_differential,
    descendedLiftDifferential] using ht

theorem ae_tendsto_configurationLipschitzSmoothApprox_gradient {N : ℕ}
    (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∀ᵐ X ∂μ, Tendsto (fun n ↦ (configurationLipschitzSmoothApprox f n).gradient X) atTop
      (𝓝 (descendedLiftGradient f X)) := by
  have hdiff : ∀ᵐ X ∂μ, DifferentiableAt ℝ
      (fun y ↦ f (configurationQuotient N y)) (configurationCenteredLift X) :=
    hμ.ae_le (ae_differentiableAt_configurationLift_centered f hf)
  exact hdiff.mono
    (fun _ hX ↦ tendsto_configurationLipschitzSmoothApprox_gradient_at f hf hX)

theorem tendsto_configurationLipschitzSmoothApprox_value_L2 {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (configurationLipschitzSmoothApprox f n).value)
      atTop (𝓝 (ContinuousMap.toLp 2 μ ℝ f)) := by
  apply tendsto_L2_of_bounded_pointwise_error
    (F := fun n X ↦ (configurationLipschitzSmoothApprox f n).value X) (g := f)
    (fun n ↦ (configurationLipschitzSmoothApprox f n).value.continuous.aestronglyMeasurable)
    f.continuous.aestronglyMeasurable
    (fun n ↦ ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ
      (configurationLipschitzSmoothApprox f n).value)
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f) K.coe_nonneg
  · intro n
    exact Eventually.of_forall (fun X ↦
      (norm_configurationMollifiedSmoothPair_value_sub_le _ (configurationSmoothingScale_pos n)
        f hf X).trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (configurationSmoothingScale_le_one n) K.coe_nonneg))
  · exact Eventually.of_forall (tendsto_configurationLipschitzSmoothApprox_value f hf)

theorem tendsto_configurationLipschitzSmoothApprox_gradient_L2 {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (configurationLipschitzSmoothApprox f n).gradient)
      atTop (𝓝 (configurationLipschitzGradientL2 μ f hf)) := by
  apply tendsto_L2_of_bounded_pointwise_error
    (F := fun n X ↦ (configurationLipschitzSmoothApprox f n).gradient X)
    (g := descendedLiftGradient f)
    (fun n ↦ (configurationLipschitzSmoothApprox f n).gradient.continuous.aestronglyMeasurable)
    (measurable_descendedLiftGradient f).aestronglyMeasurable
    (fun n ↦ ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ
      (configurationLipschitzSmoothApprox f n).gradient)
    (configurationLipschitzGradientL2_coe μ f hf) (B := 2 * (K : ℝ)) (by positivity)
  · intro n
    refine Eventually.of_forall (fun X ↦ ?_)
    calc
      ‖(configurationLipschitzSmoothApprox f n).gradient X - descendedLiftGradient f X‖ ≤
          ‖(configurationLipschitzSmoothApprox f n).gradient X‖ + ‖descendedLiftGradient f X‖ :=
        norm_sub_le _ _
      _ ≤ (K : ℝ) + K := add_le_add
        (norm_configurationMollifiedSmoothPair_gradient_le _ (configurationSmoothingScale_pos n)
          f hf X) (norm_descendedLiftGradient_le f hf X)
      _ = 2 * (K : ℝ) := by ring
  · exact ae_tendsto_configurationLipschitzSmoothApprox_gradient μ hμ f hf

/-- The approximations converge in the genuine product scalar/vector L2
topology used to define the closed ambient graph. -/
theorem tendsto_configurationLipschitzSmoothApprox_pair {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    Tendsto (fun n ↦
      (ContinuousMap.toLp 2 μ ℝ (configurationLipschitzSmoothApprox f n).value,
        ContinuousMap.toLp 2 μ ℝ (configurationLipschitzSmoothApprox f n).gradient))
      atTop (𝓝 (ContinuousMap.toLp 2 μ ℝ f, configurationLipschitzGradientL2 μ f hf)) :=
  (tendsto_configurationLipschitzSmoothApprox_value_L2 μ f hf).prodMk_nhds
    (tendsto_configurationLipschitzSmoothApprox_gradient_L2 μ hμ f hf)

theorem configurationLipschitz_pair_mem_closedGradientGraph {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    (ContinuousMap.toLp 2 μ ℝ f, configurationLipschitzGradientL2 μ f hf) ∈
      closedGradientGraph N μ :=
  mem_closure_of_tendsto (tendsto_configurationLipschitzSmoothApprox_pair μ hμ f hf)
    (Eventually.of_forall (fun n ↦ ⟨configurationLipschitzSmoothApprox f n, rfl⟩))

def configurationLipschitzAmbient {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) : AmbientFormDomain N μ :=
  ⟨(ContinuousMap.toLp 2 μ ℝ f, configurationLipschitzGradientL2 μ f hf),
    configurationLipschitz_pair_mem_closedGradientGraph μ hμ f hf⟩

@[simp] theorem configurationLipschitzAmbient_value {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ambientValue (configurationLipschitzAmbient μ hμ f hf) = ContinuousMap.toLp 2 μ ℝ f := rfl

@[simp] theorem configurationLipschitzAmbient_gradient {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ambientGradient (configurationLipschitzAmbient μ hμ f hf) =
      configurationLipschitzGradientL2 μ f hf := rfl

theorem configurationLipschitzAmbient_value_ae {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ambientValue (configurationLipschitzAmbient μ hμ f hf) =ᵐ[μ] f :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f

theorem configurationLipschitzAmbient_gradient_ae {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ambientGradient (configurationLipschitzAmbient μ hμ f hf) =ᵐ[μ] descendedLiftGradient f :=
  configurationLipschitzGradientL2_coe μ f hf

theorem configurationLipschitzAmbient_energy_eq_integral {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ambientEnergy (configurationLipschitzAmbient μ hμ f hf) =
      ∫ X, ‖descendedLiftGradient f X‖ ^ 2 ∂μ :=
  (configurationLipschitzGradientL2_norm_sq μ f hf).symm

theorem configurationLipschitzAmbient_energy_eq_coordinate_integral {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ambientEnergy (configurationLipschitzAmbient μ hμ f hf) =
      ∫ X, ∑ i : Fin N, ∑ k : Fin 2, (descendedLiftGradient f X (i, k)) ^ 2 ∂μ := by
  rw [configurationLipschitzAmbient_energy_eq_integral]
  apply integral_congr_ae
  exact Eventually.of_forall (descendedLiftGradient_norm_sq f)

theorem configurationLipschitzAmbient_smooth_formNorm_approx {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    Tendsto (fun n ↦ graphFormNorm
      ((ContinuousMap.toLp 2 μ ℝ (configurationLipschitzSmoothApprox f n).value,
        ContinuousMap.toLp 2 μ ℝ (configurationLipschitzSmoothApprox f n).gradient) -
          (configurationLipschitzAmbient μ hμ f hf).1)) atTop (𝓝 0) :=
  tendsto_iff_graphFormNorm_sub_tendsto_zero.mp
    (tendsto_configurationLipschitzSmoothApprox_pair μ hμ f hf)

/-- Comparison of the actual L2 gradient classes preserves their common
pointwise Riesz representative. -/
theorem measureComparison_configurationLipschitzGradientL2 {N : ℕ}
    {μ ν : Measure (Configuration N)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : μ ≤ c • ν)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    Lp.LpToLpOfMeasureLeSMul hc h (configurationLipschitzGradientL2 ν f hf) =
      configurationLipschitzGradientL2 μ f hf := by
  apply Lp.ext
  have hμν : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc h _).trans
    ((hμν.ae_eq (configurationLipschitzGradientL2_coe ν f hf)).trans
      (configurationLipschitzGradientL2_coe μ f hf).symm)

/-- The actual constructed Lipschitz element for the Green Gibbs law. -/
def greenLipschitzAmbient {N : ℕ} (β : ℝ) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) : GreenAmbientFormDomain N β :=
  configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
    (gibbsMeasure_absolutelyContinuous _ N β) f hf

/-- For the actual nondegenerate subcritical Green probability law, the
ambient weak-gradient theorem identifies the physical pointwise gradient
under unweighted Haar measure. -/
theorem greenLipschitz_hasReferenceWeakGradient (N : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsubcritical : β < 4)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    HasReferenceWeakGradient N (ContinuousMap.toLp 2 (referenceMeasure N) ℝ f)
      (configurationLipschitzGradientL2 (referenceMeasure N) f hf) := by
  obtain ⟨c, hc, hb, hw⟩ := green_ambient_hasReferenceWeakGradient N hN hβ hsubcritical
  have h := hw (greenLipschitzAmbient β f hf)
  change HasReferenceWeakGradient N
    (Lp.LpToLpOfMeasureLeSMul hc hb (ContinuousMap.toLp 2
      (gibbsMeasure greenRealRepresentative N β) ℝ f))
    (Lp.LpToLpOfMeasureLeSMul hc hb (configurationLipschitzGradientL2
      (gibbsMeasure greenRealRepresentative N β) f hf)) at h
  rw [measureComparison_toLp, measureComparison_configurationLipschitzGradientL2] at h
  exact h

/-- The complete Lipschitz-inclusion assertion for the specified Green law:
actual scalar and physical gradient classes, the source energy formula, and
the ordinary unweighted weak-gradient identity. -/
theorem exists_green_lipschitz_ambient (N : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsubcritical : β < 4)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    ∃ F : GreenAmbientFormDomain N β,
      ambientValue F = ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ f ∧
      ambientGradient F = configurationLipschitzGradientL2
        (gibbsMeasure greenRealRepresentative N β) f hf ∧
      ambientEnergy F = (∫ X, ∑ i : Fin N, ∑ k : Fin 2,
        (descendedLiftGradient f X (i, k)) ^ 2 ∂gibbsMeasure greenRealRepresentative N β) ∧
      HasReferenceWeakGradient N (ContinuousMap.toLp 2 (referenceMeasure N) ℝ f)
        (configurationLipschitzGradientL2 (referenceMeasure N) f hf) := by
  refine ⟨greenLipschitzAmbient β f hf, rfl, rfl, ?_,
    greenLipschitz_hasReferenceWeakGradient N hN hβ hsubcritical f hf⟩
  exact configurationLipschitzAmbient_energy_eq_coordinate_integral
    (gibbsMeasure greenRealRepresentative N β) (gibbsMeasure_absolutelyContinuous _ N β) f hf

end PeriodicAttractiveLogGas
