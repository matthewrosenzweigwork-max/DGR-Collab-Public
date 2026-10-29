import LeanResearch.PeriodicAttractiveLogGas.GreenTorusIntegration
import LeanResearch.PeriodicAttractiveLogGas.ConvolutionYoung
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationLipschitzDomain

/-! The torus Sobolev step in source Lemma 3.1. The coefficient is the actual
finite Green-gradient norm. The smooth result uses the proved signed Green
representation and constant-one Young inequality. The Lipschitz passage uses
the actual smooth convolutions, uniform convergence of values and strong L2
convergence of physical gradients, with no additional Sobolev premise. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas

def torusSobolevConstant (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * lpNorm greenGradient (ENNReal.ofReal (youngExponent r)) torusMeasure

theorem torusSobolevConstant_nonneg (r : ℝ) : 0 ≤ torusSobolevConstant r := by
  exact mul_nonneg (by positivity) lpNorm_nonneg

/-- The real coefficient is obtained from a genuinely finite extended norm. -/
theorem torusSobolevConstant_finite {r : ℝ} (hr : 2 ≤ r) :
    eLpNorm greenGradient (ENNReal.ofReal (youngExponent r)) torusMeasure < ⊤ :=
  (memLp_greenGradient (youngExponent r) (one_le_youngExponent hr)
    (youngExponent_lt_two hr)).eLpNorm_lt_top

theorem measurePreserving_singleConfiguration :
    MeasurePreserving singleConfiguration torusMeasure (referenceMeasure 1) := by
  convert (measurePreserving_piUnique (fun _ : Fin 1 ↦ torusMeasure)).symm using 1
  · ext x i
    simp [singleConfiguration, MeasurableEquiv.piUnique]
  · rfl

theorem lpNorm_singleConfiguration {E : Type*} [NormedAddCommGroup E]
    (F : Configuration 1 → E) (p : ℝ≥0∞)
    (hF : AEStronglyMeasurable F (referenceMeasure 1)) :
    lpNorm (fun x ↦ F (singleConfiguration x)) p torusMeasure =
      lpNorm F p (referenceMeasure 1) := by
  simp only [← toReal_eLpNorm]
  congr 1
  exact eLpNorm_comp_measurePreserving hF measurePreserving_singleConfiguration

theorem SmoothPair.lpNorm_torusGradient (f : SmoothPair 1) (p : ℝ≥0∞) :
    lpNorm f.torusGradient p torusMeasure = lpNorm f.gradient p (referenceMeasure 1) := by
  rw [← lpNorm_singleConfiguration f.gradient p f.gradient.continuous.aestronglyMeasurable]
  simp only [← toReal_eLpNorm]
  congr 1
  exact eLpNorm_congr_norm_ae f.torusGradient.continuous.aestronglyMeasurable
    (f.gradient.continuous.comp (by unfold singleConfiguration; fun_prop)).aestronglyMeasurable
    (Eventually.of_forall f.torusGradient_norm)

theorem SmoothPair.torus_sobolev {r : ℝ} (hr : 2 ≤ r) (f : SmoothPair 1) :
    lpNorm (fun x ↦ f.torusValue x - ∫ z, f.torusValue z ∂torusMeasure)
        (ENNReal.ofReal r) torusMeasure ≤
      torusSobolevConstant r * lpNorm f.torusGradient 2 torusMeasure := by
  have hy := (torusInnerConvolution_greenGradient_young hr
    (ContinuousMap.memLp (μ := torusMeasure) (p := 2) ℝ f.torusGradient)).2.2
  have heq : (fun x ↦ f.torusValue x - ∫ z, f.torusValue z ∂torusMeasure) =
      (-(1 / (2 * Real.pi))) • torusInnerConvolution greenGradient f.torusGradient := by
    ext x
    exact green_gradient_convolution_representation f x
  rw [heq, lpNorm_const_smul]
  change ‖(-(1 / (2 * Real.pi)) : ℝ)‖ *
    lpNorm (torusInnerConvolution greenGradient f.torusGradient) (ENNReal.ofReal r) torusMeasure ≤ _
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  exact (mul_le_mul_of_nonneg_left hy (by positivity)).trans_eq (by
    simp only [torusSobolevConstant, mul_assoc])

theorem SmoothPair.configuration_one_sobolev {r : ℝ} (hr : 2 ≤ r) (f : SmoothPair 1) :
    lpNorm (fun X ↦ f.value X - ∫ Y, f.value Y ∂referenceMeasure 1)
        (ENNReal.ofReal r) (referenceMeasure 1) ≤
      torusSobolevConstant r * lpNorm f.gradient 2 (referenceMeasure 1) := by
  have h := f.torus_sobolev hr
  rw [f.lpNorm_torusGradient] at h
  have hm := integral_reference_one_eq_torus f.value
    (f.value.continuous.comp (by unfold singleConfiguration; fun_prop)).aestronglyMeasurable
  have hn := lpNorm_singleConfiguration
    (fun X ↦ f.value X - ∫ Y, f.value Y ∂referenceMeasure 1) (ENNReal.ofReal r)
    (f.value.continuous.aestronglyMeasurable.sub aestronglyMeasurable_const)
  rw [← hn, hm]
  exact h

theorem continuousMap_lpNorm_eq_norm_toLp
    {A E : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopologyEither A E] {μ : Measure A} [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : C(A, E)) :
    lpNorm f p μ = ‖ContinuousMap.toLp p μ ℝ f‖ := by
  rw [Lp.norm_def, ← toReal_eLpNorm,
    eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := p) (𝕜 := ℝ) μ f)]

theorem continuous_lpNorm_continuousMap
    {A E : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopologyEither A E] {μ : Measure A} [IsFiniteMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Continuous (fun f : C(A, E) ↦ lpNorm f p μ) := by
  simp_rw [continuousMap_lpNorm_eq_norm_toLp]
  exact (ContinuousMap.toLp p μ ℝ).continuous.norm

theorem tendsto_configurationLipschitzSmoothApprox_uniform {N : ℕ}
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    Tendsto (fun n ↦ (configurationLipschitzSmoothApprox f n).value) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ (ContinuousMap.norm_le _ (mul_nonneg K.coe_nonneg
      (configurationSmoothingScale_pos n).le)).mpr (fun X ↦
        norm_configurationMollifiedSmoothPair_value_sub_le _
          (configurationSmoothingScale_pos n) f hf X))
  simpa only [mul_zero] using
    (tendsto_configurationSmoothingScale.const_mul (K : ℝ))

def continuousMapCenter {A : Type*} [TopologicalSpace A] [MeasurableSpace A]
    (μ : Measure A) (f : C(A, ℝ)) : C(A, ℝ) :=
  f - ContinuousMap.const A (∫ x, f x ∂μ)

theorem norm_continuousMapCenter_sub_le
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (f g : C(A, ℝ)) :
    ‖continuousMapCenter μ f - continuousMapCenter μ g‖ ≤ 2 * ‖f - g‖ := by
  have hi : ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ ‖f - g‖ := by
    rw [← integral_sub ((ContinuousMap.memLp (μ := μ) (p := 1) ℝ f).integrable le_rfl)
      ((ContinuousMap.memLp (μ := μ) (p := 1) ℝ g).integrable le_rfl)]
    simpa using norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall (f - g).norm_coe_le_norm)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖(f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ)‖ ≤ _
  rw [show (f x - ∫ y, f y ∂μ) - (g x - ∫ y, g y ∂μ) =
    (f x - g x) - ((∫ y, f y ∂μ) - ∫ y, g y ∂μ) by ring]
  exact (norm_sub_le _ _).trans ((add_le_add ((f - g).norm_coe_le_norm x) hi).trans_eq
    (by ring))

theorem continuous_continuousMapCenter
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] : Continuous (continuousMapCenter μ) := by
  apply (show LipschitzWith 2 (continuousMapCenter μ) from ?_).continuous
  rw [lipschitzWith_iff_dist_le_mul]
  intro f g
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using norm_continuousMapCenter_sub_le μ f g

/-- Smooth convolution proves the estimate for every Lipschitz one-particle
configuration lift, with the actual descended physical gradient. -/
theorem configuration_lipschitz_sobolev {r : ℝ} (hr : 2 ≤ r)
    (f : C(Configuration 1, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient 1 y))) :
    lpNorm (fun X ↦ f X - ∫ Y, f Y ∂referenceMeasure 1)
        (ENNReal.ofReal r) (referenceMeasure 1) ≤
      torusSobolevConstant r * lpNorm (descendedLiftGradient f) 2 (referenceMeasure 1) := by
  have hp : 1 ≤ ENNReal.ofReal r := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ r))
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨hp⟩
  have hc := (continuous_continuousMapCenter (referenceMeasure 1)).tendsto f |>.comp
    (tendsto_configurationLipschitzSmoothApprox_uniform f hf)
  have hl := (continuous_lpNorm_continuousMap (μ := referenceMeasure 1)
    (ENNReal.ofReal r)).tendsto (continuousMapCenter (referenceMeasure 1) f) |>.comp hc
  have hg := (tendsto_configurationLipschitzSmoothApprox_gradient_L2
    (referenceMeasure 1) (Measure.AbsolutelyContinuous.refl _) f hf).norm
  have hg' : Tendsto
      (fun n ↦ lpNorm (configurationLipschitzSmoothApprox f n).gradient 2 (referenceMeasure 1))
      atTop (𝓝 (lpNorm (descendedLiftGradient f) 2 (referenceMeasure 1))) := by
    simpa only [continuousMap_lpNorm_eq_norm_toLp, configurationLipschitzGradientL2,
      Lp.norm_toLp, toReal_eLpNorm] using hg
  exact le_of_tendsto_of_tendsto hl (hg'.const_mul (torusSobolevConstant r))
    (Eventually.of_forall (fun n ↦
      (configurationLipschitzSmoothApprox f n).configuration_one_sobolev hr))

def torusConfigurationValue (f : C(Torus, ℝ)) : C(Configuration 1, ℝ) :=
  ⟨fun X ↦ f (X 0), by fun_prop⟩

theorem isometry_firstParticleCoordinates : Isometry firstParticleCoordinates := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, ← map_sub, firstParticleCoordinates_norm, dist_eq_norm]

theorem lipschitz_torusConfigurationValue_lift (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (torusQuotient y))) :
    LipschitzWith K (fun y ↦ torusConfigurationValue f (configurationQuotient 1 y)) := by
  simpa only [mul_one] using! hf.comp isometry_firstParticleCoordinates.lipschitzWith

/-- The genuine planar Riesz gradient, obtained from the previously proved
single full-measure set of ordinary configuration derivatives. -/
def torusLiftGradient (f : C(Torus, ℝ)) (x : Torus) : PlanarSpace :=
  firstParticleCoordinates (descendedLiftGradient (torusConfigurationValue f) (singleConfiguration x))

theorem measurable_torusLiftGradient (f : C(Torus, ℝ)) : Measurable (torusLiftGradient f) :=
  firstParticleCoordinates.continuous.measurable.comp
    ((measurable_descendedLiftGradient (torusConfigurationValue f)).comp
      measurePreserving_singleConfiguration.measurable)

theorem torusLiftGradient_norm (f : C(Torus, ℝ)) (x : Torus) :
    ‖torusLiftGradient f x‖ =
      ‖descendedLiftGradient (torusConfigurationValue f) (singleConfiguration x)‖ :=
  firstParticleCoordinates_norm _

theorem ae_hasFDerivAt_torusLiftGradient (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (torusQuotient y))) :
    ∀ᵐ x ∂torusMeasure, ∀ y : PlanarSpace, torusQuotient y = x →
      HasFDerivAt (fun z ↦ f (torusQuotient z)) (innerSL ℝ (torusLiftGradient f x)) y := by
  have hfull := measurePreserving_singleConfiguration.quasiMeasurePreserving.ae
    (ae_hasFDerivAt_configurationLift_descendedGradient (torusConfigurationValue f)
      (lipschitz_torusConfigurationValue_lift f hf))
  filter_upwards [hfull] with x hx
  intro y hy
  have hd := (hx (singleParticleCoordinates y) (by
    rw [configurationQuotient_singleParticleCoordinates, hy])).comp y
      singleParticleCoordinatesL.hasFDerivAt
  convert hd using 1
  · ext z
    rfl
  · ext v
    exact inner_firstParticleCoordinates _ v

theorem torusLiftGradient_memLp (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (torusQuotient y))) :
    MemLp (torusLiftGradient f) 2 torusMeasure := by
  apply MemLp.of_bound (measurable_torusLiftGradient f).aestronglyMeasurable (K : ℝ)
  filter_upwards with x
  rw [torusLiftGradient_norm]
  exact norm_descendedLiftGradient_le _ (lipschitz_torusConfigurationValue_lift f hf) _

theorem lpNorm_torusLiftGradient (f : C(Torus, ℝ)) (p : ℝ≥0∞) :
    lpNorm (torusLiftGradient f) p torusMeasure =
      lpNorm (descendedLiftGradient (torusConfigurationValue f)) p (referenceMeasure 1) := by
  rw [← lpNorm_singleConfiguration _ p
    (measurable_descendedLiftGradient (torusConfigurationValue f)).aestronglyMeasurable]
  simp only [← toReal_eLpNorm]
  congr 1
  exact eLpNorm_congr_norm_ae (measurable_torusLiftGradient f).aestronglyMeasurable
    ((measurable_descendedLiftGradient (torusConfigurationValue f)).comp
      measurePreserving_singleConfiguration.measurable).aestronglyMeasurable
    (Eventually.of_forall (torusLiftGradient_norm f))

/-- The source torus inequality for every real Lipschitz function, including
the endpoint r=2, with exactly the finite Green norm specified in the paper. -/
theorem torus_lipschitz_sobolev {r : ℝ} (hr : 2 ≤ r) (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (torusQuotient y))) :
    lpNorm (fun x ↦ f x - ∫ z, f z ∂torusMeasure) (ENNReal.ofReal r) torusMeasure ≤
      torusSobolevConstant r * lpNorm (torusLiftGradient f) 2 torusMeasure := by
  have h := configuration_lipschitz_sobolev hr (torusConfigurationValue f)
    (lipschitz_torusConfigurationValue_lift f hf)
  rw [← lpNorm_torusLiftGradient f 2] at h
  have hm := integral_reference_one_eq_torus (torusConfigurationValue f)
    f.continuous.aestronglyMeasurable
  have hn := lpNorm_singleConfiguration
    (fun X ↦ torusConfigurationValue f X -
      ∫ Y, torusConfigurationValue f Y ∂referenceMeasure 1) (ENNReal.ofReal r)
    ((torusConfigurationValue f).continuous.aestronglyMeasurable.sub aestronglyMeasurable_const)
  rw [← hn, hm] at h
  exact h

end PeriodicAttractiveLogGas
