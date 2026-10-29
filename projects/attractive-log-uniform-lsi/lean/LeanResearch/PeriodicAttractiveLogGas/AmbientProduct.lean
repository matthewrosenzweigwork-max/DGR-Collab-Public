import LeanResearch.PeriodicAttractiveLogGas.ConfigurationLipschitzDomain
import LeanResearch.PeriodicAttractiveLogGas.BoundedFieldL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Mul

/-! Source Lemma 2.7, the product assertion and its exact energy bound.

The cutoff is Lipschitz in the physical Euclidean metric on the configuration
cover. The compact quotient supplies its actual supremum norm. The proof first
multiplies genuine smooth approximants, identifies their ordinary almost-
everywhere Riesz gradients, and then passes to the closed scalar/vector L2
graph using bounded multiplication operators. It does not identify the domain
with a maximal weighted Sobolev space or assume a product rule for that domain.

The support and entropy assertions of Lemma 2.7 are outside this file. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas

section ScalarMultiplication

variable {N : ℕ} (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (χ : C(Configuration N, ℝ))

def ambientScalarMultiplicationField (X : Configuration N) : E →L[ℝ] E :=
  χ X • ContinuousLinearMap.id ℝ E

theorem continuous_ambientScalarMultiplicationField :
    Continuous (ambientScalarMultiplicationField E χ) :=
  χ.continuous.smul continuous_const

theorem norm_ambientScalarMultiplicationField_le (X : Configuration N) :
    ‖ambientScalarMultiplicationField E χ X‖ ≤ ‖χ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg χ)
  intro v
  simpa only [ambientScalarMultiplicationField, smul_apply,
    ContinuousLinearMap.id_apply, norm_smul] using
    mul_le_mul_of_nonneg_right (χ.norm_coe_le_norm X) (norm_nonneg v)

/-- The same scalar multiplier acts on scalar or physical Euclidean vector L2.
Its bound is the compact continuous-map norm, independently of the measure. -/
def ambientScalarL2 (μ : Measure (Configuration N)) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  boundedFieldL2CLM (ambientScalarMultiplicationField E χ)
    (continuous_ambientScalarMultiplicationField E χ).aestronglyMeasurable
    (norm_ambientScalarMultiplicationField_le E χ)

theorem ambientScalarL2_coe (μ : Measure (Configuration N)) (v : Lp E 2 μ) :
    ambientScalarL2 E χ μ v =ᵐ[μ] (fun X ↦ χ X • v X) := by
  simpa only [ambientScalarL2, ambientScalarMultiplicationField,
    smul_apply, ContinuousLinearMap.id_apply] using
    boundedFieldL2CLM_coe (ambientScalarMultiplicationField E χ)
      (continuous_ambientScalarMultiplicationField E χ).aestronglyMeasurable
      (norm_ambientScalarMultiplicationField_le E χ) v

theorem norm_ambientScalarL2_le (μ : Measure (Configuration N)) (v : Lp E 2 μ) :
    ‖ambientScalarL2 E χ μ v‖ ≤ ‖χ‖ * ‖v‖ :=
  norm_boundedFieldL2_le (ambientScalarMultiplicationField E χ)
    (continuous_ambientScalarMultiplicationField E χ).aestronglyMeasurable
    (norm_ambientScalarMultiplicationField_le E χ) v

end ScalarMultiplication

section GradientMultiplication

variable {N : ℕ} (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
  (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y)))

def ambientCutoffGradientField (X : Configuration N) : ℝ →L[ℝ] Gradient N :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Gradient N)) (descendedLiftGradient χ X)

theorem aestronglyMeasurable_ambientCutoffGradientField (μ : Measure (Configuration N)) :
    AEStronglyMeasurable (ambientCutoffGradientField χ) μ :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Gradient N)).continuous.comp_aestronglyMeasurable
    (measurable_descendedLiftGradient χ).aestronglyMeasurable

include hχ in
theorem norm_ambientCutoffGradientField_le (X : Configuration N) :
    ‖ambientCutoffGradientField χ X‖ ≤ (K : ℝ) := by
  rw [ambientCutoffGradientField,
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Gradient N)).norm_map]
  exact norm_descendedLiftGradient_le χ hχ X

/-- Multiplication by the actual Riesz gradient of the cutoff. The operator
norm bound is the original Euclidean Lipschitz constant. -/
def ambientCutoffGradientL2 (μ : Measure (Configuration N)) :
    Lp ℝ 2 μ →L[ℝ] Lp (Gradient N) 2 μ :=
  boundedFieldL2CLM (ambientCutoffGradientField χ)
    (aestronglyMeasurable_ambientCutoffGradientField χ μ)
    (norm_ambientCutoffGradientField_le χ hχ)

theorem ambientCutoffGradientL2_coe (μ : Measure (Configuration N)) (v : Lp ℝ 2 μ) :
    ambientCutoffGradientL2 χ hχ μ v =ᵐ[μ]
      (fun X ↦ v X • descendedLiftGradient χ X) := by
  simpa only [ambientCutoffGradientL2, ambientCutoffGradientField,
    ContinuousLinearMap.toSpanSingletonLIE_apply, ContinuousLinearMap.toSpanSingleton_apply] using
    boundedFieldL2CLM_coe (ambientCutoffGradientField χ)
      (aestronglyMeasurable_ambientCutoffGradientField χ μ)
      (norm_ambientCutoffGradientField_le χ hχ) v

theorem norm_ambientCutoffGradientL2_le (μ : Measure (Configuration N)) (v : Lp ℝ 2 μ) :
    ‖ambientCutoffGradientL2 χ hχ μ v‖ ≤ (K : ℝ) * ‖v‖ :=
  norm_boundedFieldL2_le (ambientCutoffGradientField χ)
    (aestronglyMeasurable_ambientCutoffGradientField χ μ)
    (norm_ambientCutoffGradientField_le χ hχ) v

end GradientMultiplication

/-- Compactness bounds the genuine continuous gradient of a smooth core
element; the Euclidean mean value theorem gives a global Lipschitz lift. -/
theorem SmoothPair.lipschitz_configurationLift {N : ℕ} (s : SmoothPair N) :
    LipschitzWith ‖s.gradient‖₊ (fun y ↦ s.value (configurationQuotient N y)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (s.smooth.differentiable (by simp))
  intro y
  have h : ‖fderiv ℝ (fun w ↦ s.value (configurationQuotient N w)) y‖ ≤ ‖s.gradient‖ := by
    rw [(s.differential y).fderiv, innerSL_apply_norm]
    exact s.gradient.norm_coe_le_norm _
  exact_mod_cast h

/-- A bounded Lipschitz cutoff times a smooth core element has a globally
Lipschitz Euclidean lift. This auxiliary constant need not be uniform in `s`. -/
theorem lipschitz_configurationLift_cutoff_mul_smooth {N : ℕ}
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y))) (s : SmoothPair N) :
    LipschitzWith (‖χ‖₊ * ‖s.gradient‖₊ + K * ‖s.value‖₊)
      (fun y ↦ (χ * s.value) (configurationQuotient N y)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro y z
  change ‖χ (configurationQuotient N y) * s.value (configurationQuotient N y) -
      χ (configurationQuotient N z) * s.value (configurationQuotient N z)‖ ≤ _
  calc
    _ = ‖χ (configurationQuotient N y) *
        (s.value (configurationQuotient N y) - s.value (configurationQuotient N z)) +
        (χ (configurationQuotient N y) - χ (configurationQuotient N z)) *
          s.value (configurationQuotient N z)‖ := by congr 1; ring
    _ ≤ ‖χ (configurationQuotient N y) *
        (s.value (configurationQuotient N y) - s.value (configurationQuotient N z))‖ +
        ‖(χ (configurationQuotient N y) - χ (configurationQuotient N z)) *
          s.value (configurationQuotient N z)‖ := norm_add_le _ _
    _ = ‖χ (configurationQuotient N y)‖ *
        ‖s.value (configurationQuotient N y) - s.value (configurationQuotient N z)‖ +
        ‖χ (configurationQuotient N y) - χ (configurationQuotient N z)‖ *
          ‖s.value (configurationQuotient N z)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖χ‖ * (‖s.gradient‖ * ‖y - z‖) + ((K : ℝ) * ‖y - z‖) * ‖s.value‖ :=
      add_le_add
        (mul_le_mul (χ.norm_coe_le_norm _)
          (lipschitzWith_iff_norm_sub_le.mp s.lipschitz_configurationLift y z)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (lipschitzWith_iff_norm_sub_le.mp hχ y z)
          (s.value.norm_coe_le_norm _) (norm_nonneg _) (by positivity))
    _ = _ := by
      change _ = (‖χ‖ * ‖s.gradient‖ + (K : ℝ) * ‖s.value‖) * ‖y - z‖
      ring

/-- The smooth-factor product rule is obtained from the ordinary Fréchet
product rule on the Euclidean cover and transferred on the actual full set. -/
theorem ae_descendedLiftGradient_cutoff_mul_smooth {N : ℕ}
    (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y))) (s : SmoothPair N) :
    descendedLiftGradient (χ * s.value) =ᵐ[μ]
      (fun X ↦ χ X • s.gradient X + s.value X • descendedLiftGradient χ X) := by
  filter_upwards [ae_hasFDerivAt_configurationLift_of_absolutelyContinuous χ hχ hμ] with X hX
  have hd := ((hX (configurationCenteredLift X) (configurationQuotient_centeredLift X)).mul
    (s.differential (configurationCenteredLift X))).fderiv
  apply ext_inner_right ℝ
  intro v
  rw [descendedLiftGradient_eq_riesz_differential, InnerProductSpace.toDual_symm_apply]
  change fderiv ℝ ((fun y ↦ χ (configurationQuotient N y)) *
      (fun y ↦ s.value (configurationQuotient N y)))
      (configurationCenteredLift X) v = _
  rw [hd]
  simp only [add_apply, smul_apply,
    innerSL_apply_apply, configurationQuotient_centeredLift,
    inner_add_left, real_inner_smul_left, smul_eq_mul]

/-- Each product with a genuine smooth approximant lies in the actual closed
graph, with both coordinates identified as bounded multiplication operators. -/
theorem cutoff_mul_smooth_pair_mem_closedGradientGraph {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y))) (s : SmoothPair N) :
    (ambientScalarL2 ℝ χ μ (ContinuousMap.toLp 2 μ ℝ s.value),
      ambientScalarL2 (Gradient N) χ μ (ContinuousMap.toLp 2 μ ℝ s.gradient) +
        ambientCutoffGradientL2 χ hχ μ (ContinuousMap.toLp 2 μ ℝ s.value)) ∈
      closedGradientGraph N μ := by
  have hprod := lipschitz_configurationLift_cutoff_mul_smooth χ hχ s
  have hv : ambientScalarL2 ℝ χ μ (ContinuousMap.toLp 2 μ ℝ s.value) =
      ContinuousMap.toLp 2 μ ℝ (χ * s.value) := by
    apply Lp.ext
    filter_upwards [ambientScalarL2_coe ℝ χ μ (ContinuousMap.toLp 2 μ ℝ s.value),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ s.value,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (χ * s.value)] with X hmul hs hp
    simp only [hmul, hs, hp, ContinuousMap.mul_apply, smul_eq_mul]
  have hg : ambientScalarL2 (Gradient N) χ μ (ContinuousMap.toLp 2 μ ℝ s.gradient) +
        ambientCutoffGradientL2 χ hχ μ (ContinuousMap.toLp 2 μ ℝ s.value) =
      configurationLipschitzGradientL2 μ (χ * s.value) hprod := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add
        (ambientScalarL2 (Gradient N) χ μ (ContinuousMap.toLp 2 μ ℝ s.gradient))
        (ambientCutoffGradientL2 χ hχ μ (ContinuousMap.toLp 2 μ ℝ s.value)),
      ambientScalarL2_coe (Gradient N) χ μ (ContinuousMap.toLp 2 μ ℝ s.gradient),
      ambientCutoffGradientL2_coe χ hχ μ (ContinuousMap.toLp 2 μ ℝ s.value),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ s.value,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ s.gradient,
      configurationLipschitzGradientL2_coe μ (χ * s.value) hprod,
      ae_descendedLiftGradient_cutoff_mul_smooth μ hμ χ hχ s]
      with X hadd hmul hgrad hv hs hp hrule
    simp only [hadd, Pi.add_apply, hmul, hgrad, hv, hs, hp, hrule]
  rw [hv, hg]
  exact configurationLipschitz_pair_mem_closedGradientGraph μ hμ (χ * s.value) hprod

/-- Strong scalar/vector L2 convergence of the smooth approximants and of
both bounded multiplier images places the proposed product in the closure. -/
theorem cutoff_mul_pair_mem_closedGradientGraph {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y)))
    (f : AmbientFormDomain N μ) :
    (ambientScalarL2 ℝ χ μ (ambientValue f),
      ambientScalarL2 (Gradient N) χ μ (ambientGradient f) +
        ambientCutoffGradientL2 χ hχ μ (ambientValue f)) ∈ closedGradientGraph N μ := by
  obtain ⟨s, hs⟩ := exists_smooth_formNorm_approx f
  have hp : Tendsto (fun n ↦
      (ContinuousMap.toLp 2 μ ℝ (s n).value, ContinuousMap.toLp 2 μ ℝ (s n).gradient))
      atTop (𝓝 f.1) := tendsto_iff_graphFormNorm_sub_tendsto_zero.mpr hs
  have hv : Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (s n).value)
      atTop (𝓝 (ambientValue f)) := (continuous_fst.tendsto f.1).comp hp
  have hg : Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (s n).gradient)
      atTop (𝓝 (ambientGradient f)) := (continuous_snd.tendsto f.1).comp hp
  have hmv := ((ambientScalarL2 ℝ χ μ).continuous.tendsto (ambientValue f)).comp hv
  have hmg := ((ambientScalarL2 (Gradient N) χ μ).continuous.tendsto (ambientGradient f)).comp hg
  have hcg := ((ambientCutoffGradientL2 χ hχ μ).continuous.tendsto (ambientValue f)).comp hv
  exact isClosed_closure.mem_of_tendsto (hmv.prodMk_nhds (hmg.add hcg))
    (Eventually.of_forall (fun n ↦ cutoff_mul_smooth_pair_mem_closedGradientGraph μ hμ χ hχ (s n)))

/-- Multiplication in the closed ambient form domain, constructed without a
membership or product-rule premise for the result. -/
def ambientLipschitzProduct {N : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (hμ : μ ≪ referenceMeasure N) (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y)))
    (f : AmbientFormDomain N μ) : AmbientFormDomain N μ :=
  ⟨(ambientScalarL2 ℝ χ μ (ambientValue f),
      ambientScalarL2 (Gradient N) χ μ (ambientGradient f) +
        ambientCutoffGradientL2 χ hχ μ (ambientValue f)),
    cutoff_mul_pair_mem_closedGradientGraph μ hμ χ hχ f⟩

theorem ambientLipschitzProduct_value_ae {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y))) (f : AmbientFormDomain N μ) :
    ambientValue (ambientLipschitzProduct μ hμ χ hχ f) =ᵐ[μ]
      (fun X ↦ χ X * ambientValue f X) := by
  simpa only [ambientValue, ambientLipschitzProduct, smul_eq_mul] using
    ambientScalarL2_coe ℝ χ μ (ambientValue f)

theorem ambientLipschitzProduct_gradient_ae {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y))) (f : AmbientFormDomain N μ) :
    ambientGradient (ambientLipschitzProduct μ hμ χ hχ f) =ᵐ[μ]
      (fun X ↦ χ X • ambientGradient f X + ambientValue f X • descendedLiftGradient χ X) := by
  filter_upwards [Lp.coeFn_add
      (ambientScalarL2 (Gradient N) χ μ (ambientGradient f))
      (ambientCutoffGradientL2 χ hχ μ (ambientValue f)),
    ambientScalarL2_coe (Gradient N) χ μ (ambientGradient f),
    ambientCutoffGradientL2_coe χ hχ μ (ambientValue f)] with X hadd hmul hgrad
  change (ambientScalarL2 (Gradient N) χ μ (ambientGradient f) +
    ambientCutoffGradientL2 χ hχ μ (ambientValue f)) X = _
  simp only [hadd, Pi.add_apply, hmul, hgrad]

theorem norm_ambientLipschitzProduct_gradient_le {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y))) (f : AmbientFormDomain N μ) :
    ‖ambientGradient (ambientLipschitzProduct μ hμ χ hχ f)‖ ≤
      ‖χ‖ * ‖ambientGradient f‖ + (K : ℝ) * ‖ambientValue f‖ :=
  (norm_add_le _ _).trans (add_le_add
    (norm_ambientScalarL2_le (Gradient N) χ μ (ambientGradient f))
    (norm_ambientCutoffGradientL2_le χ hχ μ (ambientValue f)))

/-- Source cutoff estimate, with exact square-root energy normalization. -/
theorem sqrt_ambientEnergy_lipschitzProduct_le {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y))) (f : AmbientFormDomain N μ) :
    Real.sqrt (ambientEnergy (ambientLipschitzProduct μ hμ χ hχ f)) ≤
      ‖χ‖ * Real.sqrt (ambientEnergy f) + (K : ℝ) * ‖ambientValue f‖ := by
  simpa only [ambientEnergy, graphEnergy, Real.sqrt_sq_eq_abs, abs_norm, ambientGradient] using
    norm_ambientLipschitzProduct_gradient_le μ hμ χ hχ f

/-- Actual Green-law specialization of the first assertion of source
Lemma 2.7. The cutoff constant is for the ordinary `2 * N` Euclidean lift. -/
theorem exists_green_ambient_lipschitz_product (N : ℕ) (_hN : 2 ≤ N) {β : ℝ}
    (_hβ : 0 ≤ β) (_hsub : β < 4) (χ : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hχ : LipschitzWith K (fun y ↦ χ (configurationQuotient N y)))
    (f : GreenAmbientFormDomain N β) :
    ∃ p : GreenAmbientFormDomain N β,
      (ambientValue p =ᵐ[gibbsMeasure greenRealRepresentative N β]
        (fun X ↦ χ X * ambientValue f X)) ∧
      (ambientGradient p =ᵐ[gibbsMeasure greenRealRepresentative N β]
        (fun X ↦ χ X • ambientGradient f X + ambientValue f X • descendedLiftGradient χ X)) ∧
      Real.sqrt (ambientEnergy p) ≤
        ‖χ‖ * Real.sqrt (ambientEnergy f) + (K : ℝ) * ‖ambientValue f‖ := by
  let μ := gibbsMeasure greenRealRepresentative N β
  have hμ : μ ≪ referenceMeasure N := gibbsMeasure_absolutelyContinuous _ N β
  exact ⟨ambientLipschitzProduct μ hμ χ hχ f,
    ambientLipschitzProduct_value_ae μ hμ χ hχ f,
    ambientLipschitzProduct_gradient_ae μ hμ χ hχ f,
    sqrt_ambientEnergy_lipschitzProduct_le μ hμ χ hχ f⟩

end PeriodicAttractiveLogGas
