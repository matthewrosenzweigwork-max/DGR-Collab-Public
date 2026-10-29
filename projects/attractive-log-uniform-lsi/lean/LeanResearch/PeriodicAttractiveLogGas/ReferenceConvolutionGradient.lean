import LeanResearch.PeriodicAttractiveLogGas.ReferencePotentialBounds
import LeanResearch.PeriodicAttractiveLogGas.GreenRegularizationL1
import LeanResearch.PeriodicAttractiveLogGas.SharpPoleMoments
import LeanResearch.PeriodicAttractiveLogGas.FarReferenceResidual
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The analytic convolution-gradient bridge in the source cell-reference
existence proof. Small-ball integration uses the actual quotient metric and
normalized Haar measure. The bounded-density hypothesis is first expressed
as domination of an actual probability measure; no fixed point is assumed.
See the associated development note for source-bound verification status.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff

namespace PeriodicAttractiveLogGas.ReferenceConvolutionGradient

open MeshCells MeshAdjacentCells ReferenceResidual ConditionalLawEstimates

theorem integral_torus_smallBall_inverseRadius {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    (∫ z in {z : Torus | torusEuclideanNorm z < s}, (torusEuclideanNorm z)⁻¹ ∂torusMeasure) =
      2 * Real.pi * s := by
  classical
  let A : Set Torus := {z | torusEuclideanNorm z < s}
  have hA : MeasurableSet A := measurableSet_lt measurable_torusEuclideanNorm measurable_const
  have hball : ball (0 : PlanarSpace) s ⊆ euclideanFundamentalBox (centeredBoxAnchor 0) := by
    intro x hx
    exact euclideanOpenBox_subset_fundamentalBox _
      (mem_centeredOpenBox_of_norm_lt_half ((mem_ball_zero_iff.mp hx).trans_le hsmall))
  calc
    _ = ∫ z, A.indicator (fun w ↦ (torusEuclideanNorm w)⁻¹) z ∂torusMeasure :=
      (integral_indicator hA).symm
    _ = ∫ x in euclideanFundamentalBox (centeredBoxAnchor 0),
        A.indicator (fun w ↦ (torusEuclideanNorm w)⁻¹) (torusQuotient x) :=
      (integral_torus_lift_on_box (integrable_torusEuclideanNorm_inv.indicator hA) _).symm
    _ = ∫ x in euclideanFundamentalBox (centeredBoxAnchor 0),
        (ball (0 : PlanarSpace) s).indicator (fun y ↦ ‖y‖⁻¹) x := by
      apply setIntegral_congr_fun (measurableSet_euclideanFundamentalBox _)
      intro x hx
      have he := torusEuclideanNorm_quotient_eq_of_mem_centeredBox hx
      by_cases hxs : ‖x‖ < s <;> simp [A, Set.indicator, he, hxs]
    _ = ∫ x in ball (0 : PlanarSpace) s, ‖x‖⁻¹ := by
      rw [setIntegral_indicator measurableSet_ball, inter_eq_right.mpr hball]
    _ = _ := by
      simpa only [neg_one_mul, Real.rpow_neg_one, show (2 : ℝ) - 1 = 1 by norm_num,
        Real.rpow_one, div_one] using
        SharpPoleMoments.integral_ball_norm_rpow (u := 1) (by norm_num) hs

theorem integral_torus_smallBall_inverseRadius_sub (x : Torus) {s : ℝ}
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    (∫ y in {y : Torus | torusEuclideanNorm (x - y) < s},
      (torusEuclideanNorm (x - y))⁻¹ ∂torusMeasure) = 2 * Real.pi * s := by
  classical
  have hA : MeasurableSet {y : Torus | torusEuclideanNorm (x - y) < s} :=
    measurableSet_lt (measurable_torusEuclideanNorm.comp
      (measurable_const.sub measurable_id)) measurable_const
  rw [← integral_indicator hA]
  calc
    _ = ∫ y, ({z : Torus | torusEuclideanNorm z < s}.indicator
        (fun z ↦ (torusEuclideanNorm z)⁻¹)) (x - y) ∂torusMeasure := by rfl
    _ = ∫ z, ({z : Torus | torusEuclideanNorm z < s}.indicator
        (fun z ↦ (torusEuclideanNorm z)⁻¹)) z ∂torusMeasure :=
      integral_sub_left_eq_self _ torusMeasure x
    _ = _ := by
      rw [integral_indicator (measurableSet_lt measurable_torusEuclideanNorm measurable_const),
        integral_torus_smallBall_inverseRadius hs hsmall]

theorem integrable_of_haar_domination {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Torus} {B : ℝ} (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    {f : Torus → E} (hf : Integrable f torusMeasure) : Integrable f μ :=
  (hf.smul_measure (c := ENNReal.ofReal B) ENNReal.ofReal_ne_top).mono_measure hμ

theorem ae_of_haar_domination {μ : Measure Torus} {B : ℝ}
    (hμ : μ ≤ ENNReal.ofReal B • torusMeasure) {P : Torus → Prop}
    (hP : ∀ᵐ y ∂torusMeasure, P y) : ∀ᵐ y ∂μ, P y :=
  hμ.absolutelyContinuous.ae_le (Measure.ae_smul_measure hP _)

theorem inverseRadius_sub_integrable {μ : Measure Torus} {B : ℝ}
    (hμ : μ ≤ ENNReal.ofReal B • torusMeasure) (x : Torus) :
    Integrable (fun y ↦ (torusEuclideanNorm (x - y))⁻¹) μ :=
  integrable_of_haar_domination hμ
    ((torusMeasure.measurePreserving_sub_left x).integrable_comp_of_integrable
      integrable_torusEuclideanNorm_inv)

/-- The sharp near contribution uses density domination; the complementary
contribution uses only total mass one. -/
theorem inverseRadius_sub_integral_le {μ : Measure Torus} [IsProbabilityMeasure μ]
    {B s : ℝ} (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) (x : Torus) :
    (∫ y, (torusEuclideanNorm (x - y))⁻¹ ∂μ) ≤ B * (2 * Real.pi * s) + s⁻¹ := by
  classical
  let A : Set Torus := {y | torusEuclideanNorm (x - y) < s}
  let f : Torus → ℝ := fun y ↦ (torusEuclideanNorm (x - y))⁻¹
  have hA : MeasurableSet A := measurableSet_lt (measurable_torusEuclideanNorm.comp
    (measurable_const.sub measurable_id)) measurable_const
  have hf : Integrable f torusMeasure :=
    (torusMeasure.measurePreserving_sub_left x).integrable_comp_of_integrable
      integrable_torusEuclideanNorm_inv
  have hfi : Integrable f μ := integrable_of_haar_domination hμ hf
  have hnear : (∫ y, A.indicator f y ∂μ) ≤ B * (2 * Real.pi * s) := by
    have hm := integral_mono_measure hμ
      (Eventually.of_forall fun y ↦ indicator_nonneg
        (fun z _ ↦ inv_nonneg.mpr (torusEuclideanNorm_nonneg (x - z))) y)
      ((hf.indicator hA).smul_measure (c := ENNReal.ofReal B) ENNReal.ofReal_ne_top)
    rw [integral_smul_measure, ENNReal.toReal_ofReal hB, smul_eq_mul] at hm
    have he : (∫ y, A.indicator f y ∂torusMeasure) = 2 * Real.pi * s := by
      rw [integral_indicator hA]
      exact integral_torus_smallBall_inverseRadius_sub x hs hsmall
    exact hm.trans_eq (congrArg (fun r : ℝ ↦ B * r) he)
  have hpoint (y : Torus) : f y ≤ A.indicator f y + s⁻¹ := by
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy]
      exact le_add_of_nonneg_right (inv_nonneg.mpr hs.le)
    · rw [Set.indicator_of_notMem hy, zero_add]
      have hsy : s ≤ torusEuclideanNorm (x - y) := le_of_not_gt hy
      simpa only [one_div] using one_div_le_one_div_of_le hs hsy
  have hle := integral_mono hfi ((hfi.indicator hA).add (integrable_const s⁻¹)) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hfi.indicator hA) (integrable_const s⁻¹),
    integral_const, probReal_univ, one_smul] at hle
  exact hle.trans (add_le_add hnear le_rfl)

theorem gradient_sub_integrable {μ : Measure Torus} {B : ℝ}
    (hμ : μ ≤ ENNReal.ofReal B • torusMeasure) (x : Torus) :
    Integrable (fun y ↦ greenGradient (x - y)) μ :=
  integrable_of_haar_domination hμ
    ((torusMeasure.measurePreserving_sub_left x).integrable_comp_of_integrable integrable_greenGradient)

theorem integral_norm_gradient_sub_le {μ : Measure Torus} [IsProbabilityMeasure μ]
    {B C₁ s : ℝ} (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hC : 0 ≤ C₁) (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) (x : Torus) :
    (∫ y, ‖greenGradient (x - y)‖ ∂μ) ≤ C₁ * (2 * Real.pi * B * s + s⁻¹) := by
  have hp : ∀ᵐ y ∂μ, x - y ≠ 0 := ae_of_haar_domination hμ
    ((torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (torusMeasure.ae_ne (0 : Torus)))
  have he := integral_mono_ae (gradient_sub_integrable hμ x).norm
    ((inverseRadius_sub_integrable hμ x).const_mul C₁) (hp.mono fun y hy ↦ by
      simpa only [div_eq_mul_inv] using hk (x - y) hy)
  rw [integral_const_mul] at he
  calc
    _ ≤ C₁ * (∫ y, (torusEuclideanNorm (x - y))⁻¹ ∂μ) := he
    _ ≤ C₁ * (B * (2 * Real.pi * s) + s⁻¹) :=
      mul_le_mul_of_nonneg_left (inverseRadius_sub_integral_le hB hμ hs hsmall x) hC
    _ = _ := by ring

theorem norm_integral_gradient_sub_le {μ : Measure Torus} [IsProbabilityMeasure μ]
    {B C₁ s : ℝ} (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hC : 0 ≤ C₁) (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) (x : Torus) :
    ‖∫ y, greenGradient (x - y) ∂μ‖ ≤ C₁ * (2 * Real.pi * B * s + s⁻¹) :=
  (norm_integral_le_integral_norm _).trans
    (integral_norm_gradient_sub_le hB hμ hC hk hs hsmall x)

theorem integrable_mollifier_gradient_pair {μ : Measure Torus} [IsProbabilityMeasure μ]
    {B C₁ s : ℝ} (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hC : 0 ≤ C₁) (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) (x : Torus) :
    Integrable (fun p : PlanarSpace × Torus ↦ scaledRadialMollifier ε p.1 •
      greenGradient ((x - torusQuotient p.1) - p.2)) (volume.prod μ) := by
  let H : PlanarSpace × Torus → PlanarSpace := fun p ↦ scaledRadialMollifier ε p.1 •
    greenGradient ((x - torusQuotient p.1) - p.2)
  let L := C₁ * (2 * Real.pi * B * s + s⁻¹)
  have hH : Measurable H :=
    (((contDiff_scaledRadialMollifier ε).continuous.measurable.comp measurable_fst).smul
      (measurable_greenGradient.comp ((measurable_const.sub
        (isOpenQuotientMap_torusQuotient.continuous.measurable.comp measurable_fst)).sub
          measurable_snd)))
  have hI (v : PlanarSpace) : Integrable (fun y ↦ H (v, y)) μ := by
    simpa only [H, Pi.smul_apply] using! Integrable.smul (scaledRadialMollifier ε v)
      (gradient_sub_integrable hμ (x - torusQuotient v))
  have hb (v : PlanarSpace) : (∫ y, ‖H (v, y)‖ ∂μ) ≤ scaledRadialMollifier ε v * L := by
    simp only [H, norm_smul, Real.norm_of_nonneg (scaledRadialMollifier_nonneg ε v)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_norm_gradient_sub_le hB hμ hC hk hs hsmall _) (scaledRadialMollifier_nonneg ε v)
  apply (integrable_prod_iff hH.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hI, ?_⟩
  have hm : StronglyMeasurable (Function.uncurry (fun v y ↦ ‖H (v, y)‖)) :=
    hH.norm.stronglyMeasurable
  apply ((integrable_scaledRadialMollifier ε hε).mul_const L).mono'
    hm.integral_prod_right.aestronglyMeasurable
  filter_upwards with v
  rw [Real.norm_of_nonneg (integral_nonneg fun y ↦ norm_nonneg _)]
  exact hb v

/-- Averaging the actual weak-gradient convolution preserves the sharp
near/far constant; the larger pointwise mollified-kernel bound is not used. -/
theorem norm_integral_regularizedGradient_sub_le
    {μ : Measure Torus} [IsProbabilityMeasure μ] {B C₁ s : ℝ}
    (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hC : 0 ≤ C₁) (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 16) (x : Torus) :
    ‖∫ y, regularizedGreenGradient ε hε (x - y) ∂μ‖ ≤
      C₁ * (2 * Real.pi * B * s + s⁻¹) := by
  let L := C₁ * (2 * Real.pi * B * s + s⁻¹)
  have hp := integrable_mollifier_gradient_pair hB hμ hC hk hs hsmall ε hε x
  have he : (∫ y, regularizedGreenGradient ε hε (x - y) ∂μ) =
      ∫ v : PlanarSpace, scaledRadialMollifier ε v •
        (∫ y, greenGradient ((x - torusQuotient v) - y) ∂μ) := by
    calc
      _ = ∫ y, (∫ v : PlanarSpace, scaledRadialMollifier ε v •
          greenGradient ((x - torusQuotient v) - y) ∂volume) ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        rw [regularizedGreenGradient_eq_integral ε hε hεsmall]
        apply integral_congr_ae
        filter_upwards with v
        congr 2
        abel
      _ = ∫ v : PlanarSpace, ∫ y, scaledRadialMollifier ε v •
          greenGradient ((x - torusQuotient v) - y) ∂μ := (integral_integral_swap hp).symm
      _ = _ := by simp only [integral_smul]
  rw [he]
  calc
    _ ≤ ∫ v : PlanarSpace, ‖scaledRadialMollifier ε v •
        (∫ y, greenGradient ((x - torusQuotient v) - y) ∂μ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v : PlanarSpace, scaledRadialMollifier ε v * L := by
      apply integral_mono
      · simpa only [integral_smul] using hp.integral_prod_left.norm
      · exact (integrable_scaledRadialMollifier ε hε).mul_const L
      · intro v
        dsimp only
        rw [norm_smul, Real.norm_of_nonneg (scaledRadialMollifier_nonneg ε v)]
        exact mul_le_mul_of_nonneg_left
          (norm_integral_gradient_sub_le hB hμ hC hk hs hsmall _) (scaledRadialMollifier_nonneg ε v)
    _ = L := by rw [integral_mul_const, integral_scaledRadialMollifier ε hε, one_mul]

theorem hasFDerivAt_regularizedGreen_sub (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 16) (x : PlanarSpace) (y : Torus) :
    HasFDerivAt (fun w : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient w - y))
      (regularizedGreenDifferential ε hε (torusQuotient x - y)) x := by
  have h := ((contDiff_regularizedGreen_lift ε hε hεsmall).differentiable (by simp)
    (x - centeredLift y)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (centeredLift y))
  have he : torusQuotient (x - centeredLift y) = torusQuotient x - y := by
    rw [torusQuotient_sub, torusQuotient_centeredLift]
  rw [← regularizedGreenDifferential_lift ε hε, he] at h
  simpa only [Function.comp_def, id_eq, torusQuotient_sub, torusQuotient_centeredLift,
    ContinuousLinearMap.comp_id] using h

theorem hasFDerivAt_regularizedPotential {μ : Measure Torus} [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 16) (x : PlanarSpace) :
    HasFDerivAt (fun w : PlanarSpace ↦ ∫ y, regularizedGreen ε hε (torusQuotient w - y) ∂μ)
      (InnerProductSpace.toDual ℝ PlanarSpace
        (∫ y, regularizedGreenGradient ε hε (torusQuotient x - y) ∂μ)) x := by
  let F : PlanarSpace → Torus → ℝ := fun w y ↦ regularizedGreen ε hε (torusQuotient w - y)
  let D : PlanarSpace → Torus → PlanarSpace →L[ℝ] ℝ :=
    fun w y ↦ regularizedGreenDifferential ε hε (torusQuotient w - y)
  have hFc (w : PlanarSpace) : Continuous (F w) := by
    have hc : Continuous (fun y : Torus ↦ torusQuotient w - y) := by fun_prop
    exact (continuous_regularizedGreen ε hε).comp hc
  have hDc (w : PlanarSpace) : Continuous (D w) := by
    have hc : Continuous (fun y : Torus ↦ torusQuotient w - y) := by fun_prop
    exact (continuous_regularizedGreenDifferential ε hε hεsmall).comp hc
  let A : C(Torus, PlanarSpace →L[ℝ] ℝ) :=
    ⟨regularizedGreenDifferential ε hε, continuous_regularizedGreenDifferential ε hε hεsmall⟩
  have hb : ∀ᵐ y ∂μ, ∀ w ∈ (Set.univ : Set PlanarSpace), ‖D w y‖ ≤ ‖A‖ :=
    Eventually.of_forall fun y w _ ↦ A.norm_coe_le_norm (torusQuotient w - y)
  have hd : ∀ᵐ y ∂μ, ∀ w ∈ (Set.univ : Set PlanarSpace), HasFDerivAt (fun v ↦ F v y) (D w y) w :=
    Eventually.of_forall fun y w _ ↦ hasFDerivAt_regularizedGreen_sub ε hε hεsmall w y
  let fC : C(Torus, ℝ) := ⟨F x, hFc x⟩
  have hFi : Integrable (F x) μ := (integrable_const ‖fC‖).mono'
    (hFc x).aestronglyMeasurable (Eventually.of_forall fC.norm_coe_le_norm)
  have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Set.univ) (Filter.univ_mem : Set.univ ∈ 𝓝 x)
    (Eventually.of_forall fun w ↦ (hFc w).aestronglyMeasurable)
    hFi (hDc x).aestronglyMeasurable hb (integrable_const ‖A‖) hd
  have he : (∫ y, D x y ∂μ) = InnerProductSpace.toDual ℝ PlanarSpace
      (∫ y, regularizedGreenGradient ε hε (torusQuotient x - y) ∂μ) := by
    calc
      _ = ∫ y, InnerProductSpace.toDual ℝ PlanarSpace
          (regularizedGreenGradient ε hε (torusQuotient x - y)) ∂μ := by
        simp only [regularizedGreenGradient, LinearIsometryEquiv.apply_symm_apply, D]
      _ = _ := (InnerProductSpace.toDual ℝ PlanarSpace).toLinearIsometry.integral_comp_comm _
  exact hh.congr_fderiv he

theorem lipschitzWith_regularizedPotential {μ : Measure Torus} [IsProbabilityMeasure μ]
    {B C₁ s : ℝ} (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hC : 0 ≤ C₁) (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 16) :
    LipschitzWith ⟨C₁ * (2 * Real.pi * B * s + s⁻¹), by positivity⟩
      (fun w : PlanarSpace ↦ ∫ y, regularizedGreen ε hε (torusQuotient w - y) ∂μ) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (fun w ↦ (hasFDerivAt_regularizedPotential ε hε hεsmall w).differentiableAt)
  intro w
  change ‖fderiv ℝ _ w‖ ≤ _
  rw [(hasFDerivAt_regularizedPotential ε hε hεsmall w).fderiv,
    (InnerProductSpace.toDual ℝ PlanarSpace).norm_map]
  exact norm_integral_regularizedGradient_sub_le hB hμ hC hk hs hsmall ε hε hεsmall _

theorem potential_integrable_at_pole {μ : Measure Torus} {B : ℝ}
    (hμ : μ ≤ ENNReal.ofReal B • torusMeasure) (x : Torus) :
    Integrable (greenKernel x) μ :=
  integrable_of_haar_domination hμ (ReferencePotentialBounds.green_translate_integrable x)

/-- The actual potential is the pointwise limit of the smooth Green
convolutions, including at all poles of the evaluation variable. Only the
integration variable's singleton pole is removed as a null set. -/
theorem tendsto_regularizedPotential {μ : Measure Torus} [IsFiniteMeasure μ] {B : ℝ}
    (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ 1 / 16)
    (ht : Tendsto ε atTop (𝓝 0)) (x : Torus) :
    Tendsto (fun n ↦ ∫ y, regularizedGreen (ε n) (hε n) (x - y) ∂μ)
      atTop (𝓝 (potential μ x)) := by
  obtain ⟨M, hM, hb⟩ := exists_regularizedGreen_abs_majorant
  have hMI : Integrable (fun y ↦ M (x - y)) μ :=
    integrable_of_haar_domination hμ
      ((torusMeasure.measurePreserving_sub_left x).integrable_comp_of_integrable hM)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun y ↦ regularizedGreen (ε n) (hε n) (x - y)) μ := by
    have hc : Continuous (fun y : Torus ↦ x - y) := continuous_const.sub continuous_id
    exact ((continuous_regularizedGreen (ε n) (hε n)).comp hc).aestronglyMeasurable
  change Tendsto _ atTop (𝓝 (∫ y, regularGreenRepresentative (x - y) ∂μ))
  apply tendsto_integral_of_dominated_convergence (fun y ↦ M (x - y)) hmeas hMI
  · intro n
    exact ae_of_haar_domination hμ
      ((torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae (hb _ _ (hs n)))
  · have hp : ∀ᵐ y ∂μ, x - y ≠ 0 := ae_of_haar_domination hμ
      ((torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae (torusMeasure.ae_ne 0))
    exact hp.mono fun y hy ↦ tendsto_regularizedGreen hε hs ht hy

/-- The weak Green identity, smooth differentiation, uniform sharp bounds,
and dominated convergence give the actual physical-lift Lipschitz bound. -/
theorem lipschitzWith_potential {μ : Measure Torus} [IsProbabilityMeasure μ]
    {B C₁ s : ℝ} (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hC : 0 ≤ C₁) (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    LipschitzWith ⟨C₁ * (2 * Real.pi * B * s + s⁻¹), by positivity⟩
      (fun x : PlanarSpace ↦ potential μ (torusQuotient x)) := by
  let ε : ℕ → ℝ := fun n ↦ (1 / 16 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεsmall (n : ℕ) : ε n ≤ (1 / 16 : ℝ) := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (le_add_of_nonneg_left (Nat.cast_nonneg n))
    dsimp [ε]
    nlinarith
  have ht : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 16 : ℝ)
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  apply le_of_tendsto ((tendsto_regularizedPotential hμ ε hε hεsmall ht (torusQuotient x)).sub
    (tendsto_regularizedPotential hμ ε hε hεsmall ht (torusQuotient y))).norm
  exact Eventually.of_forall fun n ↦ lipschitzWith_iff_norm_sub_le.mp
    (lipschitzWith_regularizedPotential hB hμ hC hk hs hsmall (ε n) (hε n) (hεsmall n)) x y

theorem lipschitzWith_scaledPotential {μ : Measure Torus} [IsProbabilityMeasure μ]
    {β β₀ B C₁ s : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hB : 0 ≤ B) (hμ : μ ≤ ENNReal.ofReal B • torusMeasure)
    (hC : 0 ≤ C₁) (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    LipschitzWith ⟨β₀ * C₁ * (2 * Real.pi * B * s + s⁻¹),
      mul_nonneg (mul_nonneg (hβ.trans hβ₀) hC) (by positivity)⟩
      (fun x : PlanarSpace ↦ β * potential μ (torusQuotient x)) := by
  have hL := lipschitzWith_potential hB hμ hC hk hs hsmall
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  change ‖β * potential μ (torusQuotient x) - β * potential μ (torusQuotient y)‖ ≤
    (β₀ * C₁ * (2 * Real.pi * B * s + s⁻¹)) * ‖x - y‖
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg hβ]
  calc
    _ ≤ β * ((C₁ * (2 * Real.pi * B * s + s⁻¹)) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (lipschitzWith_iff_norm_sub_le.mp hL x y) hβ
    _ ≤ β₀ * ((C₁ * (2 * Real.pi * B * s + s⁻¹)) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_right hβ₀ (by positivity)
    _ = _ := by ring

/-- The exact diameter factor uses the physical chart on the closed cell,
including boundary points shared with adjacent cells. -/
theorem cell_oscillation_le_of_lipschitz {F : Torus → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L (fun x : PlanarSpace ↦ F (torusQuotient x)))
    {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ a)) :
    |F x - F y| ≤ (L : ℝ) * (Real.sqrt 2 / (J : ℝ)) := by
  rw [closure_meshCell] at hx hy
  obtain ⟨Z, hZ, rfl⟩ := hx
  obtain ⟨W, hW, rfl⟩ := hy
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have h := lipschitzWith_iff_norm_sub_le.mp hF (meshAffine J a Z) (meshAffine J a W)
  change ‖F (meshChart J a Z) - F (meshChart J a W)‖ ≤
    (L : ℝ) * ‖meshAffine J a Z - meshAffine J a W‖ at h
  rw [Real.norm_eq_abs, MeshNearbyGeometry.meshAffine_sub, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hJr.le)] at h
  calc
    _ ≤ (L : ℝ) * ((J : ℝ)⁻¹ * ‖Z - W‖) := h
    _ ≤ (L : ℝ) * ((J : ℝ)⁻¹ * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (FarReferenceResidual.square_diameter hZ hW)
          (inv_nonneg.mpr hJr.le)) L.coe_nonneg
    _ = _ := by ring

/-- The source's balancing radius, written with an ordinary square root. -/
def referenceScale (J : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * Real.exp 1 * t))⁻¹ / (J : ℝ)

theorem referenceScale_pos {J : ℕ} (hJ : 0 < J) {t : ℝ} (ht : 0 < t) :
    0 < referenceScale J t := by
  unfold referenceScale
  positivity

theorem referenceScale_le_half {J : ℕ} (_hJ : 0 < J) {t : ℝ} (_ht : 0 < t)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t)) :
    referenceScale J t ≤ 1 / 2 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hscale
  simpa only [referenceScale, one_div, div_eq_mul_inv, mul_inv_rev, one_mul] using h

theorem referenceScale_balancing {J : ℕ} (hJ : 0 < J) {t : ℝ} (ht : 0 < t) :
    2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * referenceScale J t +
        (referenceScale J t)⁻¹ = 2 * (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t) := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hr : Real.sqrt (2 * Real.pi * Real.exp 1 * t) ≠ 0 := ne_of_gt (by positivity)
  have hr2 := Real.sq_sqrt (show 0 ≤ 2 * Real.pi * Real.exp 1 * t by positivity)
  calc
    _ = (Real.sqrt (2 * Real.pi * Real.exp 1 * t)) ^ 2 * (J : ℝ) ^ 2 *
        ((Real.sqrt (2 * Real.pi * Real.exp 1 * t))⁻¹ / (J : ℝ)) +
        ((Real.sqrt (2 * Real.pi * Real.exp 1 * t))⁻¹ / (J : ℝ))⁻¹ := by
      rw [hr2]
      unfold referenceScale
      ring
    _ = _ := by field_simp; norm_num

theorem referenceScale_cell_coefficient {J : ℕ} (hJ : 0 < J) {t : ℝ} (ht : 0 < t)
    (β₀ C₁ : ℝ) :
    (β₀ * C₁ * (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * referenceScale J t +
      (referenceScale J t)⁻¹)) * (Real.sqrt 2 / (J : ℝ)) =
        4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have he : Real.sqrt (2 * Real.pi * Real.exp 1 * t) =
      Real.sqrt 2 * Real.sqrt (Real.pi * Real.exp 1 * t) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [referenceScale_balancing hJ ht, he]
  calc
    _ = 2 * β₀ * C₁ * ((Real.sqrt 2) ^ 2) * Real.sqrt (Real.pi * Real.exp 1 * t) := by
      field_simp
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

/-- The exact source oscillation estimate for every cell, occupied or not.
All analytic inputs are discharged by actual Haar domination. -/
theorem source_cell_oscillation {μ : Measure Torus} [IsProbabilityMeasure μ]
    {J : ℕ} (hJ : 0 < J) {t β β₀ C₁ : ℝ} (ht : 0 < t)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ) ^ 2) • torusMeasure)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (a : MeshIndex J) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ a)) :
    |β * potential μ x - β * potential μ y| ≤
      4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) := by
  have hs : 0 < referenceScale J t := referenceScale_pos hJ ht
  have hL := lipschitzWith_scaledPotential hβ hβ₀ (by positivity) hμ hC hk
    hs (referenceScale_le_half hJ ht hscale)
  have h := cell_oscillation_le_of_lipschitz
    (F := fun z ↦ β * potential μ z)
    (L := ⟨β₀ * C₁ * (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * referenceScale J t +
      (referenceScale J t)⁻¹), mul_nonneg (mul_nonneg (hβ.trans hβ₀) hC) (by positivity)⟩)
    hL hJ a hx hy
  change |β * potential μ x - β * potential μ y| ≤
    (β₀ * C₁ * (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * referenceScale J t +
      (referenceScale J t)⁻¹)) * (Real.sqrt 2 / (J : ℝ)) at h
  rwa [referenceScale_cell_coefficient hJ ht] at h

theorem source_gradient_bound {μ : Measure Torus} [IsProbabilityMeasure μ]
    {J : ℕ} {t β β₀ s : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ) ^ 2) • torusMeasure)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) (x : Torus) :
    ‖β • (∫ y, greenGradient (x - y) ∂μ)‖ ≤
      β₀ * kernelConstant * (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * s + s⁻¹) := by
  have h := norm_integral_gradient_sub_le (by positivity) hμ kernelConstant_pos.le
    kernel_gradient_bound hs hsmall x
  rw [norm_smul, Real.norm_of_nonneg hβ]
  calc
    _ ≤ β * (kernelConstant * (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * s + s⁻¹)) :=
      mul_le_mul_of_nonneg_left h hβ
    _ ≤ β₀ * (kernelConstant * (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * s + s⁻¹)) :=
      mul_le_mul_of_nonneg_right hβ₀ (mul_nonneg kernelConstant_pos.le (by positivity))
    _ = _ := by ring

theorem source_lipschitz_bound {μ : Measure Torus} [IsProbabilityMeasure μ]
    {J : ℕ} {t β β₀ s : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ) ^ 2) • torusMeasure)
    (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    LipschitzWith ⟨β₀ * kernelConstant *
      (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * s + s⁻¹),
      mul_nonneg (mul_nonneg (hβ.trans hβ₀) kernelConstant_pos.le) (by positivity)⟩
      (fun x : PlanarSpace ↦ β * potential μ (torusQuotient x)) :=
  lipschitzWith_scaledPotential hβ hβ₀ (by positivity) hμ kernelConstant_pos.le
    kernel_gradient_bound hs hsmall

theorem source_cell_oscillation_constants {μ : Measure Torus} [IsProbabilityMeasure μ]
    {J : ℕ} (hJ : 0 < J) {t β β₀ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ) ^ 2) • torusMeasure)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (a : MeshIndex J) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ a)) :
    |β * potential μ x - β * potential μ y| ≤
      4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) :=
  source_cell_oscillation hJ ht hβ hβ₀ kernelConstant_pos.le kernel_gradient_bound hμ hscale a hx hy

theorem source_cell_oscillation_le_one {μ : Measure Torus} [IsProbabilityMeasure μ]
    {J : ℕ} (hJ : 0 < J) {t β β₀ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ) ^ 2) • torusMeasure)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hosc : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (a : MeshIndex J) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ a)) :
    |β * potential μ x - β * potential μ y| ≤ 1 :=
  (source_cell_oscillation_constants hJ ht hβ hβ₀ hμ hscale a hx hy).trans hosc

/-- An arbitrary measurable bounded probability density supplies the
actual domination and probability instances used above. -/
theorem boundedDensity_integrable {ρ : Torus → ℝ} {B : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x) (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ B) :
    Integrable ρ torusMeasure := by
  apply (integrable_const B).mono' hρ.aestronglyMeasurable
  filter_upwards [hρ0, hρB] with x hx0 hxB
  simpa only [Real.norm_of_nonneg hx0] using hxB

theorem boundedDensity_probability {ρ : Torus → ℝ} {B : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x) (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ B)
    (hρ1 : (∫ x, ρ x ∂torusMeasure) = 1) :
    IsProbabilityMeasure (torusMeasure.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (boundedDensity_integrable hρ hρ0 hρB) hρ0,
    hρ1, ENNReal.ofReal_one]

theorem boundedDensity_le_haar {ρ : Torus → ℝ} {B : ℝ}
    (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ B) :
    torusMeasure.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) ≤ ENNReal.ofReal B • torusMeasure := by
  rw [← withDensity_const]
  exact withDensity_mono (hρB.mono fun x hx ↦ ENNReal.ofReal_le_ofReal hx)

theorem boundedDensity_green_integrable {ρ : Torus → ℝ} {B : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x) (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ B)
    (x : Torus) : Integrable (fun y ↦ regularGreenRepresentative (x - y) * ρ y) torusMeasure := by
  have hi := potential_integrable_at_pole (boundedDensity_le_haar hρB) x
  rw [integrable_withDensity_iff_integrable_smul' hρ.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at hi
  apply hi.congr
  filter_upwards [hρ0] with y hy
  simp only [ENNReal.toReal_ofReal hy, smul_eq_mul, greenKernel, mul_comm]

theorem potential_boundedDensity_eq {ρ : Torus → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x) (x : Torus) :
    potential (torusMeasure.withDensity (fun y ↦ ENNReal.ofReal (ρ y))) x =
      ∫ y, regularGreenRepresentative (x - y) * ρ y ∂torusMeasure := by
  rw [potential, integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with y hy
  simp only [ENNReal.toReal_ofReal hy, smul_eq_mul, greenKernel, mul_comm]

theorem boundedDensity_gradient_integrable {ρ : Torus → ℝ} {B : ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x) (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ B)
    (x : Torus) : Integrable (fun y ↦ ρ y • greenGradient (x - y)) torusMeasure := by
  have hi := gradient_sub_integrable (boundedDensity_le_haar hρB) x
  rw [integrable_withDensity_iff_integrable_smul' hρ.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at hi
  apply hi.congr
  filter_upwards [hρ0] with y hy
  simp only [ENNReal.toReal_ofReal hy]

theorem gradient_boundedDensity_eq {ρ : Torus → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x) (x : Torus) :
    (∫ y, greenGradient (x - y) ∂torusMeasure.withDensity (fun y ↦ ENNReal.ofReal (ρ y))) =
      ∫ y, ρ y • greenGradient (x - y) ∂torusMeasure := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with y hy
  simp only [ENNReal.toReal_ofReal hy]

theorem boundedDensity_source_gradient_bound {ρ : Torus → ℝ}
    {J : ℕ} {t β β₀ s : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x)
    (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ Real.exp 1 * t * (J : ℝ) ^ 2)
    (hρ1 : (∫ x, ρ x ∂torusMeasure) = 1) (hs : 0 < s) (hsmall : s ≤ 1 / 2) (x : Torus) :
    ‖β • (∫ y, ρ y • greenGradient (x - y) ∂torusMeasure)‖ ≤
      β₀ * kernelConstant * (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * s + s⁻¹) := by
  let := boundedDensity_probability hρ hρ0 hρB hρ1
  simpa only [gradient_boundedDensity_eq hρ hρ0] using
    source_gradient_bound ht hβ hβ₀ (boundedDensity_le_haar hρB) hs hsmall x

theorem boundedDensity_source_cell_oscillation {ρ : Torus → ℝ}
    {J : ℕ} (hJ : 0 < J) {t β β₀ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x)
    (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ Real.exp 1 * t * (J : ℝ) ^ 2)
    (hρ1 : (∫ x, ρ x ∂torusMeasure) = 1)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (a : MeshIndex J) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ a)) :
    |β * (∫ z, regularGreenRepresentative (x - z) * ρ z ∂torusMeasure) -
      β * (∫ z, regularGreenRepresentative (y - z) * ρ z ∂torusMeasure)| ≤
        4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) := by
  let := boundedDensity_probability hρ hρ0 hρB hρ1
  simpa only [potential_boundedDensity_eq hρ hρ0] using
    source_cell_oscillation_constants hJ ht hβ hβ₀ (boundedDensity_le_haar hρB) hscale a hx hy

theorem boundedDensity_source_lipschitz {ρ : Torus → ℝ}
    {J : ℕ} {t β β₀ s : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂torusMeasure, 0 ≤ ρ x)
    (hρB : ∀ᵐ x ∂torusMeasure, ρ x ≤ Real.exp 1 * t * (J : ℝ) ^ 2)
    (hρ1 : (∫ x, ρ x ∂torusMeasure) = 1) (hs : 0 < s) (hsmall : s ≤ 1 / 2) :
    LipschitzWith ⟨β₀ * kernelConstant *
      (2 * Real.pi * (Real.exp 1 * t * (J : ℝ) ^ 2) * s + s⁻¹),
      mul_nonneg (mul_nonneg (hβ.trans hβ₀) kernelConstant_pos.le) (by positivity)⟩
      (fun x : PlanarSpace ↦ β *
        ∫ y, regularGreenRepresentative (torusQuotient x - y) * ρ y ∂torusMeasure) := by
  let := boundedDensity_probability hρ hρ0 hρB hρ1
  simpa only [potential_boundedDensity_eq hρ hρ0] using
    source_lipschitz_bound ht hβ hβ₀ (boundedDensity_le_haar hρB) hs hsmall

end PeriodicAttractiveLogGas.ReferenceConvolutionGradient
