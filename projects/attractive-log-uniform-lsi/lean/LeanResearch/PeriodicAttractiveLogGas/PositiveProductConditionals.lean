import LeanResearch.PeriodicAttractiveLogGas.OneCoordinateConditionals
import LeanResearch.PeriodicAttractiveLogGas.CoordinateConditionalKernels

/-! Extension of the actual Proposition 3.4 disintegration
argument to arbitrary strictly positive measurable real joint weights.
The outside law is its actual pushforward. A Dirac fallback is used only
at divergent sections, proved null for this outside marginal. This unit
does not posit a Gibbs representation for any smaller marginal law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.PositiveProductConditionals

open OneCoordinateConditionals CellRestrictions GreenPointWeights

variable {n : ℕ}

def density (W : Configuration (n + 1) → ℝ) (X : Configuration (n + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal (W X)

theorem measurable_density {W : Configuration (n + 1) → ℝ} (hW : Measurable W) :
    Measurable (density W) := hW.ennreal_ofReal

theorem density_pos {W : Configuration (n + 1) → ℝ} (hWpos : ∀ X, 0 < W X)
    (X : Configuration (n + 1)) : 0 < density W X := ENNReal.ofReal_pos.mpr (hWpos X)

def normalizer (μ : Fin (n + 1) → Measure Torus) (W : Configuration (n + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ X, density W X ∂Measure.pi μ

def productLaw (μ : Fin (n + 1) → Measure Torus) (W : Configuration (n + 1) → ℝ) :
    Measure (Configuration (n + 1)) :=
  (normalizer μ W)⁻¹ • (Measure.pi μ).withDensity (density W)

theorem normalizer_ne_zero (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) : normalizer μ W ≠ 0 := by
  intro h
  have hae := (lintegral_eq_zero_iff (measurable_density hW)).mp h
  obtain ⟨X, hX⟩ := hae.exists
  exact (density_pos hWpos X).ne' hX

theorem normalizer_ne_top_iff_integrable (μ : Fin (n + 1) → Measure Torus)
    {W : Configuration (n + 1) → ℝ} (hW : Measurable W) (hWpos : ∀ X, 0 < W X) :
    normalizer μ W ≠ ⊤ ↔ Integrable W (Measure.pi μ) :=
  lintegral_ofReal_ne_top_iff_integrable hW.aestronglyMeasurable
    (Eventually.of_forall fun X ↦ (hWpos X).le)

theorem normalizer_eq_ofReal_integral (μ : Fin (n + 1) → Measure Torus)
    {W : Configuration (n + 1) → ℝ} (hWpos : ∀ X, 0 < W X)
    (hi : Integrable W (Measure.pi μ)) :
    normalizer μ W = ENNReal.ofReal (∫ X, W X ∂Measure.pi μ) :=
  (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun X ↦ (hWpos X).le)).symm

theorem integral_weight_pos (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (hi : Integrable W (Measure.pi μ)) :
    0 < ∫ X, W X ∂Measure.pi μ := by
  have h : 0 < normalizer μ W := pos_iff_ne_zero.mpr (normalizer_ne_zero μ hW hWpos)
  rw [normalizer_eq_ofReal_integral μ hWpos hi] at h
  exact ENNReal.ofReal_pos.mp h

/-- Probability normalization is proved from the actual finite integral. -/
theorem productLaw_probability (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (hfin : normalizer μ W ≠ ⊤) :
    IsProbabilityMeasure (productLaw μ W) := by
  constructor
  rw [productLaw, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (normalizer_ne_zero μ hW hWpos) hfin

theorem productLaw_probability_of_integrable (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (hi : Integrable W (Measure.pi μ)) :
    IsProbabilityMeasure (productLaw μ W) :=
  productLaw_probability μ hW hWpos ((normalizer_ne_top_iff_integrable μ hW hWpos).mpr hi)

theorem productLaw_absolutelyContinuous (μ : Fin (n + 1) → Measure Torus)
    (W : Configuration (n + 1) → ℝ) : productLaw μ W ≪ Measure.pi μ :=
  (withDensity_absolutelyContinuous _ _).smul_left _

def sectionMass (μ : Measure Torus) (W : Configuration (n + 1) → ℝ)
    (i : Fin (n + 1)) (Y : Configuration n) : ℝ≥0∞ :=
  ∫⁻ z, density W (insertSite i z Y) ∂μ

theorem measurable_jointSection {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1)) :
    Measurable (fun p : Configuration n × Torus ↦ density W (insertSite i p.2 p.1)) :=
  (measurable_density hW).comp ((measurable_insertSite i).comp measurable_swap)

theorem measurable_weightSection {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1)) (Y : Configuration n) :
    Measurable (fun z : Torus ↦ W (insertSite i z Y)) :=
  hW.comp ((measurable_insertSite i).comp measurable_prodMk_right)

theorem measurable_sectionMass (μ : Measure Torus) [SFinite μ]
    {W : Configuration (n + 1) → ℝ} (hW : Measurable W) (i : Fin (n + 1)) :
    Measurable (sectionMass μ W i) := (measurable_jointSection hW i).lintegral_prod_right

theorem sectionMass_ne_zero (μ : Measure Torus) [NeZero μ]
    {W : Configuration (n + 1) → ℝ} (hW : Measurable W) (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) (Y : Configuration n) : sectionMass μ W i Y ≠ 0 := by
  intro h
  have hae := (lintegral_eq_zero_iff (measurable_weightSection hW i Y).ennreal_ofReal).mp h
  obtain ⟨z, hz⟩ := hae.exists
  exact (density_pos hWpos (insertSite i z Y)).ne' hz

def sectionKernel (μ : Measure Torus) [SFinite μ] (W : Configuration (n + 1) → ℝ)
    (hW : Measurable W) (i : Fin (n + 1)) : Kernel (Configuration n) Torus where
  toFun Y := (sectionMass μ W i Y)⁻¹ •
    μ.withDensity (fun z ↦ density W (insertSite i z Y))
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
    exact (measurable_sectionMass μ hW i).inv.mul
      ((measurable_jointSection hW i).lintegral_prod_right (ν := μ.restrict s))

theorem sectionKernel_eq_cond (μ : Measure Torus) [SFinite μ]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W)
    (i : Fin (n + 1)) (Y : Configuration n) :
    sectionKernel μ W hW i Y = ProbabilityTheory.cond
      (μ.withDensity (fun z ↦ density W (insertSite i z Y))) univ := by
  change (sectionMass μ W i Y)⁻¹ •
    μ.withDensity (fun z ↦ density W (insertSite i z Y)) = _
  simp only [ProbabilityTheory.cond, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, sectionMass]

theorem lintegral_sectionKernel (μ : Measure Torus) [SFinite μ]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W)
    (i : Fin (n + 1)) (Y : Configuration n) {f : Torus → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂sectionKernel μ W hW i Y) = (sectionMass μ W i Y)⁻¹ *
      ∫⁻ z, density W (insertSite i z Y) * f z ∂μ := by
  have hs : Measurable (fun z : Torus ↦ density W (insertSite i z Y)) :=
    (measurable_weightSection hW i Y).ennreal_ofReal
  change (∫⁻ z, f z ∂(sectionMass μ W i Y)⁻¹ •
    μ.withDensity (fun z ↦ density W (insertSite i z Y))) = _
  rw [lintegral_smul_measure, smul_eq_mul]
  have hh : (∫⁻ z, f z ∂μ.withDensity (fun z ↦ density W (insertSite i z Y))) =
      ∫⁻ z, density W (insertSite i z Y) * f z ∂μ :=
    lintegral_withDensity_eq_lintegral_mul μ hs hf
  exact congrArg (fun t : ℝ≥0∞ ↦ (sectionMass μ W i Y)⁻¹ * t) hh

theorem measurable_sectionIntegral (μ : Measure Torus) [SFinite μ]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W) (i : Fin (n + 1))
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun Y ↦ ∫⁻ z, F (insertSite i z Y) ∂sectionKernel μ W hW i Y) := by
  have hFi : Measurable (fun p : Configuration n × Torus ↦ F (insertSite i p.2 p.1)) :=
    hF.comp ((measurable_insertSite i).comp measurable_swap)
  have hfixed (Y : Configuration n) : Measurable (fun z : Torus ↦ F (insertSite i z Y)) :=
    hFi.comp ((measurable_const (a := Y)).prodMk measurable_id)
  have he (Y : Configuration n) := lintegral_sectionKernel μ W hW i Y (hfixed Y)
  simp_rw [he]
  have hm : Measurable (fun p : Configuration n × Torus ↦
      density W (insertSite i p.2 p.1) * F (insertSite i p.2 p.1)) :=
    (measurable_jointSection hW i).mul hFi
  exact (measurable_sectionMass μ hW i).inv.mul hm.lintegral_prod_right'

/-- The outside marginal is always the actual pushforward of the joint law. -/
def outsideMarginal (μ : Fin (n + 1) → Measure Torus) (W : Configuration (n + 1) → ℝ)
    (i : Fin (n + 1)) : Measure (Configuration n) := Measure.map (removeSite i) (productLaw μ W)

theorem normalizer_eq_sections (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1)) :
    normalizer μ W = ∫⁻ Y, sectionMass (μ i) W i Y ∂outsideReference μ i :=
  lintegral_pi_insert μ i (measurable_density hW)

theorem lintegral_productLaw (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1))
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productLaw μ W) = (normalizer μ W)⁻¹ *
      ∫⁻ Y, ∫⁻ z, density W (insertSite i z Y) * F (insertSite i z Y)
        ∂μ i ∂outsideReference μ i := by
  rw [productLaw, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_density hW) hF]
  congr 1
  exact lintegral_pi_insert μ i ((measurable_density hW).mul hF)

theorem outsideMarginal_eq (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1)) :
    outsideMarginal μ W i = (outsideReference μ i).withDensity
      (fun Y ↦ (normalizer μ W)⁻¹ * sectionMass (μ i) W i Y) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (fun X : Configuration (n + 1) ↦ f (removeSite i X)) :=
    hf.comp (measurable_removeSite i)
  have hd : Measurable (fun Y : Configuration n ↦
      (normalizer μ W)⁻¹ * sectionMass (μ i) W i Y) :=
    measurable_const.mul (measurable_sectionMass (μ i) hW i)
  have hprod := lintegral_productLaw μ hW i hF
  have hwd : (∫⁻ Y, f Y ∂(outsideReference μ i).withDensity
      (fun Y ↦ (normalizer μ W)⁻¹ * sectionMass (μ i) W i Y)) =
      ∫⁻ Y, ((normalizer μ W)⁻¹ * sectionMass (μ i) W i Y) * f Y ∂outsideReference μ i :=
    lintegral_withDensity_eq_lintegral_mul (outsideReference μ i) hd hf
  rw [outsideMarginal, lintegral_map hf (measurable_removeSite i), hprod, hwd]
  simp only [removeSite_insertSite]
  have hinner (Y : Configuration n) :
      (∫⁻ z, density W (insertSite i z Y) * f Y ∂μ i) = sectionMass (μ i) W i Y * f Y :=
    lintegral_mul_const (f Y) (measurable_weightSection hW i Y).ennreal_ofReal
  simp_rw [hinner]
  have hmf : Measurable (fun Y : Configuration n ↦ sectionMass (μ i) W i Y * f Y) :=
    (measurable_sectionMass (μ i) hW i).mul hf
  rw [← lintegral_const_mul _ hmf]
  apply lintegral_congr
  intro Y
  exact (mul_assoc _ _ _).symm

theorem ae_sectionMass_ne_top (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1)) (hfin : normalizer μ W ≠ ⊤) :
    ∀ᵐ Y ∂outsideReference μ i, sectionMass (μ i) W i Y ≠ ⊤ := by
  rw [normalizer_eq_sections μ hW i] at hfin
  exact (ae_lt_top (measurable_sectionMass (μ i) hW i) hfin).mono fun _ h ↦ h.ne

theorem ae_marginal_sectionMass_ne_top (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1)) (hfin : normalizer μ W ≠ ⊤) :
    ∀ᵐ Y ∂outsideMarginal μ W i, sectionMass (μ i) W i Y ≠ ⊤ := by
  rw [outsideMarginal_eq μ hW i]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_sectionMass_ne_top μ hW i hfin)

theorem ae_marginal_sectionMass_pos_lt_top (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1))
    (hfin : normalizer μ W ≠ ⊤) :
    ∀ᵐ Y ∂outsideMarginal μ W i, 0 < sectionMass (μ i) W i Y ∧ sectionMass (μ i) W i Y < ⊤ :=
  (ae_marginal_sectionMass_ne_top μ hW i hfin).mono fun Y hY ↦
    ⟨pos_iff_ne_zero.mpr (sectionMass_ne_zero (μ i) hW hWpos i Y), lt_top_iff_ne_top.mpr hY⟩

theorem lintegral_disintegrate_sections (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1)) [NeZero (μ i)]
    (hfin : normalizer μ W ≠ ⊤)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productLaw μ W) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂sectionKernel (μ i) W hW i Y
        ∂outsideMarginal μ W i := by
  have hFi : Measurable (fun p : Configuration n × Torus ↦ F (insertSite i p.2 p.1)) :=
    hF.comp ((measurable_insertSite i).comp measurable_swap)
  have hm : Measurable (fun p : Configuration n × Torus ↦
      density W (insertSite i p.2 p.1) * F (insertSite i p.2 p.1)) :=
    (measurable_jointSection hW i).mul hFi
  have hinner : Measurable (fun Y : Configuration n ↦
      ∫⁻ z, density W (insertSite i z Y) * F (insertSite i z Y) ∂μ i) :=
    hm.lintegral_prod_right'
  have hd : Measurable (fun Y : Configuration n ↦
      (normalizer μ W)⁻¹ * sectionMass (μ i) W i Y) :=
    measurable_const.mul (measurable_sectionMass (μ i) hW i)
  rw [lintegral_productLaw μ hW i hF, outsideMarginal_eq μ hW i,
    lintegral_withDensity_eq_lintegral_mul (outsideReference μ i) hd
      (measurable_sectionIntegral (μ i) W hW i hF), ← lintegral_const_mul _ hinner]
  apply lintegral_congr_ae
  filter_upwards [ae_sectionMass_ne_top μ hW i hfin] with Y hY
  have hfixed : Measurable (fun z : Torus ↦ F (insertSite i z Y)) :=
    hFi.comp ((measurable_const (a := Y)).prodMk measurable_id)
  simp only [Pi.mul_apply]
  rw [lintegral_sectionKernel (μ i) W hW i Y hfixed]
  change _ = ((normalizer μ W)⁻¹ * sectionMass (μ i) W i Y) *
    ((sectionMass (μ i) W i Y)⁻¹ * _)
  rw [mul_assoc, ← mul_assoc (sectionMass (μ i) W i Y),
    ENNReal.mul_inv_cancel (sectionMass_ne_zero (μ i) hW hWpos i Y) hY, one_mul]

/-- Positivity is an explicit argument of the kernel, so its Markov
instance depends on precisely the proved hypothesis of the joint weight. -/
def conditionalKernel (μ : Measure Torus) [SFinite μ] (W : Configuration (n + 1) → ℝ)
    (hW : Measurable W) (_hWpos : ∀ X, 0 < W X) (i : Fin (n + 1)) :
    Kernel (Configuration n) Torus :=
  Kernel.piecewise (measurableSet_eq_fun (measurable_sectionMass μ hW i)
    (measurable_const (a := (⊤ : ℝ≥0∞))))
    (Kernel.const (Configuration n) (Measure.dirac (0 : Torus))) (sectionKernel μ W hW i)

theorem conditionalKernel_eq_section (μ : Measure Torus) [SFinite μ]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W) (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : sectionMass μ W i Y ≠ ⊤) :
    conditionalKernel μ W hW hWpos i Y = sectionKernel μ W hW i Y := by
  simp only [conditionalKernel, Kernel.piecewise_apply, Set.mem_ofPred_eq, hY, ite_false]

instance isMarkovKernel_conditionalKernel (μ : Measure Torus) [SFinite μ] [NeZero μ]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W) (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) : IsMarkovKernel (conditionalKernel μ W hW hWpos i) := by
  constructor
  intro Y
  by_cases hY : sectionMass μ W i Y = ⊤
  · simp only [conditionalKernel, Kernel.piecewise_apply, Set.mem_ofPred_eq, hY, ite_true,
      Kernel.const_apply]
    infer_instance
  · rw [conditionalKernel_eq_section μ W hW hWpos i Y hY, sectionKernel_eq_cond]
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, sectionMass] using
        sectionMass_ne_zero μ hW hWpos i Y
    · simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, sectionMass] using hY

theorem conditionalKernel_ae_eq_section (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1))
    (hfin : normalizer μ W ≠ ⊤) :
    ∀ᵐ Y ∂outsideMarginal μ W i,
      conditionalKernel (μ i) W hW hWpos i Y = sectionKernel (μ i) W hW i Y :=
  (ae_marginal_sectionMass_ne_top μ hW i hfin).mono fun Y hY ↦
    conditionalKernel_eq_section (μ i) W hW hWpos i Y hY

/-- Actual nonnegative-observable disintegration for the normalized law;
the observable may have infinite integral. -/
theorem lintegral_disintegrate (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1))
    (hfin : normalizer μ W ≠ ⊤)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productLaw μ W) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂conditionalKernel (μ i) W hW hWpos i Y
        ∂Measure.map (removeSite i) (productLaw μ W) := by
  rw [lintegral_disintegrate_sections μ hW hWpos i hfin hF]
  apply lintegral_congr_ae
  filter_upwards [conditionalKernel_ae_eq_section μ hW hWpos i hfin] with Y hY
  rw [hY]

theorem lintegral_disintegrate_of_integrable (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1))
    (hi : Integrable W (Measure.pi μ))
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productLaw μ W) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂conditionalKernel (μ i) W hW hWpos i Y
        ∂Measure.map (removeSite i) (productLaw μ W) :=
  lintegral_disintegrate μ hW hWpos i ((normalizer_ne_top_iff_integrable μ hW hWpos).mpr hi) hF

theorem outsideMarginal_probability (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (hfin : normalizer μ W ≠ ⊤)
    (i : Fin (n + 1)) : IsProbabilityMeasure (outsideMarginal μ W i) := by
  let hprob : IsProbabilityMeasure (productLaw μ W) := productLaw_probability μ hW hWpos hfin
  unfold outsideMarginal
  infer_instance

theorem divergent_sections_marginal_null (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (i : Fin (n + 1)) (hfin : normalizer μ W ≠ ⊤) :
    outsideMarginal μ W i {Y | sectionMass (μ i) W i Y = ⊤} = 0 := by
  have h := ae_iff.mp (ae_marginal_sectionMass_ne_top μ hW i hfin)
  simpa only [not_not] using h

theorem sectionMass_ne_top_of_integrable (μ : Measure Torus)
    {W : Configuration (n + 1) → ℝ} (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) (Y : Configuration n)
    (hi : Integrable (fun z ↦ W (insertSite i z Y)) μ) : sectionMass μ W i Y ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Eventually.of_forall fun z ↦ (hWpos (insertSite i z Y)).le)).mpr hi

theorem section_integral_pos (μ : Measure Torus) [NeZero μ]
    {W : Configuration (n + 1) → ℝ} (hW : Measurable W) (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) (Y : Configuration n)
    (hi : Integrable (fun z ↦ W (insertSite i z Y)) μ) :
    0 < ∫ z, W (insertSite i z Y) ∂μ := by
  have hmass : ENNReal.ofReal (∫ z, W (insertSite i z Y) ∂μ) = sectionMass μ W i Y :=
    ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun z ↦ (hWpos (insertSite i z Y)).le)
  apply ENNReal.ofReal_pos.mp
  rw [hmass]
  exact pos_iff_ne_zero.mpr (sectionMass_ne_zero μ hW hWpos i Y)

/-- The a.e. finite extended section is also an actually integrable real
section with a strictly positive real integral. -/
theorem ae_marginal_real_sections (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1))
    (hfin : normalizer μ W ≠ ⊤) :
    ∀ᵐ Y ∂outsideMarginal μ W i,
      Integrable (fun z ↦ W (insertSite i z Y)) (μ i) ∧
        0 < ∫ z, W (insertSite i z Y) ∂μ i := by
  filter_upwards [ae_marginal_sectionMass_ne_top μ hW i hfin] with Y hY
  have hi : Integrable (fun z ↦ W (insertSite i z Y)) (μ i) :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_weightSection hW i Y).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ (hWpos (insertSite i z Y)).le)).mp hY
  exact ⟨hi, section_integral_pos (μ i) hW hWpos i Y hi⟩

/-- Conversion to a real normalized density uses actual integrability and
the positive real normalizer, rather than totalized integral conventions. -/
theorem cond_withDensity_eq_real_density {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {V : A → ℝ} (hV : Measurable V) (hVnonneg : ∀ z, 0 ≤ V z)
    (hi : Integrable V μ) (hz : 0 < ∫ z, V z ∂μ) :
    ProbabilityTheory.cond (μ.withDensity (fun z ↦ ENNReal.ofReal (V z))) univ =
      μ.withDensity (fun z ↦ ENNReal.ofReal (V z / ∫ u, V u ∂μ)) := by
  have hmass := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hVnonneg)
  have hd : (fun z ↦ ENNReal.ofReal (V z / ∫ u, V u ∂μ)) =
      (ENNReal.ofReal (∫ u, V u ∂μ))⁻¹ • (fun z ↦ ENNReal.ofReal (V z)) := by
    funext z
    change ENNReal.ofReal (V z / ∫ u, V u ∂μ) =
      (ENNReal.ofReal (∫ u, V u ∂μ))⁻¹ * ENNReal.ofReal (V z)
    rw [ENNReal.ofReal_div_of_pos hz, div_eq_mul_inv, mul_comm]
  rw [hd, withDensity_smul _ hV.ennreal_ofReal]
  simp only [ProbabilityTheory.cond, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← hmass]

theorem productLaw_eq_real_density (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (hi : Integrable W (Measure.pi μ)) :
    productLaw μ W = (Measure.pi μ).withDensity
      (fun X ↦ ENNReal.ofReal (W X / ∫ Y, W Y ∂Measure.pi μ)) := by
  have he : productLaw μ W = ProbabilityTheory.cond ((Measure.pi μ).withDensity (density W)) univ := by
    simp only [productLaw, ProbabilityTheory.cond, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, normalizer]
  rw [he]
  exact cond_withDensity_eq_real_density _ hW (fun X ↦ (hWpos X).le) hi
    (integral_weight_pos μ hW hWpos hi)

theorem sectionMass_factor (μ : Measure Torus) {W : Configuration (n + 1) → ℝ}
    (i : Fin (n + 1)) (Y : Configuration n) {A : ℝ} (hA : 0 < A)
    {V : Torus → ℝ} (hV : Measurable V)
    (hfactor : ∀ z, W (insertSite i z Y) = A * V z) :
    sectionMass μ W i Y = ENNReal.ofReal A * ∫⁻ z, ENNReal.ofReal (V z) ∂μ := by
  unfold sectionMass density
  simp_rw [hfactor, ENNReal.ofReal_mul hA.le]
  exact lintegral_const_mul _ hV.ennreal_ofReal

/-- The finite positive outside scalar cancels at the level of the actual
normalized section, even before a real one-site integral is supplied. -/
theorem sectionKernel_factor_eq_cond (μ : Measure Torus) [SFinite μ]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W)
    (i : Fin (n + 1)) (Y : Configuration n) {A : ℝ} (hA : 0 < A)
    {V : Torus → ℝ} (hV : Measurable V)
    (hfactor : ∀ z, W (insertSite i z Y) = A * V z) :
    sectionKernel μ W hW i Y =
      ProbabilityTheory.cond (μ.withDensity (fun z ↦ ENNReal.ofReal (V z))) univ := by
  rw [sectionKernel_eq_cond]
  have hd : (fun z ↦ density W (insertSite i z Y)) =
      ENNReal.ofReal A • (fun z ↦ ENNReal.ofReal (V z)) := by
    funext z
    change ENNReal.ofReal (W (insertSite i z Y)) = ENNReal.ofReal A * ENNReal.ofReal (V z)
    rw [hfactor z, ENNReal.ofReal_mul hA.le]
  rw [hd, withDensity_smul _ hV.ennreal_ofReal]
  exact cond_smul _ _ (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top

theorem factor_pos {W : Configuration (n + 1) → ℝ} (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) (Y : Configuration n) {A : ℝ} (hA : 0 < A)
    {V : Torus → ℝ} (hfactor : ∀ z, W (insertSite i z Y) = A * V z) : ∀ z, 0 < V z := by
  intro z
  by_contra hz
  have hm := mul_nonpos_of_nonneg_of_nonpos hA.le (le_of_not_gt hz)
  rw [← hfactor z] at hm
  exact (not_le_of_gt (hWpos (insertSite i z Y))) hm

theorem conditionalKernel_factor_eq_real_density (μ : Measure Torus) [SFinite μ]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W) (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) (Y : Configuration n) {A : ℝ} (hA : 0 < A)
    {V : Torus → ℝ} (hV : Measurable V)
    (hfactor : ∀ z, W (insertSite i z Y) = A * V z)
    (hi : Integrable V μ) (hz : 0 < ∫ z, V z ∂μ) :
    conditionalKernel μ W hW hWpos i Y =
      μ.withDensity (fun z ↦ ENNReal.ofReal (V z / ∫ u, V u ∂μ)) := by
  have hsec : Integrable (fun z ↦ W (insertSite i z Y)) μ := by
    simp_rw [hfactor]
    exact hi.const_mul A
  rw [conditionalKernel_eq_section μ W hW hWpos i Y
    (sectionMass_ne_top_of_integrable μ hWpos i Y hsec),
    sectionKernel_factor_eq_cond μ W hW i Y hA hV hfactor]
  exact cond_withDensity_eq_real_density μ hV
    (fun z ↦ (factor_pos hWpos i Y hA hfactor z).le) hi hz

/-- The precise interface for a deleted interaction's point-source weight.
The source weights may be zero; all analytic premises refer to the actual
point weight and actual normalized site measure. -/
theorem conditionalKernel_factor_eq_pointLaw {ι : Type*} [Fintype ι]
    (μ : Measure Torus) [SFinite μ] (W : Configuration (n + 1) → ℝ)
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X)
    (i : Fin (n + 1)) (Y : Configuration n) {A : ℝ} (hA : 0 < A)
    (y : ι → Torus) (w : ι → ℝ)
    (hfactor : ∀ z, W (insertSite i z Y) = A * torusWeight y w z)
    (hi : Integrable (torusWeight y w) μ) (hz : 0 < ∫ z, torusWeight y w z ∂μ) :
    conditionalKernel μ W hW hWpos i Y = pointLaw μ y w := by
  simpa only [pointLaw, pointDensity] using
    conditionalKernel_factor_eq_real_density μ W hW hWpos i Y hA
      (measurable_torusWeight y w) hfactor hi hz

theorem conditionalKernel_ae_eq_real_density (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1))
    (hfin : normalizer μ W ≠ ⊤) :
    ∀ᵐ Y ∂outsideMarginal μ W i, conditionalKernel (μ i) W hW hWpos i Y =
      (μ i).withDensity (fun z ↦ ENNReal.ofReal
        (W (insertSite i z Y) / ∫ u, W (insertSite i u Y) ∂μ i)) := by
  filter_upwards [ae_marginal_real_sections μ hW hWpos i hfin] with Y hY
  exact conditionalKernel_factor_eq_real_density (μ i) W hW hWpos i Y (A := 1)
    (by norm_num) (measurable_weightSection hW i Y) (fun z ↦ (one_mul _).symm) hY.1 hY.2

/-- The same disintegration written with the literal real section
normalizer. Bad sections have already been proved marginal-null. -/
theorem lintegral_disintegrate_real_density (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] {W : Configuration (n + 1) → ℝ}
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1))
    (hfin : normalizer μ W ≠ ⊤)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productLaw μ W) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
        ∂(μ i).withDensity (fun z ↦ ENNReal.ofReal
          (W (insertSite i z Y) / ∫ u, W (insertSite i u Y) ∂μ i))
        ∂Measure.map (removeSite i) (productLaw μ W) := by
  rw [lintegral_disintegrate μ hW hWpos i hfin hF]
  apply lintegral_congr_ae
  filter_upwards [conditionalKernel_ae_eq_real_density μ hW hWpos i hfin] with Y hY
  rw [hY]

/-- The family directly consumed by the checked L2/subtype bridge. -/
def coordinateKernels (μ : Fin (n + 1) → Measure Torus) [∀ j, IsProbabilityMeasure (μ j)]
    (W : Configuration (n + 1) → ℝ) (hW : Measurable W) (hWpos : ∀ X, 0 < W X) :
    Fin (n + 1) → Kernel (Configuration (n + 1)) Torus :=
  CoordinateConditionalKernels.finLift fun i ↦ conditionalKernel (μ i) W hW hWpos i

instance isMarkovKernel_coordinateKernels (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] (W : Configuration (n + 1) → ℝ)
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (i : Fin (n + 1)) :
    IsMarkovKernel (coordinateKernels μ W hW hWpos i) := by
  unfold coordinateKernels
  infer_instance

theorem independentSite_coordinateKernels (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] (W : Configuration (n + 1) → ℝ)
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) :
    CoordinateOscillation.IndependentSite (coordinateKernels μ W hW hWpos) :=
  CoordinateConditionalKernels.independentSite_finLift _

theorem preservesLaw_coordinateKernels (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] (W : Configuration (n + 1) → ℝ)
    (hW : Measurable W) (hWpos : ∀ X, 0 < W X) (hfin : normalizer μ W ≠ ⊤) :
    ConditionalKernelL2.PreservesLaw (coordinateKernels μ W hW hWpos) (productLaw μ W) := by
  let hprob : IsProbabilityMeasure (productLaw μ W) := productLaw_probability μ hW hWpos hfin
  apply CoordinateConditionalKernels.preservesLaw_finLift
  intro i F hF
  exact lintegral_disintegrate μ hW hWpos i hfin hF

end PeriodicAttractiveLogGas.PositiveProductConditionals
