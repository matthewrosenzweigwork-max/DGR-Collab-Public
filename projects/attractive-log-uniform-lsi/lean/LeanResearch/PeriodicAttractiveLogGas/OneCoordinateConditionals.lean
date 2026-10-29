import LeanResearch.PeriodicAttractiveLogGas.CellRestrictions
import LeanResearch.PeriodicAttractiveLogGas.OneSiteConstants
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Fin

/-! The one-coordinate conditional-version step
in source Proposition 3.4. The joint density is split using the actual
coordinate measurable equivalence and Tonelli; its outside marginal is an
actual pushforward, not an asserted smaller Gibbs ensemble. The pointwise
even Green representative is used for energy splitting, and its equality
with the source ensemble is transferred by the proved Haar-a.e. identity.
-/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.OneCoordinateConditionals

open MeshCells MeshAdjacentCells CellRestrictions GreenPointWeights
  LabelOccupations ConditionalParameters

instance isProbabilityMeasure_patchMeasure (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    IsProbabilityMeasure (patchMeasure J hJ a b) := patchMeasure_probability J hJ a b

def siteEquiv {n : ℕ} (i : Fin (n + 1)) :
    Configuration (n + 1) ≃ᵐ Torus × Configuration n :=
  MeasurableEquiv.piFinSuccAbove (fun _ ↦ Torus) i

def insertSite {n : ℕ} (i : Fin (n + 1)) (z : Torus) (Y : Configuration n) :
    Configuration (n + 1) := i.insertNth z Y

def removeSite {n : ℕ} (i : Fin (n + 1)) (X : Configuration (n + 1)) :
    Configuration n := fun j ↦ X (i.succAbove j)

theorem siteEquiv_symm_apply {n : ℕ} (i : Fin (n + 1)) (p : Torus × Configuration n) :
    (siteEquiv i).symm p = insertSite i p.1 p.2 := rfl

@[simp] theorem insertSite_self {n : ℕ} (i : Fin (n + 1)) (z : Torus) (Y : Configuration n) :
    insertSite i z Y i = z := Fin.insertNth_apply_same (α := fun _ ↦ Torus) i z Y

@[simp] theorem insertSite_succAbove {n : ℕ} (i : Fin (n + 1)) (z : Torus)
    (Y : Configuration n) (j : Fin n) : insertSite i z Y (i.succAbove j) = Y j :=
  Fin.insertNth_apply_succAbove (α := fun _ ↦ Torus) i z Y j

@[simp] theorem removeSite_insertSite {n : ℕ} (i : Fin (n + 1)) (z : Torus)
    (Y : Configuration n) : removeSite i (insertSite i z Y) = Y := by
  funext j
  exact insertSite_succAbove i z Y j

@[simp] theorem insertSite_removeSite {n : ℕ} (i : Fin (n + 1))
    (X : Configuration (n + 1)) : insertSite i (X i) (removeSite i X) = X :=
  (siteEquiv i).symm_apply_apply X

theorem measurable_insertSite {n : ℕ} (i : Fin (n + 1)) :
    Measurable (fun p : Torus × Configuration n ↦ insertSite i p.1 p.2) :=
  (siteEquiv i).symm.measurable

theorem measurable_removeSite {n : ℕ} (i : Fin (n + 1)) : Measurable (removeSite i) :=
  measurable_pi_iff.mpr fun j ↦ measurable_pi_apply (i.succAbove j)

def outsideReference {n : ℕ} (μ : Fin (n + 1) → Measure Torus) (i : Fin (n + 1)) :
    Measure (Configuration n) := Measure.pi fun j ↦ μ (i.succAbove j)

instance sigmaFinite_outsideReference {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) : SigmaFinite (outsideReference μ i) := by
  unfold outsideReference
  infer_instance

instance isProbabilityMeasure_outsideReference {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, IsProbabilityMeasure (μ j)] (i : Fin (n + 1)) :
    IsProbabilityMeasure (outsideReference μ i) := by
  unfold outsideReference
  infer_instance

theorem lintegral_pi_insert {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1))
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂Measure.pi μ) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂μ i ∂outsideReference μ i := by
  have hmp := (measurePreserving_piFinSuccAbove μ i).symm
  calc
    _ = ∫⁻ p : Torus × Configuration n, F (insertSite i p.1 p.2)
        ∂(μ i).prod (outsideReference μ i) := (hmp.lintegral_comp hF).symm
    _ = _ := lintegral_prod_symm _ (hF.comp (measurable_insertSite i)).aemeasurable

def jointDensity (N : ℕ) (β : ℝ) (X : Configuration N) : ℝ≥0∞ :=
  ENNReal.ofReal (gibbsWeight regularGreenRepresentative N β X)

theorem measurable_jointDensity (N : ℕ) (β : ℝ) : Measurable (jointDensity N β) :=
  (measurable_gibbsWeight regularGreenRepresentative_measurable N β).ennreal_ofReal

theorem jointDensity_pos (N : ℕ) (β : ℝ) (X : Configuration N) :
    0 < jointDensity N β X := ENNReal.ofReal_pos.mpr (gibbsWeight_pos _ _ _ _)

theorem measurable_jointSection {n : ℕ} (i : Fin (n + 1)) (β : ℝ) :
    Measurable (fun p : Configuration n × Torus ↦ jointDensity (n + 1) β (insertSite i p.2 p.1)) :=
  (measurable_jointDensity _ β).comp ((measurable_insertSite i).comp measurable_swap)

def sectionMass {n : ℕ} (μ : Measure Torus) (i : Fin (n + 1)) (β : ℝ)
    (Y : Configuration n) : ℝ≥0∞ := ∫⁻ z, jointDensity (n + 1) β (insertSite i z Y) ∂μ

theorem measurable_sectionMass {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) : Measurable (sectionMass μ i β) :=
  (measurable_jointSection i β).lintegral_prod_right

theorem sectionMass_ne_zero {n : ℕ} (μ : Measure Torus) [NeZero μ]
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) : sectionMass μ i β Y ≠ 0 := by
  intro h
  have hm := (measurable_jointSection i β).comp ((measurable_const (a := Y)).prodMk measurable_id)
  have hae := (lintegral_eq_zero_iff hm).mp h
  obtain ⟨z, hz⟩ := hae.exists
  exact (jointDensity_pos _ β (insertSite i z Y)).ne' hz

/-- The normalized actual joint-density section. It may be zero at a
divergent section; the Markov version below replaces just those sections. -/
def sectionKernel {n : ℕ} (μ : Measure Torus) [SFinite μ] (i : Fin (n + 1)) (β : ℝ) :
    Kernel (Configuration n) Torus where
  toFun Y := (sectionMass μ i β Y)⁻¹ •
    μ.withDensity (fun z ↦ jointDensity (n + 1) β (insertSite i z Y))
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
    exact (measurable_sectionMass μ i β).inv.mul
      ((measurable_jointSection i β).lintegral_prod_right (ν := μ.restrict s))

theorem sectionKernel_eq_cond {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) :
    sectionKernel μ i β Y = ProbabilityTheory.cond
      (μ.withDensity (fun z ↦ jointDensity (n + 1) β (insertSite i z Y))) univ := by
  change (sectionMass μ i β Y)⁻¹ •
    μ.withDensity (fun z ↦ jointDensity (n + 1) β (insertSite i z Y)) = _
  simp only [ProbabilityTheory.cond, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, sectionMass]

theorem lintegral_sectionKernel {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) {f : Torus → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ z, f z ∂sectionKernel μ i β Y) = (sectionMass μ i β Y)⁻¹ *
      ∫⁻ z, jointDensity (n + 1) β (insertSite i z Y) * f z ∂μ := by
  have hs : Measurable (fun z : Torus ↦ jointDensity (n + 1) β (insertSite i z Y)) :=
    (measurable_jointDensity (n + 1) β).comp
      (show Measurable (fun z : Torus ↦ insertSite i z Y) from
        (measurable_insertSite i).comp
          (show Measurable (fun z : Torus ↦ (z, Y)) from measurable_prodMk_right))
  change (∫⁻ z, f z ∂(sectionMass μ i β Y)⁻¹ •
    μ.withDensity (fun z ↦ jointDensity (n + 1) β (insertSite i z Y))) = _
  rw [lintegral_smul_measure, smul_eq_mul]
  have hh : (∫⁻ z, f z ∂μ.withDensity (fun z ↦ jointDensity (n + 1) β (insertSite i z Y))) =
      ∫⁻ z, jointDensity (n + 1) β (insertSite i z Y) * f z ∂μ :=
    lintegral_withDensity_eq_lintegral_mul μ hs hf
  exact congrArg (fun t : ℝ≥0∞ ↦ (sectionMass μ i β Y)⁻¹ * t)
    hh

theorem measurable_sectionIntegral {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun Y ↦ ∫⁻ z, F (insertSite i z Y) ∂sectionKernel μ i β Y) := by
  have hFi : Measurable (fun p : Configuration n × Torus ↦ F (insertSite i p.2 p.1)) :=
    hF.comp ((measurable_insertSite i).comp measurable_swap)
  have hfixed (Y : Configuration n) : Measurable (fun z : Torus ↦ F (insertSite i z Y)) :=
    hFi.comp ((measurable_const (a := Y)).prodMk measurable_id)
  have he (Y : Configuration n) := lintegral_sectionKernel μ i β Y (hfixed Y)
  simp_rw [he]
  have hm : Measurable (fun p : Configuration n × Torus ↦
      jointDensity (n + 1) β (insertSite i p.2 p.1) * F (insertSite i p.2 p.1)) :=
    (measurable_jointSection i β).mul hFi
  exact (measurable_sectionMass μ i β).inv.mul
    hm.lintegral_prod_right'

def productNormalizer {n : ℕ} (μ : Fin (n + 1) → Measure Torus) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ X, jointDensity (n + 1) β X ∂Measure.pi μ

def productGibbs {n : ℕ} (μ : Fin (n + 1) → Measure Torus) (β : ℝ) :
    Measure (Configuration (n + 1)) :=
  (productNormalizer μ β)⁻¹ • (Measure.pi μ).withDensity (jointDensity (n + 1) β)

/-- This is the actual outside pushforward; no Gibbs form is assigned to it. -/
def outsideMarginal {n : ℕ} (μ : Fin (n + 1) → Measure Torus) (i : Fin (n + 1)) (β : ℝ) :
    Measure (Configuration n) := Measure.map (removeSite i) (productGibbs μ β)

theorem productNormalizer_eq_sections {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) (β : ℝ) :
    productNormalizer μ β = ∫⁻ Y, sectionMass (μ i) i β Y ∂outsideReference μ i :=
  lintegral_pi_insert μ i (measurable_jointDensity _ β)

theorem lintegral_productGibbs {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) (β : ℝ)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productGibbs μ β) = (productNormalizer μ β)⁻¹ *
      ∫⁻ Y, ∫⁻ z, jointDensity (n + 1) β (insertSite i z Y) * F (insertSite i z Y)
        ∂μ i ∂outsideReference μ i := by
  rw [productGibbs, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_jointDensity _ β) hF]
  congr 1
  exact lintegral_pi_insert μ i ((measurable_jointDensity _ β).mul hF)

theorem outsideMarginal_eq {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) (β : ℝ) :
    outsideMarginal μ i β = (outsideReference μ i).withDensity
      (fun Y ↦ (productNormalizer μ β)⁻¹ * sectionMass (μ i) i β Y) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hsec (Y : Configuration n) :
      Measurable (fun z : Torus ↦ jointDensity (n + 1) β (insertSite i z Y)) :=
    (measurable_jointDensity (n + 1) β).comp
      (show Measurable (fun z : Torus ↦ insertSite i z Y) from
        (measurable_insertSite i).comp
          (show Measurable (fun z : Torus ↦ (z, Y)) from measurable_prodMk_right))
  have hF : Measurable (fun X : Configuration (n + 1) ↦ f (removeSite i X)) :=
    hf.comp (measurable_removeSite i)
  have hd : Measurable (fun Y : Configuration n ↦
      (productNormalizer μ β)⁻¹ * sectionMass (μ i) i β Y) :=
    measurable_const.mul (measurable_sectionMass (μ i) i β)
  have hprod := lintegral_productGibbs μ i β hF
  have hwd : (∫⁻ Y, f Y ∂(outsideReference μ i).withDensity
      (fun Y ↦ (productNormalizer μ β)⁻¹ * sectionMass (μ i) i β Y)) =
      ∫⁻ Y, ((productNormalizer μ β)⁻¹ * sectionMass (μ i) i β Y) * f Y
        ∂outsideReference μ i :=
    lintegral_withDensity_eq_lintegral_mul (outsideReference μ i) hd hf
  rw [outsideMarginal, lintegral_map hf (measurable_removeSite i), hprod, hwd]
  simp only [removeSite_insertSite]
  have hinner (Y : Configuration n) :
      (∫⁻ z, jointDensity (n + 1) β (insertSite i z Y) * f Y ∂μ i) =
        sectionMass (μ i) i β Y * f Y := lintegral_mul_const (f Y) (hsec Y)
  simp_rw [hinner]
  have hmf : Measurable (fun Y : Configuration n ↦ sectionMass (μ i) i β Y * f Y) :=
    (measurable_sectionMass (μ i) i β).mul hf
  rw [← lintegral_const_mul _ hmf]
  apply lintegral_congr
  intro Y
  exact (mul_assoc _ _ _).symm

theorem ae_sectionMass_ne_top {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) (β : ℝ)
    (hfin : productNormalizer μ β ≠ ⊤) :
    ∀ᵐ Y ∂outsideReference μ i, sectionMass (μ i) i β Y ≠ ⊤ := by
  rw [productNormalizer_eq_sections μ i β] at hfin
  exact (ae_lt_top (measurable_sectionMass (μ i) i β) hfin).mono fun _ h ↦ h.ne

theorem ae_marginal_sectionMass_ne_top {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) (β : ℝ)
    (hfin : productNormalizer μ β ≠ ⊤) :
    ∀ᵐ Y ∂outsideMarginal μ i β, sectionMass (μ i) i β Y ≠ ⊤ := by
  rw [outsideMarginal_eq]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_sectionMass_ne_top μ i β hfin)

/-- The actual nonnegative-observable disintegration. It is an extended
integral identity and needs no artificial integrability assumption on F. -/
theorem lintegral_disintegrate_sections {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) [NeZero (μ i)] (β : ℝ)
    (hfin : productNormalizer μ β ≠ ⊤)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productGibbs μ β) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂sectionKernel (μ i) i β Y
        ∂outsideMarginal μ i β := by
  have hFi : Measurable (fun p : Configuration n × Torus ↦ F (insertSite i p.2 p.1)) :=
    hF.comp ((measurable_insertSite i).comp measurable_swap)
  have hm : Measurable (fun p : Configuration n × Torus ↦
      jointDensity (n + 1) β (insertSite i p.2 p.1) * F (insertSite i p.2 p.1)) :=
    (measurable_jointSection i β).mul hFi
  have hinner : Measurable (fun Y : Configuration n ↦
      ∫⁻ z, jointDensity (n + 1) β (insertSite i z Y) * F (insertSite i z Y) ∂μ i) :=
    hm.lintegral_prod_right'
  have hd : Measurable (fun Y : Configuration n ↦
      (productNormalizer μ β)⁻¹ * sectionMass (μ i) i β Y) :=
    measurable_const.mul (measurable_sectionMass (μ i) i β)
  rw [lintegral_productGibbs μ i β hF, outsideMarginal_eq,
    lintegral_withDensity_eq_lintegral_mul (outsideReference μ i) hd
      (measurable_sectionIntegral (μ i) i β hF), ← lintegral_const_mul _ hinner]
  apply lintegral_congr_ae
  filter_upwards [ae_sectionMass_ne_top μ i β hfin] with Y hY
  have hfixed : Measurable (fun z : Torus ↦ F (insertSite i z Y)) :=
    hFi.comp ((measurable_const (a := Y)).prodMk measurable_id)
  simp only [Pi.mul_apply]
  rw [lintegral_sectionKernel (μ i) i β Y hfixed]
  change _ = ((productNormalizer μ β)⁻¹ * sectionMass (μ i) i β Y) *
    ((sectionMass (μ i) i β Y)⁻¹ * _)
  rw [mul_assoc, ← mul_assoc (sectionMass (μ i) i β Y),
    ENNReal.mul_inv_cancel (sectionMass_ne_zero (μ i) i β Y) hY, one_mul]

/-- A genuine Markov version, with an explicit harmless value only on
divergent sections. The exceptional sections have zero actual marginal mass. -/
def conditionalKernel {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) : Kernel (Configuration n) Torus :=
  Kernel.piecewise (measurableSet_eq_fun (measurable_sectionMass μ i β)
    (measurable_const (a := (⊤ : ℝ≥0∞))))
    (Kernel.const (Configuration n) (Measure.dirac (0 : Torus))) (sectionKernel μ i β)

theorem conditionalKernel_eq_section {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) (hY : sectionMass μ i β Y ≠ ⊤) :
    conditionalKernel μ i β Y = sectionKernel μ i β Y := by
  simp only [conditionalKernel, Kernel.piecewise_apply, Set.mem_ofPred_eq, hY, ite_false]

instance isMarkovKernel_conditionalKernel {n : ℕ} (μ : Measure Torus) [SFinite μ] [NeZero μ]
    (i : Fin (n + 1)) (β : ℝ) : IsMarkovKernel (conditionalKernel μ i β) := by
  constructor
  intro Y
  by_cases hY : sectionMass μ i β Y = ⊤
  · simp only [conditionalKernel, Kernel.piecewise_apply, Set.mem_ofPred_eq, hY, ite_true,
      Kernel.const_apply]
    infer_instance
  · rw [conditionalKernel_eq_section μ i β Y hY, sectionKernel_eq_cond]
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, sectionMass] using
        sectionMass_ne_zero μ i β Y
    · simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, sectionMass] using hY

theorem lintegral_disintegrate {n : ℕ} (μ : Fin (n + 1) → Measure Torus)
    [∀ j, SigmaFinite (μ j)] (i : Fin (n + 1)) [NeZero (μ i)] (β : ℝ)
    (hfin : productNormalizer μ β ≠ ⊤)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂productGibbs μ β) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂conditionalKernel (μ i) i β Y
        ∂outsideMarginal μ i β := by
  rw [lintegral_disintegrate_sections μ i β hfin hF]
  apply lintegral_congr_ae
  filter_upwards [ae_marginal_sectionMass_ne_top μ i β hfin] with Y hY
  rw [conditionalKernel_eq_section (μ i) i β Y hY]

theorem pairEnergy_eq_sum_ite (g : Torus → ℝ) (N : ℕ) (X : Configuration N) :
    pairEnergy g N X = ∑ p, ∑ q, if p < q then g (X p - X q) else 0 := by
  classical
  unfold pairEnergy
  apply Finset.sum_congr rfl
  intro p _
  have hs : Finset.Ioi p = Finset.univ.filter (fun q : Fin N ↦ p < q) := by
    ext q
    simp
  rw [hs, Finset.sum_filter]

/-- The unordered-pair convention is retained exactly; the factor two is
proved by pairing the two orientations using the actual evenness hypothesis. -/
theorem two_mul_pairEnergy (g : Torus → ℝ) (heven : ∀ z, g (-z) = g z)
    (N : ℕ) (X : Configuration N) :
    2 * pairEnergy g N X = ∑ p, ∑ q, if p = q then 0 else g (X p - X q) := by
  classical
  have hs : ∀ p q : Fin N,
      (if p = q then 0 else g (X p - X q)) =
        (if p < q then g (X p - X q) else 0) +
        (if q < p then g (X q - X p) else 0) := by
    intro p q
    by_cases hpq : p = q
    · subst q
      simp
    · rcases lt_or_gt_of_ne hpq with hlt | hgt
      · simp [hpq, hlt, (not_lt_of_ge hlt.le)]
      · have he : g (X q - X p) = g (X p - X q) := by
          simpa only [neg_sub] using heven (X p - X q)
        simp [hpq, hgt, (not_lt_of_ge hgt.le), he]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun p q : Fin N ↦ if q < p then g (X q - X p) else 0),
    ← pairEnergy_eq_sum_ite]
  ring

theorem pairEnergy_insertSite (g : Torus → ℝ) (heven : ∀ z, g (-z) = g z)
    {n : ℕ} (i : Fin (n + 1)) (z : Torus) (Y : Configuration n) :
    pairEnergy g (n + 1) (insertSite i z Y) =
      pairEnergy g n Y + ∑ j, g (z - Y j) := by
  classical
  have h := two_mul_pairEnergy g heven (n + 1) (insertSite i z Y)
  rw [Fin.sum_univ_succAbove _ i] at h
  have hrow : (∑ q : Fin (n + 1),
      if i = q then 0 else g (insertSite i z Y i - insertSite i z Y q)) =
      ∑ j : Fin n, g (z - Y j) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [ite_true, zero_add, Fin.ne_succAbove, ite_false,
      insertSite_self, insertSite_succAbove]
  have hother (j : Fin n) : (∑ q : Fin (n + 1),
      if i.succAbove j = q then 0 else
        g (insertSite i z Y (i.succAbove j) - insertSite i z Y q)) =
      g (z - Y j) + ∑ k : Fin n, if j = k then 0 else g (Y j - Y k) := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.succAbove_ne, ite_false, insertSite_self, insertSite_succAbove,
      Fin.succAbove_right_inj]
    congr 1
    simpa only [neg_sub] using heven (z - Y j)
  rw [hrow] at h
  simp_rw [hother] at h
  rw [Finset.sum_add_distrib, ← two_mul_pairEnergy g heven n Y] at h
  linarith

def sourceWeight {n : ℕ} (β : ℝ) (Y : Configuration n) (z : Torus) : ℝ :=
  torusWeight Y (fun _ ↦ β / (n + 1 : ℕ)) z

def outsideWeight {n : ℕ} (β : ℝ) (Y : Configuration n) : ℝ :=
  Real.exp ((β / (n + 1 : ℕ)) * pairEnergy regularGreenRepresentative n Y)

theorem measurable_sourceWeight {n : ℕ} (β : ℝ) (Y : Configuration n) :
    Measurable (sourceWeight β Y) := measurable_torusWeight Y _

theorem sourceWeight_pos {n : ℕ} (β : ℝ) (Y : Configuration n) (z : Torus) :
    0 < sourceWeight β Y z := torusWeight_pos Y _ z

/-- The outside term keeps denominator n+1. It is not identified with
the n-particle Gibbs law at the original coupling. -/
theorem gibbsWeight_insertSite {n : ℕ} (i : Fin (n + 1)) (β : ℝ)
    (z : Torus) (Y : Configuration n) :
    gibbsWeight regularGreenRepresentative (n + 1) β (insertSite i z Y) =
      outsideWeight β Y * sourceWeight β Y z := by
  rw [gibbsWeight, pairEnergy_insertSite _ regularGreenRepresentative_even,
    mul_add, Real.exp_add]
  congr 1
  unfold sourceWeight torusWeight
  rw [Finset.mul_sum]

theorem jointDensity_insertSite {n : ℕ} (i : Fin (n + 1)) (β : ℝ)
    (z : Torus) (Y : Configuration n) :
    jointDensity (n + 1) β (insertSite i z Y) =
      ENNReal.ofReal (outsideWeight β Y) * ENNReal.ofReal (sourceWeight β Y z) := by
  have hw : 0 ≤ outsideWeight β Y := (Real.exp_pos _).le
  rw [jointDensity, gibbsWeight_insertSite, ENNReal.ofReal_mul hw]

/-- Exact cancellation of the finite positive outside-energy factor,
valid even before one-site integrability is established. -/
theorem sectionKernel_eq_source_cond {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) :
    sectionKernel μ i β Y = ProbabilityTheory.cond
      (μ.withDensity (fun z ↦ ENNReal.ofReal (sourceWeight β Y z))) univ := by
  rw [sectionKernel_eq_cond]
  have hd : (fun z ↦ jointDensity (n + 1) β (insertSite i z Y)) =
      ENNReal.ofReal (outsideWeight β Y) • (fun z ↦ ENNReal.ofReal (sourceWeight β Y z)) := by
    funext z
    exact jointDensity_insertSite i β z Y
  rw [hd, withDensity_smul _ (measurable_sourceWeight β Y).ennreal_ofReal]
  exact cond_smul _ _ (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top

theorem source_cond_eq_pointLaw {n : ℕ} (μ : Measure Torus) (β : ℝ) (Y : Configuration n)
    (hi : Integrable (sourceWeight β Y) μ) (hz : 0 < ∫ z, sourceWeight β Y z ∂μ) :
    ProbabilityTheory.cond (μ.withDensity (fun z ↦ ENNReal.ofReal (sourceWeight β Y z))) univ =
      pointLaw μ Y (fun _ ↦ β / (n + 1 : ℕ)) := by
  have hmass := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z ↦ (sourceWeight_pos β Y z).le)
  have hd : (fun z ↦ ENNReal.ofReal (pointDensity μ Y (fun _ ↦ β / (n + 1 : ℕ)) z)) =
      (ENNReal.ofReal (∫ z, sourceWeight β Y z ∂μ))⁻¹ •
        (fun z ↦ ENNReal.ofReal (sourceWeight β Y z)) := by
    funext z
    change ENNReal.ofReal (sourceWeight β Y z / ∫ u, sourceWeight β Y u ∂μ) =
      (ENNReal.ofReal (∫ u, sourceWeight β Y u ∂μ))⁻¹ * ENNReal.ofReal (sourceWeight β Y z)
    rw [ENNReal.ofReal_div_of_pos hz, div_eq_mul_inv, mul_comm]
  rw [pointLaw, hd, withDensity_smul _ (measurable_sourceWeight β Y).ennreal_ofReal]
  simp only [ProbabilityTheory.cond, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← hmass]

theorem sectionMass_ne_top_of_source_integrable {n : ℕ} (μ : Measure Torus)
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n)
    (hi : Integrable (sourceWeight β Y) μ) : sectionMass μ i β Y ≠ ⊤ := by
  have hw : Integrable (fun z ↦ gibbsWeight regularGreenRepresentative (n + 1) β
      (insertSite i z Y)) μ := by
    simp_rw [gibbsWeight_insertSite]
    exact hi.const_mul _
  exact (lintegral_ofReal_ne_top_iff_integrable hw.aestronglyMeasurable
    (Eventually.of_forall fun z ↦ (gibbsWeight_pos _ _ _ _).le)).mpr hw

theorem conditionalKernel_eq_pointLaw {n : ℕ} (μ : Measure Torus) [SFinite μ]
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n)
    (hi : Integrable (sourceWeight β Y) μ) (hz : 0 < ∫ z, sourceWeight β Y z ∂μ) :
    conditionalKernel μ i β Y = pointLaw μ Y (fun _ ↦ β / (n + 1 : ℕ)) := by
  rw [conditionalKernel_eq_section μ i β Y
    (sectionMass_ne_top_of_source_integrable μ i β Y hi), sectionKernel_eq_source_cond]
  exact source_cond_eq_pointLaw μ β Y hi hz

def rawSourceWeight {n : ℕ} (β : ℝ) (Y : Configuration n) (z : Torus) : ℝ :=
  Real.exp (∑ j, (β / (n + 1 : ℕ)) * greenRealRepresentative (z - Y j))

/-- Representative transfer for every fixed outside placement, not just
for almost every joint configuration. Coincident sources cause no exception. -/
theorem sourceWeight_ae_rawSourceWeight {n : ℕ} (β : ℝ) (Y : Configuration n) :
    sourceWeight β Y =ᵐ[torusMeasure] rawSourceWeight β Y := by
  have h : ∀ᵐ z ∂torusMeasure, ∀ j : Fin n,
      regularGreenRepresentative (z - Y j) = greenRealRepresentative (z - Y j) := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_sub_right torusMeasure (Y j)).quasiMeasurePreserving.ae_eq_comp
      regularGreenRepresentative_ae
  filter_upwards [h] with z hz
  unfold sourceWeight torusWeight rawSourceWeight
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hz j]

theorem source_cond_eq_rawSource_cond {n : ℕ} (μ : Measure Torus)
    (hμ : μ ≪ torusMeasure) (β : ℝ) (Y : Configuration n) :
    ProbabilityTheory.cond (μ.withDensity (fun z ↦ ENNReal.ofReal (sourceWeight β Y z))) univ =
      ProbabilityTheory.cond (μ.withDensity (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z))) univ := by
  congr 1
  have hae : sourceWeight β Y =ᵐ[μ] rawSourceWeight β Y :=
    hμ.ae_le (sourceWeight_ae_rawSourceWeight β Y)
  exact withDensity_congr_ae (hae.mono
    fun _ he ↦ congrArg ENNReal.ofReal he)

def patchDomain (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) : Set Torus :=
  TorusPatchDensity.domain (LocalPointEstimates.shape b) J hJ a

def patchScale (J : ℕ) : Patch → ℝ≥0∞
  | .cell => (J : ℝ≥0∞) ^ 2
  | .edge _ => (J : ℝ≥0∞) ^ 2 / 2

theorem measurableSet_patchDomain (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    MeasurableSet (patchDomain J hJ a b) := by
  cases b with
  | cell => exact measurableSet_meshCell J hJ a
  | edge j => exact measurableSet_edgeCellUnion J hJ a j

theorem patchScale_ne_zero {J : ℕ} (hJ : 0 < J) (b : Patch) : patchScale J b ≠ 0 := by
  have hJ0 : (J : ℝ≥0∞) ≠ 0 := by exact_mod_cast hJ.ne'
  cases b <;> simp [patchScale, div_eq_mul_inv, hJ0]

theorem patchScale_ne_top (J : ℕ) (b : Patch) : patchScale J b ≠ ⊤ := by
  cases b <;> dsimp [patchScale] <;> finiteness

theorem patchMeasure_eq_scaled (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) :
    patchMeasure J hJ a b = patchScale J b • torusMeasure.restrict (patchDomain J hJ a b) := by
  cases b with
  | cell => rfl
  | edge j => exact edgeCellMeasure_eq_normalized J hJ hJ2 a j

theorem patchMeasure_absolutelyContinuous (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) : patchMeasure J hJ a b ≪ torusMeasure := by
  rw [patchMeasure_eq_scaled J hJ hJ2 a b]
  exact Measure.absolutelyContinuous_restrict.smul_left _

def patchProductEvent {N J : ℕ} (hJ : 0 < J) (a : Fin N → MeshIndex J)
    (b : Fin N → Patch) : Set (Configuration N) :=
  Set.pi univ fun k ↦ patchDomain J hJ (a k) (b k)

theorem measurableSet_patchProductEvent {N J : ℕ} (hJ : 0 < J)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) : MeasurableSet (patchProductEvent hJ a b) :=
  MeasurableSet.univ_pi fun k ↦ measurableSet_patchDomain J hJ (a k) (b k)

theorem pi_patchMeasure_eq {N J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin N → MeshIndex J) (b : Fin N → Patch) :
    (Measure.pi fun k ↦ patchMeasure J hJ (a k) (b k)) =
      (∏ k, patchScale J (b k)) • (referenceMeasure N).restrict (patchProductEvent hJ a b) := by
  apply Measure.pi_eq
  intro s hs
  have hcell (k : Fin N) : patchMeasure J hJ (a k) (b k) (s k) =
      patchScale J (b k) * torusMeasure (s k ∩ patchDomain J hJ (a k) (b k)) := by
    rw [patchMeasure_eq_scaled J hJ hJ2, Measure.smul_apply,
      Measure.restrict_apply (hs k), smul_eq_mul]
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  rw [patchProductEvent, ← Set.pi_inter_distrib, referenceMeasure, Measure.pi_pi]
  simp_rw [hcell]
  exact (Finset.prod_mul_distrib).symm

theorem productNormalizer_patch_ne_top {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    productNormalizer (fun k ↦ patchMeasure J hJ (a k) (b k)) β ≠ ⊤ := by
  rw [productNormalizer, pi_patchMeasure_eq hJ hJ2 a b, lintegral_smul_measure, smul_eq_mul]
  apply ENNReal.mul_ne_top
  · exact ENNReal.prod_ne_top fun k _ ↦ patchScale_ne_top J (b k)
  · exact ne_top_of_le_ne_top (regularGreen_partitionFunction_ne_top (n + 1) hn hβ hsub)
      (setLIntegral_le_lintegral _ _)

/-- Equality with the actual Green ensemble conditioned on the genuine
product patch event. The regular representative is transferred by the
already proved joint Haar-a.e. ensemble identity. -/
theorem productGibbs_patch_eq_cond {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    productGibbs (fun k ↦ patchMeasure J hJ (a k) (b k)) β =
      ProbabilityTheory.cond (gibbsMeasure greenRealRepresentative (n + 1) β)
        (patchProductEvent hJ a b) := by
  let μ := Measure.pi fun k ↦ patchMeasure J hJ (a k) (b k)
  have hnorm : productGibbs (fun k ↦ patchMeasure J hJ (a k) (b k)) β =
      ProbabilityTheory.cond (μ.withDensity (jointDensity (n + 1) β)) univ := by
    simp only [productGibbs, ProbabilityTheory.cond, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, productNormalizer, μ]
  have hc0 : (∏ k, patchScale J (b k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ patchScale_ne_zero hJ (b k)
  have hct : (∏ k, patchScale J (b k)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun k _ ↦ patchScale_ne_top J (b k)
  rw [hnorm]
  change ProbabilityTheory.cond ((Measure.pi _).withDensity _) univ = _
  rw [pi_patchMeasure_eq hJ hJ2 a b, withDensity_smul_measure,
    ← restrict_withDensity (measurableSet_patchProductEvent hJ a b),
    cond_smul _ _ hc0 hct, cond_restrict_univ,
    ← regularGreen_gibbsMeasure_eq (n + 1) β]
  change ProbabilityTheory.cond ((referenceMeasure (n + 1)).withDensity _) _ =
    ProbabilityTheory.cond ((partitionFunction regularGreenRepresentative (n + 1) β)⁻¹ •
      (referenceMeasure (n + 1)).withDensity _) _
  exact (cond_smul _ _
    (ENNReal.inv_ne_zero.mpr (regularGreen_partitionFunction_ne_top (n + 1) hn hβ hsub))
    (ENNReal.inv_ne_top.mpr (partitionFunction_ne_zero regularGreenRepresentative_measurable
      (n + 1) β))).symm

/-- A proved conditional version for every coordinate of a product patch
restriction, in particular for a different coordinate of a two-cell law. -/
theorem lintegral_patch_conditionals {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (i : Fin (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    let P := ProbabilityTheory.cond (gibbsMeasure greenRealRepresentative (n + 1) β)
      (patchProductEvent hJ a b)
    (∫⁻ X, F X ∂P) = ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
      ∂conditionalKernel (patchMeasure J hJ (a i) (b i)) i β Y ∂Measure.map (removeSite i) P := by
  dsimp only
  rw [← productGibbs_patch_eq_cond hJ hJ2 hn a b hβ hsub]
  exact lintegral_disintegrate _ i β (productNormalizer_patch_ne_top hJ hJ2 hn a b hβ hsub) hF

theorem patchProductEvent_cells {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) :
    patchProductEvent hJ η (fun _ ↦ .cell) = labelFiber hJ η := rfl

def adjacentShapes {N : ℕ} (t : Fin N) (d : Fin 2) : Fin N → Patch :=
  Function.update (fun _ ↦ .cell) t (.edge d)

theorem patchProductEvent_adjacent {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (t : Fin N) (a : MeshIndex J) (d : Fin 2) :
    patchProductEvent hJ (Function.update η t a) (adjacentShapes t d) =
      twoCellFiber hJ η t a (nextCell J hJ a d) := by
  ext X
  change (∀ k ∈ univ, X k ∈ patchDomain J hJ (Function.update η t a k)
    (adjacentShapes t d k)) ↔ _
  simp only [Set.mem_univ, forall_const]
  rw [twoCellFiber_eq_adjacent_event]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Function.update_self, adjacentShapes, patchDomain,
        LocalPointEstimates.shape, TorusPatchDensity.domain] using h t
    · intro k hkt
      simpa only [Function.update_of_ne hkt, adjacentShapes, patchDomain,
        LocalPointEstimates.shape, TorusPatchDensity.domain] using h k
  · rintro ⟨ht, hrest⟩ k
    by_cases hkt : k = t
    · subst k
      simpa only [Function.update_self, adjacentShapes, patchDomain,
        LocalPointEstimates.shape, TorusPatchDensity.domain] using ht
    · simpa only [Function.update_of_ne hkt, adjacentShapes, patchDomain,
        LocalPointEstimates.shape, TorusPatchDensity.domain] using hrest k hkt

theorem lintegral_label_conditionals {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) (η : Fin (n + 1) → MeshIndex J) (i : Fin (n + 1))
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ X, F X ∂labelGibbsMeasure hJ η β) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y) ∂conditionalKernel (meshCellMeasure J hJ (η i)) i β Y
        ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β) := by
  rw [labelGibbsMeasure_eq_cond hJ hn η hβ hsub]
  exact lintegral_patch_conditionals hJ hJ2 hn η (fun _ ↦ .cell) i hβ hsub hF

theorem lintegral_twoCell_conditionals {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) (η : Fin (n + 1) → MeshIndex J)
    (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    let P := twoCellGibbsMeasure hJ η t a (nextCell J hJ a d) β
    (∫⁻ X, F X ∂P) = ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
      ∂conditionalKernel (patchMeasure J hJ (Function.update η t a i)
        (adjacentShapes t d i)) i β Y ∂Measure.map (removeSite i) P := by
  have h := lintegral_patch_conditionals hJ hJ2 hn (Function.update η t a)
    (adjacentShapes t d) i hβ hsub hF
  simpa only [patchProductEvent_adjacent, twoCellGibbsMeasure] using h

def otherIndexMap {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : ↥(otherParticles i) :=
  ⟨i.succAbove j, (mem_otherParticles i _).mpr (Fin.succAbove_ne i j)⟩

theorem otherIndexMap_bijective {n : ℕ} (i : Fin (n + 1)) :
    Function.Bijective (otherIndexMap i) := by
  constructor
  · intro j k h
    exact Fin.succAbove_right_injective (congrArg Subtype.val h)
  · intro k
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq ((mem_otherParticles i k).mp k.2)
    exact ⟨j, Subtype.ext hj⟩

def otherIndexEquiv {n : ℕ} (i : Fin (n + 1)) : Fin n ≃ ↥(otherParticles i) :=
  Equiv.ofBijective (otherIndexMap i) (otherIndexMap_bijective i)

theorem sourceWeight_eq_subfamily {n : ℕ} (i : Fin (n + 1)) (β : ℝ)
    (Y : Configuration n) :
    sourceWeight β Y = torusWeight (fun k : otherParticles i ↦ insertSite i 0 Y k)
      (fun _ ↦ β / (n + 1 : ℕ)) := by
  funext z
  unfold sourceWeight torusWeight
  congr 1
  apply Fintype.sum_equiv (otherIndexEquiv i)
  intro j
  change (β / (n + 1 : ℕ)) * regularGreenRepresentative (z - Y j) =
    (β / (n + 1 : ℕ)) * regularGreenRepresentative (z - insertSite i 0 Y (i.succAbove j))
  rw [insertSite_succAbove]

theorem pointDensity_subfamily {n : ℕ} (μ : Measure Torus) (i : Fin (n + 1))
    (β : ℝ) (Y : Configuration n) :
    pointDensity μ (fun k : otherParticles i ↦ insertSite i 0 Y k)
      (fun _ ↦ β / (n + 1 : ℕ)) = pointDensity μ Y (fun _ ↦ β / (n + 1 : ℕ)) := by
  unfold pointDensity
  rw [← sourceWeight_eq_subfamily i β Y]
  rfl

theorem pointLaw_subfamily {n : ℕ} (μ : Measure Torus) (i : Fin (n + 1))
    (β : ℝ) (Y : Configuration n) :
    pointLaw μ (fun k : otherParticles i ↦ insertSite i 0 Y k)
      (fun _ ↦ β / (n + 1 : ℕ)) = pointLaw μ Y (fun _ ↦ β / (n + 1 : ℕ)) := by
  rw [pointLaw, pointDensity_subfamily]
  rfl

def PrescribedOutside {n J : ℕ} (hJ : 0 < J) (η : Fin (n + 1) → MeshIndex J)
    (i : Fin (n + 1)) (Y : Configuration n) : Prop :=
  ∀ j, Y j ∈ closure (meshCell J hJ (η (i.succAbove j)))

theorem prescribedOutside_insertSite {n J : ℕ} (hJ : 0 < J)
    (η : Fin (n + 1) → MeshIndex J) (i : Fin (n + 1)) (Y : Configuration n)
    (hY : PrescribedOutside hJ η i Y) :
    ∀ k ∈ otherParticles i, insertSite i 0 Y k ∈ closure (meshCell J hJ (η k)) := by
  intro k hk
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ((mem_otherParticles i k).mp hk)
  simpa only [insertSite_succAbove] using hY j

/-- All fixed closed-cell placements are admitted, including repeated
points. Every integrability and normalization premise is discharged. -/
theorem capped_source_bounds {n J : ℕ} (hJ : 0 < J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (b : Patch) :
    let μ := patchMeasure J hJ a b
    Integrable (sourceWeight β Y) μ ∧ 0 < (∫ z, sourceWeight β Y z ∂μ) ∧
      IsProbabilityMeasure (pointLaw μ Y (fun _ ↦ β / (n + 1 : ℕ))) ∧
      MemLp (pointDensity μ Y (fun _ ↦ β / (n + 1 : ℕ))) 4 μ ∧
      (∀ᵐ z ∂μ, fixedLower β₀ C₀ C₁ ≤ pointDensity μ Y (fun _ ↦ β / (n + 1 : ℕ)) z) ∧
      lpNorm (pointDensity μ Y (fun _ ↦ β / (n + 1 : ℕ))) 4 μ ≤ fixedNorm β₀ C₀ C₁ := by
  have h := CappedPointWeights.capped_pointWeight_bounds hJ (Nat.succ_pos n)
    hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh η hη (otherParticles i) (insertSite i 0 Y)
    (prescribedOutside_insertSite hJ η i Y hY) (fun _ ↦ β / (n + 1 : ℕ))
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) a b
  dsimp only at h ⊢
  rw [← sourceWeight_eq_subfamily i β Y, pointLaw_subfamily, pointDensity_subfamily] at h
  exact h

theorem conditionalKernel_eq_raw_density {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) (a : MeshIndex J) (b : Patch)
    (hi : Integrable (sourceWeight β Y) (patchMeasure J hJ a b))
    (hz : 0 < ∫ z, sourceWeight β Y z ∂patchMeasure J hJ a b) :
    conditionalKernel (patchMeasure J hJ a b) i β Y =
      (patchMeasure J hJ a b).withDensity (fun z ↦ ENNReal.ofReal
        (rawSourceWeight β Y z / ∫ u, rawSourceWeight β Y u ∂patchMeasure J hJ a b)) := by
  rw [conditionalKernel_eq_pointLaw _ i β Y hi hz, pointLaw]
  have hae := (patchMeasure_absolutelyContinuous J hJ hJ2 a b).ae_le
    (sourceWeight_ae_rawSourceWeight β Y)
  have hint := integral_congr_ae hae
  apply withDensity_congr_ae
  filter_upwards [hae] with z hz'
  change ENNReal.ofReal (sourceWeight β Y z / ∫ u, sourceWeight β Y u ∂_) = _
  rw [hint, hz']

/-- The all-placement source formula, with the actual real one-site
normalizer finite and positive, plus equality to the Markov conditional version. -/
theorem capped_conditional_formula {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (b : Patch) :
    let μ := patchMeasure J hJ a b
    Integrable (rawSourceWeight β Y) μ ∧ 0 < (∫ z, rawSourceWeight β Y z ∂μ) ∧
      conditionalKernel μ i β Y =
        μ.withDensity (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z / ∫ u, rawSourceWeight β Y u ∂μ)) ∧
      conditionalKernel μ i β Y = pointLaw μ Y (fun _ ↦ β / (n + 1 : ℕ)) := by
  have h := capped_source_bounds hJ hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh η hη i Y hY a b
  have hae := (patchMeasure_absolutelyContinuous J hJ hJ2 a b).ae_le
    (sourceWeight_ae_rawSourceWeight β Y)
  refine ⟨h.1.congr hae, ?_, conditionalKernel_eq_raw_density hJ hJ2 i β Y a b h.1 h.2.1,
    conditionalKernel_eq_pointLaw _ i β Y h.1 h.2.1⟩
  rw [← integral_congr_ae hae]
  exact h.2.1

theorem capped_conditional_uniform_estimates {n J : ℕ} (hJ : 0 < J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) (b : Patch) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (patchDomain J hJ a b))) :
    let ν := conditionalKernel (patchMeasure J hJ a b) i β Y
    let c := fixedLower β₀ C₀ C₁
    let K := fixedNorm β₀ C₀ C₁
    ProbabilityTheory.variance f ν ≤ (OneSiteConstants.poincare c K / (J : ℝ) ^ 2) *
      (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) ∧
    entropy ν (fun z ↦ f z ^ 2) ≤
      (((OneSiteConstants.logSobolev c K / (J : ℝ) ^ 2) *
        (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) : ℝ) : EReal) ∧
    MemLp (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν ∧
    lpNorm (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν ≤
      (OneSiteConstants.fourthMoment c K / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν := by
  have hb := capped_source_bounds hJ hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh η hη i Y hY a b
  have h := OneSiteConstants.capped_pointWeight_uniform_estimates hJ (Nat.succ_pos n)
    hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh η hη (otherParticles i) (insertSite i 0 Y)
    (prescribedOutside_insertSite hJ η i Y hY) (fun _ ↦ β / (n + 1 : ℕ))
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) a b hf
  dsimp only at h ⊢
  rw [conditionalKernel_eq_pointLaw _ i β Y hb.1 hb.2.1]
  simpa only [pointLaw_subfamily] using h

def PatchOutside {n J : ℕ} (hJ : 0 < J) (a : Fin (n + 1) → MeshIndex J)
    (b : Fin (n + 1) → Patch) (i : Fin (n + 1)) (Y : Configuration n) : Prop :=
  ∀ j, Y j ∈ closure (patchDomain J hJ (a (i.succAbove j)) (b (i.succAbove j)))

theorem ae_mem_patchDomain (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (b : Patch) :
    ∀ᵐ z ∂patchMeasure J hJ a b, z ∈ patchDomain J hJ a b := by
  rw [patchMeasure_eq_scaled J hJ hJ2 a b]
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_patchDomain J hJ a b)) _

theorem ae_patchOutside {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch) (i : Fin (n + 1)) (β : ℝ) :
    ∀ᵐ Y ∂outsideMarginal (fun k ↦ patchMeasure J hJ (a k) (b k)) i β,
      PatchOutside hJ a b i Y := by
  rw [outsideMarginal_eq]
  apply (withDensity_absolutelyContinuous _ _).ae_le
  apply ae_all_iff.mpr
  intro j
  have h := (measurePreserving_eval (fun k : Fin n ↦
    patchMeasure J hJ (a (i.succAbove k)) (b (i.succAbove k))) j).quasiMeasurePreserving.ae
      (ae_mem_patchDomain J hJ hJ2 (a (i.succAbove j)) (b (i.succAbove j)))
  exact h.mono fun _ hz ↦ subset_closure hz

theorem ae_cond_patchOutside {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) (a : Fin (n + 1) → MeshIndex J) (b : Fin (n + 1) → Patch)
    (i : Fin (n + 1)) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    ∀ᵐ Y ∂Measure.map (removeSite i)
      (ProbabilityTheory.cond (gibbsMeasure greenRealRepresentative (n + 1) β)
        (patchProductEvent hJ a b)), PatchOutside hJ a b i Y := by
  rw [← productGibbs_patch_eq_cond hJ hJ2 hn a b hβ hsub]
  exact ae_patchOutside hJ hJ2 a b i β

/-- For a different coordinate of an adjacent-cell law, the one source
allowed to move between the endpoints receives an admissible completed
label. Both cap premises are used to cover its two possible closed cells. -/
theorem exists_capped_adjacent_outside {n J : ℕ} (hJ : 0 < J) {δ : ℝ}
    (η : Fin (n + 1) → MeshIndex J) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible hJ δ η t a d) (Y : Configuration n)
    (hY : PatchOutside hJ (Function.update η t a) (adjacentShapes t d) i Y) :
    ∃ ζ, OccupationCap δ ζ ∧ PrescribedOutside hJ ζ i Y := by
  by_cases hit : i = t
  · refine ⟨complete η t a, hadm.1, ?_⟩
    intro j
    have hjt : i.succAbove j ≠ t := by simpa only [← hit] using Fin.succAbove_ne i j
    simpa [complete, adjacentShapes, patchDomain, LocalPointEstimates.shape,
      TorusPatchDensity.domain, hjt] using hY j
  · obtain ⟨j₀, hj₀⟩ := Fin.exists_succAbove_eq (Ne.symm hit)
    have hmoving : Y j₀ ∈ closure (meshCell J hJ a) ∪
        closure (meshCell J hJ (nextCell J hJ a d)) := by
      simpa [hj₀, adjacentShapes, patchDomain, LocalPointEstimates.shape,
        TorusPatchDensity.domain, edgeCellUnion, closure_union] using hY j₀
    have hcompletion (c : MeshIndex J) (hc : Y j₀ ∈ closure (meshCell J hJ c)) :
        PrescribedOutside hJ (complete η t c) i Y := by
      intro j
      by_cases hjt : i.succAbove j = t
      · have hj : j = j₀ := Fin.succAbove_right_injective (hjt.trans hj₀.symm)
        subst j
        simpa [complete, hj₀] using hc
      · simpa [complete, adjacentShapes, patchDomain, LocalPointEstimates.shape,
          TorusPatchDensity.domain, hjt] using hY j
    rcases hmoving with ha | hb
    · exact ⟨complete η t a, hadm.1, hcompletion a ha⟩
    · exact ⟨complete η t (nextCell J hJ a d), hadm.2, hcompletion _ hb⟩

def allowedPatchLabels {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) : Patch → Finset (MeshIndex J)
  | .cell => {a}
  | .edge d => {a, nextCell J hJ a d}

theorem allowedPatchLabels_nonempty {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    (allowedPatchLabels hJ a b).Nonempty := by
  cases b <;> simp [allowedPatchLabels]

theorem mem_patchDomain_iff_label {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch) (z : Torus) :
    z ∈ patchDomain J hJ a b ↔ meshLabel J hJ z ∈ allowedPatchLabels hJ a b := by
  cases b <;> simp [patchDomain, LocalPointEstimates.shape, TorusPatchDensity.domain,
    edgeCellUnion, allowedPatchLabels]

theorem exists_capped_probe_outside {n J : ℕ} (hJ : 0 < J) {δ : ℝ}
    (η : Fin (n + 1) → MeshIndex J) (i : Fin (n + 1)) (a : MeshIndex J) (b : Patch)
    (hadm : ProbeAdmissible δ η i (allowedPatchLabels hJ a b))
    (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    ∃ ζ, OccupationCap δ ζ ∧ PrescribedOutside hJ ζ i Y := by
  obtain ⟨c, hc⟩ := allowedPatchLabels_nonempty hJ a b
  refine ⟨complete η i c, hadm c hc, ?_⟩
  intro j
  simpa only [complete_of_ne η i (i.succAbove j) c (Fin.succAbove_ne i j)] using hY j

theorem probe_conditional_formula {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (i : Fin (n + 1)) (a : MeshIndex J) (b : Patch)
    (hadm : ProbeAdmissible (fixedDelta β₀ C₀ C₁) η i (allowedPatchLabels hJ a b))
    (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    let μ := patchMeasure J hJ a b
    Integrable (rawSourceWeight β Y) μ ∧ 0 < (∫ z, rawSourceWeight β Y z ∂μ) ∧
      conditionalKernel μ i β Y =
        μ.withDensity (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z / ∫ u, rawSourceWeight β Y u ∂μ)) ∧
      conditionalKernel μ i β Y = pointLaw μ Y (fun _ ↦ β / (n + 1 : ℕ)) := by
  obtain ⟨ζ, hζ, hYζ⟩ := exists_capped_probe_outside hJ η i a b hadm Y hY
  exact capped_conditional_formula hJ hJ2 hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh ζ hζ i Y hYζ a b

theorem adjacent_conditional_formula {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible hJ (fixedDelta β₀ C₀ C₁) η t a d)
    (Y : Configuration n)
    (hY : PatchOutside hJ (Function.update η t a) (adjacentShapes t d) i Y) :
    let μ := patchMeasure J hJ (Function.update η t a i) (adjacentShapes t d i)
    Integrable (rawSourceWeight β Y) μ ∧ 0 < (∫ z, rawSourceWeight β Y z ∂μ) ∧
      conditionalKernel μ i β Y =
        μ.withDensity (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z / ∫ u, rawSourceWeight β Y u ∂μ)) ∧
      conditionalKernel μ i β Y = pointLaw μ Y (fun _ ↦ β / (n + 1 : ℕ)) := by
  obtain ⟨ζ, hζ, hYζ⟩ := exists_capped_adjacent_outside hJ η t i a d hadm Y hY
  exact capped_conditional_formula hJ hJ2 hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh ζ hζ i Y hYζ
    (Function.update η t a i) (adjacentShapes t d i)

/-- The normalization of the uniform patch measure cancels. Thus the
source formula may equivalently use restricted Haar and its own integral. -/
theorem conditionalKernel_eq_restricted_source {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n) (a : MeshIndex J) (b : Patch)
    (hi : Integrable (sourceWeight β Y) (patchMeasure J hJ a b)) :
    conditionalKernel (patchMeasure J hJ a b) i β Y =
      ProbabilityTheory.cond ((torusMeasure.restrict (patchDomain J hJ a b)).withDensity
        (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z))) univ := by
  rw [conditionalKernel_eq_section _ i β Y
    (sectionMass_ne_top_of_source_integrable _ i β Y hi), sectionKernel_eq_source_cond,
    source_cond_eq_rawSource_cond _ (patchMeasure_absolutelyContinuous J hJ hJ2 a b),
    patchMeasure_eq_scaled J hJ hJ2 a b, withDensity_smul_measure]
  exact cond_smul _ _ (patchScale_ne_zero hJ b) (patchScale_ne_top J b)

/-- The literal source density is a conditional version for the actual
specified-label law, for every measurable nonnegative observable. -/
theorem lintegral_label_raw_conditionals {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β < 4)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (i : Fin (n + 1)) {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    let μ := meshCellMeasure J hJ (η i)
    (∫⁻ X, F X ∂labelGibbsMeasure hJ η β) =
      ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
        ∂μ.withDensity (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z / ∫ u, rawSourceWeight β Y u ∂μ))
        ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β) := by
  dsimp only
  rw [lintegral_label_conditionals hJ hJ2 hn η i hβ hsub hF]
  have hae : ∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β),
      PrescribedOutside hJ η i Y := by
    rw [labelGibbsMeasure_eq_cond hJ hn η hβ hsub]
    exact ae_cond_patchOutside hJ hJ2 hn η (fun _ ↦ .cell) i hβ hsub
  apply lintegral_congr_ae
  filter_upwards [hae] with Y hY
  have h := capped_conditional_formula hJ hJ2 hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    η hη i Y hY (η i) .cell
  simp only [patchMeasure] at h
  rw [h.2.2.1]

/-- All coordinates are covered, including a coordinate other than the
one whose domain is the adjacent-cell union. Both completed caps remain
explicit. The outer measure is the actual marginal of the two-cell law. -/
theorem lintegral_twoCell_raw_conditionals {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hn : 2 ≤ n + 1) {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β < 4)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : Fin (n + 1) → MeshIndex J) (t i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible hJ (fixedDelta β₀ C₀ C₁) η t a d)
    {F : Configuration (n + 1) → ℝ≥0∞} (hF : Measurable F) :
    let P := twoCellGibbsMeasure hJ η t a (nextCell J hJ a d) β
    let μ := patchMeasure J hJ (Function.update η t a i) (adjacentShapes t d i)
    (∫⁻ X, F X ∂P) = ∫⁻ Y, ∫⁻ z, F (insertSite i z Y)
      ∂μ.withDensity (fun z ↦ ENNReal.ofReal (rawSourceWeight β Y z / ∫ u, rawSourceWeight β Y u ∂μ))
      ∂Measure.map (removeSite i) P := by
  dsimp only
  rw [lintegral_twoCell_conditionals hJ hJ2 hn η t i a d hβ hsub hF]
  have hae : ∀ᵐ Y ∂Measure.map (removeSite i)
      (twoCellGibbsMeasure hJ η t a (nextCell J hJ a d) β),
      PatchOutside hJ (Function.update η t a) (adjacentShapes t d) i Y := by
    have h := ae_cond_patchOutside hJ hJ2 hn (Function.update η t a)
      (adjacentShapes t d) i hβ hsub
    simpa only [patchProductEvent_adjacent, twoCellGibbsMeasure] using h
  apply lintegral_congr_ae
  filter_upwards [hae] with Y hY
  have h := adjacent_conditional_formula hJ hJ2 hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    η t i a d hadm Y hY
  rw [h.2.2.1]

@[simp] theorem sourceWeight_zero {n : ℕ} (Y : Configuration n) (z : Torus) :
    sourceWeight 0 Y z = 1 := by simp [sourceWeight, torusWeight]

@[simp] theorem rawSourceWeight_zero {n : ℕ} (Y : Configuration n) (z : Torus) :
    rawSourceWeight 0 Y z = 1 := by simp [rawSourceWeight]

@[simp] theorem conditionalKernel_zero {n : ℕ} (μ : Measure Torus) [IsProbabilityMeasure μ]
    (i : Fin (n + 1)) (Y : Configuration n) : conditionalKernel μ i 0 Y = μ := by
  simp [conditionalKernel, Kernel.piecewise_apply, sectionMass, jointDensity, sectionKernel]

end PeriodicAttractiveLogGas.OneCoordinateConditionals
