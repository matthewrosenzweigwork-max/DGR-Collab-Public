import LeanResearch.PeriodicAttractiveLogGas.CoordinateOscillation
import LeanResearch.PeriodicAttractiveLogGas.ConditionalL2Projections
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Identification of genuine coordinate-resampling kernels with the
actual conditional expectations. The measure hypothesis is an explicit
resampling pushforward identity, not a variance or operator bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace PeriodicAttractiveLogGas.ConditionalKernelL2

open CoordinateOscillation ConditionalL2Projections

variable {ι : Type*} {E : ι → Type*} [DecidableEq ι]
variable [∀ i, MeasurableSpace (E i)]

def fillOutside (x₀ : ∀ k, E k) (i : ι)
    (Y : ∀ k : {k : ι // k ≠ i}, E k) (k : ι) : E k :=
  if h : k = i then x₀ k else Y ⟨k, h⟩

theorem measurable_fillOutside (x₀ : ∀ k, E k) (i : ι) :
    Measurable (fillOutside x₀ i) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hki : k = i
  · simpa only [fillOutside, dite_eq_left hki] using
      (measurable_const (a := x₀ k) : Measurable (fun _ : (∀ k : {k : ι // k ≠ i}, E k) ↦ x₀ k))
  · simpa only [fillOutside, dite_eq_right hki] using
      (measurable_pi_apply (⟨k, hki⟩ : {k : ι // k ≠ i}))

omit [∀ i, MeasurableSpace (E i)] in
theorem fillOutside_sameExcept (x₀ x : ∀ k, E k) (i : ι) :
    SameExcept i (fillOutside x₀ i (omitCoordinate E i x)) x := by
  intro k hki
  simp only [fillOutside, dite_eq_right hki, omitCoordinate]

omit [∀ i, MeasurableSpace (E i)] in
theorem omitCoordinate_update (x : ∀ k, E k) (i : ι) (z : E i) :
    omitCoordinate E i (Function.update x i z) = omitCoordinate E i x := by
  funext k
  exact Function.update_of_ne k.property z x

theorem mem_update_iff {s : Set (∀ k, E k)} {i : ι}
    (hs : MeasurableSet[outsideSigma E i] s) (x : ∀ k, E k) (z : E i) :
    Function.update x i z ∈ s ↔ x ∈ s := by
  obtain ⟨t, _, rfl⟩ := hs
  change omitCoordinate E i (Function.update x i z) ∈ t ↔ omitCoordinate E i x ∈ t
  rw [omitCoordinate_update]

variable (κ : ∀ i, Kernel (∀ k, E k) (E i)) [∀ i, IsMarkovKernel (κ i)]

theorem measurable_outside_siteAverage [Nonempty (∀ k, E k)]
    (hind : IndependentSite κ) {f : (∀ k, E k) → ℝ} (hf : Measurable f) (i : ι) :
    Measurable[outsideSigma E i] (siteAverage κ f i) := by
  obtain ⟨x₀⟩ := ‹Nonempty (∀ k, E k)›
  have he : siteAverage κ f i =
      (siteAverage κ f i ∘ fillOutside x₀ i) ∘ omitCoordinate E i := by
    funext x
    exact (siteAverage_sameExcept κ hind (fillOutside_sameExcept x₀ x i)).symm
  rw [he]
  exact ((measurable_siteAverage κ hf i).comp (measurable_fillOutside x₀ i)).comp
    (comap_measurable (omitCoordinate E i))

/-- This is the actual measure identity obtained from a coordinate
conditional version: resampling that coordinate preserves the joint law. -/
def PreservesLaw (μ : Measure (∀ k, E k)) : Prop :=
  ∀ i, Measure.map (fun p : (∀ k, E k) × E i ↦ Function.update p.1 i p.2)
    (μ ⊗ₘ κ i) = μ

theorem integrable_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ}
    (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) : Integrable f μ := by
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hf x

variable (μ : Measure (∀ k, E k)) [IsProbabilityMeasure μ]

theorem integral_siteAverage (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} {B : ℝ} (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) (i : ι) :
    (∫ x, siteAverage κ f i x ∂μ) = ∫ x, f x ∂μ := by
  have hi : Integrable (fun p : (∀ k, E k) × E i ↦ f (Function.update p.1 i p.2))
      (μ ⊗ₘ κ i) := integrable_bounded _ (hm.comp measurable_update') (fun p ↦ hf _)
  calc
    _ = ∫ p : (∀ k, E k) × E i, f (Function.update p.1 i p.2) ∂(μ ⊗ₘ κ i) :=
      (Measure.integral_compProd hi).symm
    _ = ∫ x, f x ∂Measure.map (fun p : (∀ k, E k) × E i ↦ Function.update p.1 i p.2)
        (μ ⊗ₘ κ i) :=
      (integral_map_of_stronglyMeasurable measurable_update' hm.stronglyMeasurable).symm
    _ = _ := by rw [hstat i]

omit [IsProbabilityMeasure μ] [∀ i, IsMarkovKernel (κ i)] in
theorem siteAverage_indicator {s : Set (∀ k, E k)} (i : ι)
    (hs : MeasurableSet[outsideSigma E i] s) (f : (∀ k, E k) → ℝ) :
    siteAverage κ (s.indicator f) i = s.indicator (siteAverage κ f i) := by
  classical
  funext x
  have he (z : E i) : s.indicator f (Function.update x i z) =
      if x ∈ s then f (Function.update x i z) else 0 := by
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem ((mem_update_iff hs x z).mpr hx), ite_eq_left hx]
    · simp only [indicator_of_notMem (fun hz ↦ hx ((mem_update_iff hs x z).mp hz)), ite_eq_right hx]
  unfold siteAverage
  simp_rw [he]
  by_cases hx : x ∈ s
  · simp only [ite_eq_left hx, indicator_of_mem hx]
  · simp only [ite_eq_right hx, indicator_of_notMem hx, integral_zero]

theorem setIntegral_siteAverage (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} {B : ℝ} (hm : Measurable f) (hf : ∀ x, |f x| ≤ B)
    (i : ι) {s : Set (∀ k, E k)} (hs : MeasurableSet[outsideSigma E i] s) :
    (∫ x in s, siteAverage κ f i x ∂μ) = ∫ x in s, f x ∂μ := by
  have hs₀ : MeasurableSet s := outsideSigma_le E i s hs
  have hb (x) : |s.indicator f x| ≤ max B 0 := by
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using (hf x).trans (le_max_left B 0)
    · simpa only [indicator_of_notMem hx, abs_zero] using le_max_right B 0
  rw [← integral_indicator hs₀, ← integral_indicator hs₀,
    ← siteAverage_indicator κ i hs f]
  exact integral_siteAverage κ μ hstat (hm.indicator hs₀) hb i

/-- Independence from the resampled coordinate and the actual joint
pushforward identity prove the conditional-expectation property. -/
theorem siteAverage_ae_eq_condExp (hind : IndependentSite κ) (hstat : PreservesLaw κ μ)
    {f : (∀ k, E k) → ℝ} {B : ℝ} (hm : Measurable f) (hf : ∀ x, |f x| ≤ B) (i : ι) :
    siteAverage κ f i =ᵐ[μ] μ[f | outsideSigma E i] := by
  let := nonempty_of_isProbabilityMeasure μ
  have hi : Integrable (siteAverage κ f i) μ :=
    integrable_bounded μ (measurable_siteAverage κ hm i) (siteAverage_bound κ hf i)
  apply ae_eq_condExp_of_forall_setIntegral_eq (outsideSigma_le E i)
    (integrable_bounded μ hm hf) (fun _ _ _ ↦ hi.integrableOn)
    (fun s hs _ ↦ setIntegral_siteAverage κ μ hstat hm hf i hs)
  exact (measurable_outside_siteAverage κ hind hm i).stronglyMeasurable.aestronglyMeasurable

/-- The actual L2 projection has the pointwise kernel-average
representative whenever the input is represented by a bounded measurable
function. No representative at null points is prescribed. -/
theorem coordinateProjection_ae_eq_siteAverage (hind : IndependentSite κ)
    (hstat : PreservesLaw κ μ) (f : Lp ℝ 2 μ) {g : (∀ k, E k) → ℝ} {B : ℝ}
    (hm : Measurable g) (hg : ∀ x, |g x| ≤ B) (hfg : (f : (∀ k, E k) → ℝ) =ᵐ[μ] g)
    (i : ι) :
    (coordinateProjection E μ i f : (∀ k, E k) → ℝ) =ᵐ[μ] siteAverage κ g i :=
  (coordinateProjection_ae_eq_condExp E μ i f).trans
    ((condExp_congr_ae hfg).trans (siteAverage_ae_eq_condExp κ μ hind hstat hm hg i).symm)

end PeriodicAttractiveLogGas.ConditionalKernelL2
