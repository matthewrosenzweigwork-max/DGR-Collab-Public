import LeanResearch.PeriodicAttractiveLogGas.MovingPoleDerivativeIdentification
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationSections
import LeanResearch.PeriodicAttractiveLogGas.DeletedPairConditionals
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! The actual outside-coordinate interpretation of source Lemma 3.5.

The retained sources are indexed by `otherParticles i`; the outside
configuration uses `Fin.succAbove`. Their exact identification preserves
the original denominator `n + 1`. The observable is the actual particle
function with coordinate `i` integrated out, and the source blocks are
identified with its ordinary physical coordinate gradients.

SOURCE_ONLY candidate. The author has performed no Lean execution, axiom
inspection, semantic acceptance, or protected verification. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace BigOperators

namespace PeriodicAttractiveLogGas.ConditionalSourceCharts

open MovingPoleNumerators hiding patchDomain
open MovingPoleCharts MovingPoleCalculus MovingPoleNormalized
open MovingPoleDerivativeIdentification GreenPointWeights MeshCells MeshAdjacentCells
open LabelOccupations ConditionalParameters OneCoordinateConditionals

variable {n J : ℕ}

theorem source_patchDomain (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    MovingPoleNumerators.patchDomain J hJ a b = OneCoordinateConditionals.patchDomain J hJ a b := by
  cases b <;> rfl

/-- Outside coordinates in exactly the order used by `removeSite`. -/
def outsideCoordinates (i : Fin (n + 1)) (X : SourceSpace (otherParticles i)) :
    Configuration n := fun j ↦ sources X (otherIndexEquiv i j)

def insertedConfiguration (i : Fin (n + 1)) (X : SourceSpace (otherParticles i))
    (z : Torus) : Configuration (n + 1) := insertSite i z (outsideCoordinates i X)

def configurationFactor (i : Fin (n + 1)) (f : Configuration (n + 1) → ℝ)
    (X : SourceSpace (otherParticles i)) (z : Torus) : ℝ :=
  f (insertedConfiguration i X z)

@[simp] theorem otherIndexEquiv_val (i : Fin (n + 1)) (j : Fin n) :
    (otherIndexEquiv i j : Fin (n + 1)) = i.succAbove j := rfl

@[simp] theorem insertedConfiguration_self (i : Fin (n + 1))
    (X : SourceSpace (otherParticles i)) (z : Torus) :
    insertedConfiguration i X z i = z := insertSite_self i z _

@[simp] theorem insertedConfiguration_retained (i : Fin (n + 1))
    (X : SourceSpace (otherParticles i)) (z : Torus) (k : otherParticles i) :
    insertedConfiguration i X z k = sources X k := by
  obtain ⟨j, rfl⟩ := (otherIndexEquiv i).surjective k
  exact insertSite_succAbove i z _ j

@[simp] theorem removeSite_insertedConfiguration (i : Fin (n + 1))
    (X : SourceSpace (otherParticles i)) (z : Torus) :
    removeSite i (insertedConfiguration i X z) = outsideCoordinates i X :=
  removeSite_insertSite i z _

theorem continuous_outsideCoordinates (i : Fin (n + 1)) : Continuous (outsideCoordinates i) :=
  continuous_pi fun j ↦ continuous_sources (otherIndexEquiv i j)

theorem sourceVariation_sources {i : Fin (n + 1)} (k l : otherParticles i)
    (X : SourceSpace (otherParticles i)) (v : PlanarSpace) :
    sources (sourceVariation k X v) l = if l = k then torusQuotient v else sources X l := by
  classical
  unfold sources
  have hp : sourceProjection l (sourceVariation k X v) =
      if l = k then v else sourceProjection l X := by
    ext q
    simp only [sourceProjection_apply, sourceVariation_apply]
    split_ifs <;> rfl
  rw [hp]
  split_ifs <;> rfl

/-- The physical variation is the actual retained-particle update. -/
theorem insertedConfiguration_variation (i : Fin (n + 1))
    (X : SourceSpace (otherParticles i)) (z : Torus) (k : otherParticles i)
    (v : PlanarSpace) :
    insertedConfiguration i (sourceVariation k X v) z =
      Function.update (insertedConfiguration i X z) (k : Fin (n + 1)) (torusQuotient v) := by
  classical
  funext l
  by_cases hli : l = i
  · subst l
    rw [insertedConfiguration_self,
      Function.update_of_ne (Ne.symm ((mem_otherParticles i k).mp k.property)),
      insertedConfiguration_self]
  · let l' : otherParticles i := ⟨l, (mem_otherParticles i l).mpr hli⟩
    change insertedConfiguration i (sourceVariation k X v) z l' = _
    rw [insertedConfiguration_retained, sourceVariation_sources]
    by_cases hlk : l' = k
    · have hv : l = (k : Fin (n + 1)) := congrArg Subtype.val hlk
      rw [ite_eq_left hlk, hv, Function.update_self]
    · have hv : l ≠ (k : Fin (n + 1)) := fun h ↦ hlk (Subtype.ext h)
      rw [ite_eq_right hlk, Function.update_of_ne hv]
      exact (insertedConfiguration_retained i X z l').symm

theorem outsideCoordinates_variation (i : Fin (n + 1))
    (X : SourceSpace (otherParticles i)) (j : Fin n) (v : PlanarSpace) :
    outsideCoordinates i (sourceVariation (otherIndexEquiv i j) X v) =
      Function.update (outsideCoordinates i X) j (torusQuotient v) := by
  classical
  funext l
  rw [outsideCoordinates, sourceVariation_sources]
  by_cases h : l = j
  · subst l
    simp only [ite_true, Function.update_self]
  · have he : otherIndexEquiv i l ≠ otherIndexEquiv i j :=
      fun he ↦ h ((otherIndexEquiv i).injective he)
    simp only [ite_eq_right he, Function.update_of_ne h, outsideCoordinates]

/-- Exact retained-source weight equality, with the original particle
number in the denominator. -/
theorem sourceWeight_outsideCoordinates (i : Fin (n + 1)) (β : ℝ)
    (X : SourceSpace (otherParticles i)) :
    sourceWeight β (outsideCoordinates i X) =
      torusWeight (sources X) (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) := by
  rw [sourceWeight_eq_subfamily i β]
  congr 1
  funext k
  exact insertedConfiguration_retained i X 0 k

theorem pointLaw_outsideCoordinates (μ : Measure Torus) (i : Fin (n + 1)) (β : ℝ)
    (X : SourceSpace (otherParticles i)) :
    pointLaw μ (outsideCoordinates i X) (fun _ ↦ β / (n + 1 : ℕ)) =
      pointLaw μ (sources X) (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) := by
  rw [← pointLaw_subfamily μ i β]
  congr 1
  funext k
  exact insertedConfiguration_retained i X 0 k

def outsideNormalizer (hJ : 0 < J) (_i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (Y : Configuration n) : ℝ :=
  ∫ z in patchDomain J hJ a b, sourceWeight β Y z ∂torusMeasure

def outsideLog (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (Y : Configuration n) : ℝ :=
  Real.log (outsideNormalizer hJ i β a b Y)

def outsideMean (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (f : Configuration (n + 1) → ℝ)
    (Y : Configuration n) : ℝ :=
  ∫ z, f (insertSite i z Y) ∂conditionalKernel (patchMeasure J hJ a b) i β Y

theorem outsideNormalizer_comp (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (X : SourceSpace (otherParticles i)) :
    outsideNormalizer hJ i β a b (outsideCoordinates i X) =
      rawNormalizer (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b X := by
  rw [outsideNormalizer, sourceWeight_outsideCoordinates, rawNormalizer_eq_integral, source_patchDomain]

theorem outsideLog_comp (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (X : SourceSpace (otherParticles i)) :
    outsideLog hJ i β a b (outsideCoordinates i X) =
      rawLog (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b X := by
  rw [outsideLog, outsideNormalizer_comp]
  rfl

/-- The ordinary factor block is the physical gradient of the actual
particle observable. Only the local source differentiability is used. -/
theorem configurationFactor_block (i : Fin (n + 1)) (f : Configuration (n + 1) → ℝ)
    (X : SourceSpace (otherParticles i)) (z : Torus)
    (hf : DifferentiableAt ℝ (fun Y ↦ configurationFactor i f Y z) X)
    (k : otherParticles i) :
    factorBlock (configurationFactor i f) k X z =
      coordinateOrdinaryGradient f k (insertedConfiguration i X z) := by
  rw [factorBlock_eq_ordinaryGradient hf k, coordinateOrdinaryGradient,
    insertedConfiguration_retained, sources, torusOrdinaryGradient_lift]
  unfold rectangleOrdinaryGradient
  congr 2
  funext v
  exact congrArg f (insertedConfiguration_variation i X z k v)

theorem configurationFactor_block_on_patch (hJ : 0 < J)
    (i : Fin (n + 1)) (f : Configuration (n + 1) → ℝ) (a : MeshIndex J) (b : Patch)
    {S : Set (SourceSpace (otherParticles i))}
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a))
    {X : SourceSpace (otherParticles i)} (hX : X ∈ S)
    {z : Torus} (hz : z ∈ closure (patchDomain J hJ a b)) (k : otherParticles i) :
    factorBlock (configurationFactor i f) k X z =
    coordinateOrdinaryGradient f k (insertedConfiguration i X z) :=
  configurationFactor_block i f X z (differentiableAt_factor_source hJ a b hf hX
    (by simpa only [source_patchDomain] using hz)) k

/-- A full derivative of a pulled-back outside observable gives precisely
its ordinary torus-coordinate derivative, without a mesh dilation factor. -/
theorem coordinateOrdinaryGradient_of_sourceDerivative (i : Fin (n + 1))
    (g : Configuration n → ℝ) (X G : SourceSpace (otherParticles i))
    (hg : HasFDerivAt (fun Y ↦ g (outsideCoordinates i Y))
      (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i)) G) X) (j : Fin n) :
    coordinateOrdinaryGradient g j (outsideCoordinates i X) =
      sourceProjection (otherIndexEquiv i j) G := by
  have hb := hasFDerivAt_sourceBlock hg (otherIndexEquiv i j)
  simp_rw [outsideCoordinates_variation] at hb
  rw [coordinateOrdinaryGradient, outsideCoordinates, sources,
    torusOrdinaryGradient_lift, rectangleOrdinaryGradient, hb.fderiv]
  exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _

theorem ae_closedChart_mem_nhds {ι : Type*} [Fintype ι] (J : ℕ)
    (A : ι → MeshIndex J) (B : ι → Patch) :
    ∀ᵐ X ∂(volume : Measure (SourceSpace ι)).restrict (closedChart J A B),
      closedChart J A B ∈ 𝓝 X := by
  have he : interior (closedChart J A B) =ᵐ[(volume : Measure (SourceSpace ι))]
      closedChart J A B :=
    interior_ae_eq_of_null_frontier ((convex_closedChart J A B).addHaar_frontier volume)
  filter_upwards [ae_restrict_of_ae he,
    ae_restrict_mem (isCompact_closedChart J A B).measurableSet] with X hX hXS
  have hi : X ∈ interior (closedChart J A B) := by rwa [hX]
  exact mem_interior_iff_mem_nhds.mp hi

/-- The two physical statements on the actual outside configuration. -/
def OutsideDerivativeFormula (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (f : Configuration (n + 1) → ℝ)
    (Y : Configuration n) : Prop :=
  ∀ j : Fin n,
    coordinateOrdinaryGradient (outsideLog hJ i β a b) j Y =
      (-(β / (n + 1 : ℕ))) •
        ∫ z, greenGradient (z - Y j) ∂conditionalKernel (patchMeasure J hJ a b) i β Y ∧
    coordinateOrdinaryGradient (outsideMean hJ i β a b f) j Y =
      (∫ z, coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)
        ∂conditionalKernel (patchMeasure J hJ a b) i β Y) -
      (β / (n + 1 : ℕ)) • vectorCovariance
        (conditionalKernel (patchMeasure J hJ a b) i β Y)
        (fun z ↦ f (insertSite i z Y)) (fun z ↦ greenGradient (z - Y j))

namespace SourceCalculus

variable {hJ : 0 < J} {i : Fin (n + 1)} {β : ℝ} {a : MeshIndex J} {b : Patch}
    {S : Set (SourceSpace (otherParticles i))} {f : Configuration (n + 1) → ℝ}
    (h : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b S (configurationFactor i f))

include h

theorem conditionalKernel_eq_source (hJ2 : 2 ≤ J)
    (X : SourceSpace (otherParticles i)) (hX : X ∈ S) :
    conditionalKernel (patchMeasure J hJ a b) i β (outsideCoordinates i X) =
      pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X)
        (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) := by
  have hz : 0 < ∫ z in patchDomain J hJ a b,
      sourceWeight β (outsideCoordinates i X) z ∂torusMeasure := by
    rw [sourceWeight_outsideCoordinates, ← source_patchDomain, ← rawNormalizer_eq_integral]
    exact h.normalization.normalizer_pos X hX
  have hi : Integrable (sourceWeight β (outsideCoordinates i X))
      (torusMeasure.restrict (patchDomain J hJ a b)) := Integrable.of_integral_ne_zero hz.ne'
  have hip : Integrable (sourceWeight β (outsideCoordinates i X)) (patchMeasure J hJ a b) := by
    rw [patchMeasure_eq_scaled J hJ hJ2]
    exact hi.smul_measure (patchScale_ne_top J b)
  have hzp : 0 < ∫ z, sourceWeight β (outsideCoordinates i X) z ∂patchMeasure J hJ a b := by
    rw [patchMeasure_eq_scaled J hJ hJ2, integral_smul_measure, smul_eq_mul]
    exact mul_pos (ENNReal.toReal_pos (patchScale_ne_zero hJ b) (patchScale_ne_top J b)) hz
  rw [conditionalKernel_eq_pointLaw _ i β _ hip hzp,
    pointLaw_outsideCoordinates, pointLaw_patch_eq_raw hJ hJ2, source_patchDomain]

theorem outsideMean_comp (hJ2 : 2 ≤ J) (X : SourceSpace (otherParticles i)) (hX : X ∈ S) :
    outsideMean hJ i β a b f (outsideCoordinates i X) =
      conditionalMean (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b
        (configurationFactor i f) X := by
  rw [outsideMean, SourceCalculus.conditionalKernel_eq_source h hJ2 X hX]
  simp only [conditionalMean, source_patchDomain, configurationFactor, insertedConfiguration]

theorem physical_gradient_integrable (hJ2 : 2 ≤ J)
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a))
    (X : SourceSpace (otherParticles i)) (hX : X ∈ S) (k : otherParticles i) :
    Integrable (fun z ↦ coordinateOrdinaryGradient f k (insertedConfiguration i X z))
      (conditionalKernel (patchMeasure J hJ a b) i β (outsideCoordinates i X)) := by
  rw [SourceCalculus.conditionalKernel_eq_source h hJ2 X hX]
  have hi := h.integrable_factorBlock X hX k
  rw [source_patchDomain] at hi
  apply hi.congr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem (measurableSet_patchDomain J hJ a b)] with z hz
  exact configurationFactor_block_on_patch hJ i f a b hf hX (subset_closure hz) k

theorem meanBlock_eq_physical (hJ2 : 2 ≤ J)
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a))
    (X : SourceSpace (otherParticles i)) (hX : X ∈ S) (j : Fin n) :
    meanBlock (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b
      (configurationFactor i f) (otherIndexEquiv i j) X =
      (∫ z, coordinateOrdinaryGradient f (i.succAbove j)
        (insertSite i z (outsideCoordinates i X))
        ∂conditionalKernel (patchMeasure J hJ a b) i β (outsideCoordinates i X)) -
      (β / (n + 1 : ℕ)) • vectorCovariance
        (conditionalKernel (patchMeasure J hJ a b) i β (outsideCoordinates i X))
        (fun z ↦ f (insertSite i z (outsideCoordinates i X)))
        (fun z ↦ greenGradient (z - outsideCoordinates i X j)) := by
  rw [SourceCalculus.conditionalKernel_eq_source h hJ2 X hX, meanBlock, source_patchDomain]
  congr 1
  apply integral_congr_ae
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem (measurableSet_patchDomain J hJ a b)] with z hz
  exact configurationFactor_block_on_patch hJ i f a b hf hX (subset_closure hz)
    (otherIndexEquiv i j)

/-- Finiteness of every displayed physical term, including the covariance
product, for every fixed placement admitted by the chart. -/
theorem physical_finiteness (hJ2 : 2 ≤ J)
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a))
    (X : SourceSpace (otherParticles i)) (hX : X ∈ S) :
    let Y := outsideCoordinates i X
    let ν := conditionalKernel (patchMeasure J hJ a b) i β Y
    Integrable (fun z ↦ f (insertSite i z Y)) ν ∧
      ∀ j : Fin n,
        Integrable (fun z ↦ coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)) ν ∧
        Integrable (fun z ↦ greenGradient (z - Y j)) ν ∧
        Integrable (fun z ↦ f (insertSite i z Y) • greenGradient (z - Y j)) ν := by
  dsimp only
  refine ⟨?_, fun j ↦ ⟨SourceCalculus.physical_gradient_integrable h hJ2 hf X hX (otherIndexEquiv i j), ?_⟩⟩
  · rw [SourceCalculus.conditionalKernel_eq_source h hJ2 X hX]
    have he : configurationFactor i f X = fun z ↦ f (insertSite i z (outsideCoordinates i X)) := rfl
    simpa only [source_patchDomain, he] using (h.finiteness X hX).1
  · rw [SourceCalculus.conditionalKernel_eq_source h hJ2 X hX]
    simpa only [source_patchDomain, configurationFactor, insertedConfiguration] using
      (h.finiteness X hX).2.2 (outsideCoordinates i X j)

/-- The abstract source derivatives yield the literal outside-coordinate
formulas. Equality with the conditional kernel is used on a neighborhood,
not merely at the evaluation point. -/
theorem outsideDerivativeFormula_of_mem_nhds (hJ2 : 2 ≤ J)
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a))
    (X : SourceSpace (otherParticles i)) (hX : X ∈ S) (hXS : S ∈ 𝓝 X)
    (hd : HasFDerivAt (rawLog (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b)
        (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i))
          (rawLogGradient (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b X)) X ∧
      HasFDerivAt (conditionalMean (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b
        (configurationFactor i f))
        (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i))
          (rawMeanGradient (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b
            (configurationFactor i f) X)) X) :
    OutsideDerivativeFormula hJ i β a b f (outsideCoordinates i X) := by
  have hl : HasFDerivAt (fun Y ↦ outsideLog hJ i β a b (outsideCoordinates i Y))
      (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i))
        (rawLogGradient (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b X)) X := by
    simpa only [outsideLog_comp] using hd.1
  have he : (fun Y ↦ outsideMean hJ i β a b f (outsideCoordinates i Y)) =ᶠ[𝓝 X]
      conditionalMean (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a b
        (configurationFactor i f) :=
    Filter.mem_of_superset hXS fun Y hY ↦ SourceCalculus.outsideMean_comp h hJ2 Y hY
  have hm := he.hasFDerivAt_iff.mpr hd.2
  intro j
  constructor
  · rw [coordinateOrdinaryGradient_of_sourceDerivative i _ X _ hl j,
      (h.blocks X hX (otherIndexEquiv i j)).1, logBlock,
      SourceCalculus.conditionalKernel_eq_source h hJ2 X hX, source_patchDomain]
    rfl
  · rw [coordinateOrdinaryGradient_of_sourceDerivative i _ X _ hm j,
      (h.blocks X hX (otherIndexEquiv i j)).2,
      SourceCalculus.meanBlock_eq_physical h hJ2 hf X hX j]

theorem ae_outsideDerivativeFormula (hJ2 : 2 ≤ J)
    (A : otherParticles i → MeshIndex J) (B : otherParticles i → Patch)
    (hS : S = closedChart J A B)
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a)) :
    ∀ᵐ X ∂(volume : Measure (SourceSpace (otherParticles i))).restrict S,
      OutsideDerivativeFormula hJ i β a b f (outsideCoordinates i X) := by
  have hn : ∀ᵐ X ∂(volume : Measure (SourceSpace (otherParticles i))).restrict S, S ∈ 𝓝 X := by
    rw [hS]
    exact ae_closedChart_mem_nhds J A B
  have hs : MeasurableSet S := by
    rw [hS]
    exact (isCompact_closedChart J A B).measurableSet
  filter_upwards [h.ordinary, hn, ae_restrict_mem hs] with X hd hn hX
  exact SourceCalculus.outsideDerivativeFormula_of_mem_nhds h hJ2 hf X hX hn hd

theorem ae_weighted_outsideDerivativeFormula (hJ2 : 2 ≤ J)
    (A : otherParticles i → MeshIndex J) (B : otherParticles i → Patch)
    (hS : S = closedChart J A B)
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a))
    (ρ : SourceSpace (otherParticles i) → ℝ≥0∞) (c : ℝ≥0∞) :
    ∀ᵐ X ∂c • ((sourceChartMeasure S).withDensity ρ),
      OutsideDerivativeFormula hJ i β a b f (outsideCoordinates i X) := by
  have hac : c • ((sourceChartMeasure S).withDensity ρ) ≪
      (volume : Measure (SourceSpace (otherParticles i))).restrict S := by
    unfold sourceChartMeasure
    exact ((withDensity_absolutelyContinuous _ _).trans
      (Measure.AbsolutelyContinuous.smul_left Measure.AbsolutelyContinuous.rfl _)).smul_left c
  exact (SourceCalculus.ae_outsideDerivativeFormula h hJ2 A B hS hf).filter_mono hac.ae_le

end SourceCalculus

section ChartTransport

variable {ι : Type*} [Fintype ι]

def blockLinearEquiv : SourceSpace ι ≃ₗ[ℝ] (ι → PlanarSpace) where
  toFun X i := sourceProjection i X
  invFun Y := WithLp.toLp 2 (fun ik ↦ Y ik.1 ik.2)
  left_inv X := by ext ik; rfl
  right_inv Y := by ext i k; rfl
  map_add' X Y := by ext i k; rfl
  map_smul' c X := by ext i k; rfl

def blockEquiv : SourceSpace ι ≃L[ℝ] (ι → PlanarSpace) :=
  blockLinearEquiv.toContinuousLinearEquiv

@[simp] theorem blockEquiv_apply (X : SourceSpace ι) (i : ι) :
    blockEquiv X i = sourceProjection i X := rfl

def physicalBlock (J : ℕ) (a : MeshIndex J) (b : Patch) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi univ
    (fun k ↦ Icc ((a k : ℝ) / J) (((a k : ℝ) + patchWidth b k) / J))

theorem physicalBlock_eq_image (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    physicalBlock J a b = meshAffine J a '' patchClosed b := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  ext x
  constructor
  · intro hx
    refine ⟨meshAffineInv J a x, ?_, meshAffine_right_inverse J hJ a x⟩
    rw [mem_patchClosed_iff]
    intro k
    have hk := hx k (mem_univ k)
    have hl := (div_le_iff₀ hj).mp hk.1
    have hu := (le_div_iff₀ hj).mp hk.2
    simp only [meshAffineInv_apply]
    constructor <;> nlinarith
  · rintro ⟨z, hz, rfl⟩ k hk
    have hz' := (mem_patchClosed_iff b z).mp hz k
    rw [meshAffine_apply]
    exact ⟨(div_le_div_iff_of_pos_right hj).mpr (by linarith),
      (div_le_div_iff_of_pos_right hj).mpr (by linarith)⟩

def patchVolumeFactor : Patch → ℝ≥0∞
  | .cell => 1
  | .edge _ => (2 : ℝ≥0∞)⁻¹

theorem patchReference_eq_scaled_closed (b : Patch) :
    patchReference b = patchVolumeFactor b • (volume : Measure PlanarSpace).restrict (patchClosed b) := by
  cases b with
  | cell => simp only [patchReference, patchVolumeFactor, patchClosed, one_smul, squareLebesgue]
  | edge k => exact edgeLebesgue_eq_closed k

def physicalBlockMeasure (J : ℕ) (a : MeshIndex J) (b : Patch) : Measure PlanarSpace :=
  (patchReference b).map (meshAffine J a)

theorem physicalBlockMeasure_eq (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    physicalBlockMeasure J a b =
      (patchVolumeFactor b * (J : ℝ≥0∞) ^ 2) •
        (volume : Measure PlanarSpace).restrict (physicalBlock J a b) := by
  have he : MeasurableEmbedding (meshAffine J a) := by
    rw [meshAffine_eq_dilation]
    exact RectangleDilation.measurableEmbedding_affine _ (by exact_mod_cast hJ.ne')
  have hr := he.restrict_map (volume : Measure PlanarSpace) (physicalBlock J a b)
  have hpre : meshAffine J a ⁻¹' physicalBlock J a b = patchClosed b := by
    rw [physicalBlock_eq_image hJ, (meshAffine_left_inverse J hJ a).injective.preimage_image]
  rw [hpre, (measurePreserving_meshAffine_volume J hJ a).map_eq, Measure.restrict_smul] at hr
  rw [physicalBlockMeasure, patchReference_eq_scaled_closed,
    Measure.map_smul _ (continuous_meshAffine J a).measurable.aemeasurable, ← hr, smul_smul]

instance physicalBlockMeasure_probability (J : ℕ) (a : MeshIndex J) (b : Patch) :
    IsProbabilityMeasure (physicalBlockMeasure J a b) := by
  unfold physicalBlockMeasure
  infer_instance

theorem measurePreserving_quotient_physicalBlock (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    MeasurePreserving torusQuotient (physicalBlockMeasure J a b) (patchMeasure J hJ a b) := by
  refine ⟨isOpenQuotientMap_torusQuotient.continuous.measurable, ?_⟩
  rw [physicalBlockMeasure, Measure.map_map isOpenQuotientMap_torusQuotient.continuous.measurable
    (continuous_meshAffine J a).measurable]
  exact (measurePreserving_patch J hJ a b).map_eq

theorem probability_smul_restrict_eq_normalized {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (s : Set E) (c : ℝ≥0∞) (h₀ : μ s ≠ 0) (h_top : μ s ≠ ⊤)
    (hp : IsProbabilityMeasure (c • μ.restrict s)) :
    c • μ.restrict s = (μ s)⁻¹ • μ.restrict s := by
  have hv : c * μ s = 1 := by
    let := hp
    simpa only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul] using
      (measure_univ (μ := c • μ.restrict s))
  have hc : c = (μ s)⁻¹ := by
    calc
      c = c * (μ s * (μ s)⁻¹) := by rw [ENNReal.mul_inv_cancel h₀ h_top, mul_one]
      _ = (μ s)⁻¹ := by rw [← mul_assoc, hv, one_mul]
  rw [hc]

/-- Grouping Euclidean coordinates is used only for measure transport.
Haar uniqueness introduces a scalar which disappears on normalization;
the physical gradient and its norm never pass through the Pi norm. -/
theorem measurePreserving_blocks (hJ : 0 < J) (A : ι → MeshIndex J) (B : ι → Patch) :
    MeasurePreserving (blockEquiv : SourceSpace ι → ι → PlanarSpace)
      (sourceChartMeasure (closedChart J A B))
      (Measure.pi fun i ↦ physicalBlockMeasure J (A i) (B i)) := by
  let e : SourceSpace ι ≃L[ℝ] (ι → PlanarSpace) := blockEquiv
  let S := closedChart J A B
  let T : Set (ι → PlanarSpace) := Set.pi univ (fun i ↦ physicalBlock J (A i) (B i))
  let ν : Measure (ι → PlanarSpace) := volume
  have hpre : e ⁻¹' T = S := by
    ext X
    simp only [T, S, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      physicalBlock, closedChart]
    constructor
    · intro h ik
      exact h ik.1 ik.2
    · intro h i k
      exact h (i, k)
  have himage : e '' S = T := by
    rw [← hpre]
    exact Set.image_preimage_eq _ e.surjective
  have hTc : IsCompact T := himage ▸ (isCompact_closedChart J A B).image e.continuous
  have hTi : (interior T).Nonempty := by
    obtain ⟨X, hX⟩ := interior_closedChart_nonempty hJ A B
    refine ⟨e X, mem_interior_iff_mem_nhds.mpr ?_⟩
    rw [← himage]
    exact e.toHomeomorph.isOpenMap.image_mem_nhds (mem_interior_iff_mem_nhds.mp hX)
  have hT₀ : ν T ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν hTi).ne'
  have hT_top : ν T ≠ ⊤ := hTc.measure_lt_top.ne
  let c : ℝ≥0 := Measure.addHaarScalarFactor ((volume : Measure (SourceSpace ι)).map e) ν
  have hhaar : (volume : Measure (SourceSpace ι)).map e = (c : ℝ≥0∞) • ν := by
    exact Measure.isAddLeftInvariant_eq_smul _ _
  have hr := e.toHomeomorph.measurableEmbedding.restrict_map
    (volume : Measure (SourceSpace ι)) T
  change ((volume : Measure (SourceSpace ι)).map e).restrict T =
    (volume.restrict (e ⁻¹' T)).map e at hr
  rw [hpre, hhaar, Measure.restrict_smul] at hr
  have hmap : (sourceChartMeasure S).map e =
      ((volume S)⁻¹ * (c : ℝ≥0∞)) • ν.restrict T := by
    rw [sourceChartMeasure, Measure.map_smul _ e.continuous.measurable.aemeasurable,
      ← hr, smul_smul]
  have hmprob : IsProbabilityMeasure ((sourceChartMeasure S).map e) := by
    let := closedChart_probability hJ A B
    infer_instance
  have hmnorm : (sourceChartMeasure S).map e = (ν T)⁻¹ • ν.restrict T := by
    rw [hmap] at hmprob ⊢
    exact probability_smul_restrict_eq_normalized ν T _ hT₀ hT_top hmprob
  have hprod : (Measure.pi fun i ↦ physicalBlockMeasure J (A i) (B i)) =
      (∏ i, patchVolumeFactor (B i) * (J : ℝ≥0∞) ^ 2) • ν.restrict T := by
    apply Measure.pi_eq
    intro s hs
    have hi (i : ι) : physicalBlockMeasure J (A i) (B i) (s i) =
        (patchVolumeFactor (B i) * (J : ℝ≥0∞) ^ 2) *
          volume (s i ∩ physicalBlock J (A i) (B i)) := by
      rw [physicalBlockMeasure_eq hJ, Measure.smul_apply, Measure.restrict_apply (hs i), smul_eq_mul]
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
    dsimp only [T]
    rw [← Set.pi_inter_distrib, show ν = Measure.pi (fun _ : ι ↦ (volume : Measure PlanarSpace)) from rfl,
      Measure.pi_pi]
    simp_rw [hi]
    exact (Finset.prod_mul_distrib).symm
  have hpnorm : (Measure.pi fun i ↦ physicalBlockMeasure J (A i) (B i)) =
      (ν T)⁻¹ • ν.restrict T := by
    have hp : IsProbabilityMeasure (Measure.pi fun i ↦ physicalBlockMeasure J (A i) (B i)) :=
      inferInstance
    rw [hprod] at hp ⊢
    exact probability_smul_restrict_eq_normalized ν T _ hT₀ hT_top hp
  exact ⟨e.continuous.measurable, hmnorm.trans hpnorm.symm⟩

/-- Exact pushforward of the literal normalized physical source rectangle
to the actual product of torus patch probabilities, including wrap. -/
theorem measurePreserving_sources (hJ : 0 < J) (A : ι → MeshIndex J) (B : ι → Patch) :
    MeasurePreserving (sources : SourceSpace ι → ι → Torus)
      (sourceChartMeasure (closedChart J A B))
      (Measure.pi fun i ↦ patchMeasure J hJ (A i) (B i)) := by
  have hpi := measurePreserving_pi
    (fun i ↦ physicalBlockMeasure J (A i) (B i))
    (fun i ↦ patchMeasure J hJ (A i) (B i))
    (fun i ↦ measurePreserving_quotient_physicalBlock hJ (A i) (B i))
  exact hpi.comp (measurePreserving_blocks hJ A B)

theorem patchWidth_le_two (b : Patch) (k : Fin 2) : patchWidth b k ≤ 2 := by
  cases b with
  | cell => norm_num [patchWidth]
  | edge d => exact edgeWidth_le_two d k

theorem physicalBlock_subset_fundamentalBox (hJ3 : 3 ≤ J) (a : MeshIndex J) (b : Patch) :
    physicalBlock J a b ⊆ euclideanFundamentalBox
      (WithLp.toLp 2 (fun k ↦ (a k : ℝ) / J - 1 / 4)) := by
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hj3 : (3 : ℝ) ≤ J := by exact_mod_cast hJ3
  intro X hX k hk
  have hb : (a k : ℝ) / J ≤ X k ∧ X k ≤ ((a k : ℝ) + patchWidth b k) / J := hX k (mem_univ k)
  have hw : patchWidth b k / J < (3 / 4 : ℝ) := by
    apply (div_lt_iff₀ hj).mpr
    nlinarith [patchWidth_le_two b k]
  change (a k : ℝ) / J - 1 / 4 < X k ∧ X k ≤ (a k : ℝ) / J - 1 / 4 + 1
  rw [add_div] at hb
  constructor <;> linarith

/-- Closed-chart injectivity also holds at periodic wrap: each physical
interval has width strictly below one, and lies in a translated fundamental box. -/
theorem sources_injOn_closedChart (hJ3 : 3 ≤ J) (A : ι → MeshIndex J) (B : ι → Patch) :
    Set.InjOn (sources : SourceSpace ι → ι → Torus) (closedChart J A B) := by
  intro X hX Y hY hXY
  have hblock (Z : SourceSpace ι) (hZ : Z ∈ closedChart J A B) (i : ι) :
      sourceProjection i Z ∈ physicalBlock J (A i) (B i) := by
    intro k hk
    exact (mem_closedChart_iff J A B Z).mp hZ (i, k)
  have he (i : ι) : sourceProjection i X = sourceProjection i Y :=
    injOn_torusQuotient_box _
      (physicalBlock_subset_fundamentalBox hJ3 _ _ (hblock X hX i))
      (physicalBlock_subset_fundamentalBox hJ3 _ _ (hblock Y hY i)) (congrFun hXY i)
  ext ik
  exact congrArg (fun Z : PlanarSpace ↦ Z ik.2) (he ik.1)

end ChartTransport

/-- Exact `Fin.succAbove`-ordered source-chart pushforward. -/
theorem measurePreserving_outsideCoordinates (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch) :
    MeasurePreserving (outsideCoordinates i)
      (sourceChartMeasure (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)))
      (outsideReference (fun k ↦ patchMeasure J hJ (A k) (B k)) i) := by
  let e := otherIndexEquiv i
  have hp := measurePreserving_piCongrLeft
    (fun j : Fin n ↦ patchMeasure J hJ (A (e j)) (B (e j))) e.symm
  have hp' : MeasurePreserving (fun Y : otherParticles i → Torus ↦ fun j ↦ Y (e j))
      (Measure.pi fun k : otherParticles i ↦ patchMeasure J hJ (A k) (B k))
      (outsideReference (fun k ↦ patchMeasure J hJ (A k) (B k)) i) := by
    convert hp using 1
    · funext Y j
      simpa only [Equiv.symm_apply_apply] using
        (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n ↦ Torus) e.symm Y (e j)).symm
    · congr 1
      funext k
      simp only [Equiv.apply_symm_apply]
    · rfl
  exact hp'.comp (measurePreserving_sources hJ (fun k : otherParticles i ↦ A k) (fun k ↦ B k))

theorem outsideCoordinates_injOn_closedChart (hJ3 : 3 ≤ J) (i : Fin (n + 1))
    (A : otherParticles i → MeshIndex J) (B : otherParticles i → Patch) :
    Set.InjOn (outsideCoordinates i) (closedChart J A B) := by
  intro X hX Y hY hXY
  apply sources_injOn_closedChart hJ3 A B hX hY
  funext k
  obtain ⟨j, rfl⟩ := (otherIndexEquiv i).surjective k
  exact congrFun hXY j

theorem ae_map_restrict_of_comp {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    [MeasurableSpace E] [MeasurableSpace T] [BorelSpace E] [BorelSpace T] [T2Space E] [T2Space T]
    {μ : Measure E} {s : Set E} (hs : IsCompact s) {q : E → T}
    (hq : Continuous q) (hinj : Set.InjOn q s) {P : T → Prop}
    (hP : ∀ᵐ X ∂μ.restrict s, P (q X)) :
    ∀ᵐ Y ∂(μ.restrict s).map q, P Y := by
  let : CompactSpace s := (isCompact_iff_compactSpace).mp hs
  have hc : Continuous (fun X : s ↦ q X) := hq.comp continuous_subtype_val
  have hi : Function.Injective (fun X : s ↦ q X) :=
    fun X Y h ↦ Subtype.ext (hinj X.property Y.property h)
  have he : MeasurableEmbedding (fun X : s ↦ q X) :=
    (hc.isClosedEmbedding hi).measurableEmbedding
  rw [← map_comap_subtype_coe hs.measurableSet μ,
    Measure.map_map hq.measurable measurable_subtype_coe]
  exact he.ae_map_iff.mpr ((ae_restrict_iff_subtype hs.measurableSet).mp hP)

/-- Forward a.e. transport uses a proved compact-chart embedding; there is
no unproved measurability hypothesis on the derivative predicate. -/
theorem ae_outsideReference_of_chart (hJ : 0 < J) (hJ3 : 3 ≤ J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch) {P : Configuration n → Prop}
    (hP : ∀ᵐ X ∂(volume : Measure (SourceSpace (otherParticles i))).restrict
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)), P (outsideCoordinates i X)) :
    ∀ᵐ Y ∂outsideReference (fun k ↦ patchMeasure J hJ (A k) (B k)) i, P Y := by
  rw [← (measurePreserving_outsideCoordinates hJ i A B).map_eq, sourceChartMeasure,
    Measure.map_smul _ (continuous_outsideCoordinates i).measurable.aemeasurable]
  exact Measure.ae_smul_measure
    (ae_map_restrict_of_comp (isCompact_closedChart J _ _) (continuous_outsideCoordinates i)
      (outsideCoordinates_injOn_closedChart hJ3 i _ _) hP) _

/-- Actual product projection underlying the Gibbs disintegration. -/
theorem measurePreserving_removeSite (μ : Fin (n + 1) → Measure Torus)
    [∀ k, IsProbabilityMeasure (μ k)] (i : Fin (n + 1)) :
    MeasurePreserving (removeSite i) (Measure.pi μ) (outsideReference μ i) := by
  exact (measurePreserving_snd (μ := μ i) (ν := outsideReference μ i)).comp
    (measurePreserving_piFinSuccAbove μ i)

theorem ae_jointLaw_of_outsideReference (hJ : 0 < J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (i : Fin (n + 1))
    {P : Configuration n → Prop}
    (hP : ∀ᵐ Y ∂outsideReference (fun k ↦ patchMeasure J hJ (A k) (B k)) i, P Y) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ A B d β, P (removeSite i X) := by
  apply (PositiveProductConditionals.productLaw_absolutelyContinuous _ _).ae_le
  exact (measurePreserving_removeSite _ i).quasiMeasurePreserving.ae hP

/-- Literal ENNReal density transport, used for section-mass densities
which are not required to be finite everywhere. -/
theorem measurePreserving_withDensity_ennreal {E T : Type*}
    [MeasurableSpace E] [MeasurableSpace T] {μ : Measure E} {ν : Measure T} {q : E → T}
    (hq : MeasurePreserving q μ ν) (ρ : T → ℝ≥0∞) (hρ : Measurable ρ) :
    MeasurePreserving q (μ.withDensity (ρ ∘ q)) (ν.withDensity ρ) := by
  refine ⟨hq.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hq.measurable hs, withDensity_apply _ (hq.measurable hs),
    withDensity_apply _ hs]
  exact (hq.restrict_preimage hs).lintegral_comp hρ

/-- The density on the source chart is the actual integrated joint Gibbs
weight, including the global normalizing scalar. Its image is the actual
outside marginal; no smaller-particle Gibbs identification is asserted. -/
theorem measurePreserving_actual_outsideMarginal (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch) (β : ℝ) :
    let μ := fun k ↦ patchMeasure J hJ (A k) (B k)
    let S := closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)
    MeasurePreserving (outsideCoordinates i)
      ((sourceChartMeasure S).withDensity (fun X ↦
        (productNormalizer μ β)⁻¹ * sectionMass (μ i) i β (outsideCoordinates i X)))
      (outsideMarginal μ i β) := by
  dsimp only
  let μ := fun k ↦ patchMeasure J hJ (A k) (B k)
  let ρ : Configuration n → ℝ≥0∞ := fun Y ↦ (productNormalizer μ β)⁻¹ * sectionMass (μ i) i β Y
  have hρ : Measurable ρ := measurable_const.mul (measurable_sectionMass (μ i) i β)
  have hm := measurePreserving_withDensity_ennreal
    (measurePreserving_outsideCoordinates hJ i A B) ρ hρ
  rw [outsideMarginal_eq μ i β]
  exact hm

/-- The same exact chart density transport holds for the genuine optional
deleted-pair marginal, with the integrated joint weight in its density. -/
theorem measurePreserving_deleted_outsideMarginal (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    let μ := fun k ↦ patchMeasure J hJ (A k) (B k)
    let W := DeletedPairEnsemble.weight regularGreenRepresentative d β
    let S := closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)
    MeasurePreserving (outsideCoordinates i)
      ((sourceChartMeasure S).withDensity (fun X ↦
        (PositiveProductConditionals.normalizer μ W)⁻¹ *
          PositiveProductConditionals.sectionMass (μ i) W i (outsideCoordinates i X)))
      (Measure.map (removeSite i) (DeletedPairConditionals.jointLaw hJ A B d β)) := by
  dsimp only
  let μ := fun k ↦ patchMeasure J hJ (A k) (B k)
  let W := DeletedPairEnsemble.weight regularGreenRepresentative d β
  let ρ : Configuration n → ℝ≥0∞ := fun Y ↦
    (PositiveProductConditionals.normalizer μ W)⁻¹ * PositiveProductConditionals.sectionMass (μ i) W i Y
  have hW : Measurable W := DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable d β
  have hρ : Measurable ρ := measurable_const.mul
    (PositiveProductConditionals.measurable_sectionMass (μ i) hW i)
  have hm := measurePreserving_withDensity_ennreal (measurePreserving_outsideCoordinates hJ i A B) ρ hρ
  change MeasurePreserving _ _ (PositiveProductConditionals.outsideMarginal μ W i)
  rw [PositiveProductConditionals.outsideMarginal_eq μ hW i]
  exact hm

theorem removeSite_update_retained (i : Fin (n + 1)) (X : Configuration (n + 1))
    (j : Fin n) (z : Torus) :
    removeSite i (Function.update X (i.succAbove j) z) =
      Function.update (removeSite i X) j z := by
  classical
  funext k
  by_cases h : k = j
  · subst k
    simp only [removeSite, Function.update_self]
  · have he : i.succAbove k ≠ i.succAbove j :=
      fun he ↦ h (Fin.succAbove_right_injective he)
    simp only [removeSite, Function.update_of_ne h, Function.update_of_ne he]

theorem coordinateOrdinaryGradient_removeSite (i : Fin (n + 1))
    (g : Configuration n → ℝ) (X : Configuration (n + 1)) (j : Fin n) :
    coordinateOrdinaryGradient (fun Y ↦ g (removeSite i Y)) (i.succAbove j) X =
      coordinateOrdinaryGradient g j (removeSite i X) := by
  unfold coordinateOrdinaryGradient
  simp only [removeSite_update_retained]
  rfl

/-- The conditional average as an actual observable of the full joint
configuration. It is independent of the coordinate being integrated out. -/
def jointConditionalMean (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (f : Configuration (n + 1) → ℝ)
    (X : Configuration (n + 1)) : ℝ :=
  outsideMean hJ i β a b f (removeSite i X)

theorem jointConditionalMean_eq (hJ : 0 < J) (i : Fin (n + 1)) (β : ℝ)
    (a : MeshIndex J) (b : Patch) (f : Configuration (n + 1) → ℝ)
    (X : Configuration (n + 1)) :
    jointConditionalMean hJ i β a b f X =
      ∫ z, f (Function.update X i z)
        ∂conditionalKernel (patchMeasure J hJ a b) i β (removeSite i X) := by
  simp only [jointConditionalMean, outsideMean, CoordinateConditionalKernels.insertSite_eq_update]

theorem SourceCalculus.ae_jointLaw_outsideDerivativeFormula
    (hJ : 0 < J) (hJ3 : 3 ≤ J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch) (β : ℝ)
    (f : Configuration (n + 1) → ℝ)
    (h : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ (A i) (B i)
      (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k)) (configurationFactor i f))
    (hf : SmoothOnChart (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))
      (patchClosed (B i)) (torusFactor (configurationFactor i f) J (A i)))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ A B d β,
      OutsideDerivativeFormula hJ i β (A i) (B i) f (removeSite i X) := by
  apply ae_jointLaw_of_outsideReference hJ A B d β i
  apply ae_outsideReference_of_chart hJ hJ3 i A B
  exact SourceCalculus.ae_outsideDerivativeFormula h (by omega) _ _ rfl hf

/-- The product law uses `Function.update`, whereas the geometric source
chart uses a subtype-indexed conditional. These shapes are identical. -/
theorem retained_adjacentShapes {N : ℕ} (I : Finset (Fin N)) (t : Fin N) (r : Fin 2) :
    (fun k : I ↦ OneCoordinateConditionals.adjacentShapes t r k) =
      MovingPoleCharts.adjacentShapes I t r := by
  classical
  funext k
  by_cases hk : (k : Fin N) = t <;>
    simp [OneCoordinateConditionals.adjacentShapes, MovingPoleCharts.adjacentShapes, hk]

theorem retained_adjacentChart (η : LabelVector J (n + 1))
    (i t : Fin (n + 1)) (r : Fin 2) :
    closedChart J (fun k : otherParticles i ↦ η k)
      (fun k ↦ OneCoordinateConditionals.adjacentShapes t r k) =
      adjacentChart (otherParticles i) η t r := by
  rw [retained_adjacentShapes]
  rfl

section SourceEndpoints

variable (K : MovingPoleIntegrability.KernelBounds) (hJ : 0 < J)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)

include K hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh

/-- Prescribed-cell endpoint. Every derivative and normalization input is
constructed from the earlier Green estimates and the genuine occupation cap. -/
theorem cell_jointLaw_derivatives (η : LabelVector J (n + 1))
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η) (i : Fin (n + 1))
    (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed .cell)
      (torusFactor (configurationFactor i f) J (η i))) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (fun _ ↦ .cell) none β,
      OutsideDerivativeFormula hJ i β (η i) .cell f (removeSite i X) := by
  have hc := cellChart_sourceCalculus K hJ (Nat.succ_pos n) hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    (otherParticles i) η hη (fun _ ↦ β / (n + 1 : ℕ))
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) (η i) .cell hf
  exact SourceCalculus.ae_jointLaw_outsideDerivativeFormula hJ (by omega) i η
    (fun _ ↦ .cell) β f hc hf none

/-- The integrated coordinate may itself range over an adjacent union.
Both endpoint caps are stated, and either orientation and wrap are included. -/
theorem integrated_adjacent_jointLaw_derivatives (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (d : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (_hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁)
      (Function.update η i (nextCell J hJ (η i) d)))
    (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge d))
      (torusFactor (configurationFactor i f) J (η i))) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (OneCoordinateConditionals.adjacentShapes i d) none β,
      OutsideDerivativeFormula hJ i β (η i) (.edge d) f (removeSite i X) := by
  have hc := cellChart_sourceCalculus K hJ (Nat.succ_pos n) hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    (otherParticles i) η hη₀ (fun _ ↦ β / (n + 1 : ℕ))
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) (η i) (.edge d) hf
  have hs : (fun k : otherParticles i ↦ OneCoordinateConditionals.adjacentShapes i d k) =
      fun _ ↦ Patch.cell := by
    funext k
    exact Function.update_of_ne ((mem_otherParticles i k).mp k.property) _ _
  have hb : OneCoordinateConditionals.adjacentShapes i d i = .edge d :=
    Function.update_self i _ _
  have hc' := hc
  have hf' := hf
  rw [cellChart] at hc' hf'
  have h := SourceCalculus.ae_jointLaw_outsideDerivativeFormula hJ (by omega) i η
    (OneCoordinateConditionals.adjacentShapes i d) β f
    (by simpa only [hs, hb] using hc')
    (by simpa only [hs, hb] using hf') none
  simpa only [hb] using h

/-- A retained source may range over the sole adjacent union. Both completed
labels satisfy the cap; the integrated coordinate remains a cell. -/
theorem source_adjacent_jointLaw_derivatives (η : LabelVector J (n + 1))
    (i t : Fin (n + 1)) (d : Fin 2) (hit : i ≠ t)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁)
      (Function.update η t (nextCell J hJ (η t) d)))
    (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (adjacentChart (otherParticles i) η t d) (patchClosed .cell)
      (torusFactor (configurationFactor i f) J (η i))) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (OneCoordinateConditionals.adjacentShapes t d) none β,
      OutsideDerivativeFormula hJ i β (η i) .cell f (removeSite i X) := by
  have hc := adjacentChart_sourceCalculus K hJ (Nat.succ_pos n) hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    (otherParticles i) η t d hη₀ hη₁ (fun _ ↦ β / (n + 1 : ℕ))
    (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) (η i) hf
  have hb : OneCoordinateConditionals.adjacentShapes t d i = .cell :=
    Function.update_of_ne hit _ _
  have h := SourceCalculus.ae_jointLaw_outsideDerivativeFormula hJ (by omega) i η
    (OneCoordinateConditionals.adjacentShapes t d) β f
    (by simpa only [retained_adjacentChart, hb] using hc)
    (by simpa only [retained_adjacentChart, hb] using hf) none
  simpa only [hb] using h

end SourceEndpoints

section DeletedSource

def deletedOutsideKernel (hJ : 0 < J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch) :=
  PositiveProductConditionals.conditionalKernel (patchMeasure J hJ a b)
    (DeletedPairEnsemble.weight regularGreenRepresentative d β)
    (DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable d β)
    (DeletedPairEnsemble.weight_pos regularGreenRepresentative d β) i

theorem deletedOutsideKernel_eq_ambient (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (X : Configuration (n + 1)) :
    deletedOutsideKernel hJ i d β (A i) (B i) (removeSite i X) =
      DeletedPairConditionals.ambientKernels hJ A B d β i X := rfl

def deletedOutsideNormalizer (hJ : 0 < J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (Y : Configuration n) : ℝ :=
  ∫ z in patchDomain J hJ a b, torusWeight Y (DeletedPairEnsemble.sourceCoefficient d β i) z
    ∂torusMeasure

def deletedOutsideLog (hJ : 0 < J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (Y : Configuration n) : ℝ := Real.log (deletedOutsideNormalizer hJ i d β a b Y)

def deletedOutsideMean (hJ : 0 < J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (f : Configuration (n + 1) → ℝ) (Y : Configuration n) : ℝ :=
  ∫ z, f (insertSite i z Y) ∂deletedOutsideKernel hJ i d β a b Y

theorem deletedWeight_outsideCoordinates (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (X : SourceSpace (otherParticles i)) :
    torusWeight (outsideCoordinates i X) (DeletedPairEnsemble.sourceCoefficient d β i) =
      torusWeight (sources X) (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) := by
  rw [DeletedPairEnsemble.sourceWeight_eq_subfamily d i β]
  congr 1
  funext k
  exact insertedConfiguration_retained i X 0 k

theorem deletedPointLaw_outsideCoordinates (μ : Measure Torus) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (X : SourceSpace (otherParticles i)) :
    pointLaw μ (outsideCoordinates i X) (DeletedPairEnsemble.sourceCoefficient d β i) =
      pointLaw μ (sources X) (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) := by
  rw [← DeletedPairEnsemble.pointLaw_subfamily μ d i β]
  congr 1
  funext k
  exact insertedConfiguration_retained i X 0 k

theorem deletedOutsideLog_comp (hJ : 0 < J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (X : SourceSpace (otherParticles i)) :
    deletedOutsideLog hJ i d β a b (outsideCoordinates i X) =
      rawLog (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) J hJ a b X := by
  simp only [deletedOutsideLog, deletedOutsideNormalizer, deletedWeight_outsideCoordinates,
    rawLog, rawNormalizer_eq_integral, source_patchDomain]

theorem deletedOutsideKernel_eq_source (hJ : 0 < J) (hJ2 : 2 ≤ J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (X : SourceSpace (otherParticles i))
    (hz : 0 < rawNormalizer
      (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) J hJ a b X) :
    deletedOutsideKernel hJ i d β a b (outsideCoordinates i X) =
      pointLaw (torusMeasure.restrict (patchDomain J hJ a b)) (sources X)
        (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) := by
  have hz' : 0 < ∫ z in patchDomain J hJ a b,
      torusWeight (outsideCoordinates i X) (DeletedPairEnsemble.sourceCoefficient d β i) z
        ∂torusMeasure := by
    rw [deletedWeight_outsideCoordinates, ← source_patchDomain, ← rawNormalizer_eq_integral]
    exact hz
  have hi := Integrable.of_integral_ne_zero hz'.ne'
  have hip : Integrable (torusWeight (outsideCoordinates i X)
      (DeletedPairEnsemble.sourceCoefficient d β i)) (patchMeasure J hJ a b) := by
    rw [patchMeasure_eq_scaled J hJ hJ2]
    exact hi.smul_measure (patchScale_ne_top J b)
  have hzp : 0 < ∫ z, torusWeight (outsideCoordinates i X)
      (DeletedPairEnsemble.sourceCoefficient d β i) z ∂patchMeasure J hJ a b := by
    rw [patchMeasure_eq_scaled J hJ hJ2, integral_smul_measure, smul_eq_mul]
    exact mul_pos (ENNReal.toReal_pos (patchScale_ne_zero hJ b) (patchScale_ne_top J b)) hz'
  rw [deletedOutsideKernel, PositiveProductConditionals.conditionalKernel_factor_eq_pointLaw
    _ _ _ _ i _ (Real.exp_pos _) _ _
      (fun z ↦ DeletedPairEnsemble.weight_insertSite d β i z _) hip hzp,
    deletedPointLaw_outsideCoordinates, pointLaw_patch_eq_raw hJ hJ2, source_patchDomain]

def DeletedOutsideDerivativeFormula (hJ : 0 < J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (f : Configuration (n + 1) → ℝ) (Y : Configuration n) : Prop :=
  ∀ j : Fin n,
    coordinateOrdinaryGradient (deletedOutsideLog hJ i d β a b) j Y =
      (-DeletedPairEnsemble.sourceCoefficient d β i j) •
        ∫ z, greenGradient (z - Y j) ∂deletedOutsideKernel hJ i d β a b Y ∧
    coordinateOrdinaryGradient (deletedOutsideMean hJ i d β a b f) j Y =
      (∫ z, coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)
        ∂deletedOutsideKernel hJ i d β a b Y) -
      DeletedPairEnsemble.sourceCoefficient d β i j • vectorCovariance
        (deletedOutsideKernel hJ i d β a b Y)
        (fun z ↦ f (insertSite i z Y)) (fun z ↦ greenGradient (z - Y j))

/-- A general value-identification bridge. Its premises identify the actual
functions on the chart; they do not posit any derivative identity. -/
theorem ae_pulled_source_blocks (hJ : 0 < J) (i : Fin (n + 1))
    (A : otherParticles i → MeshIndex J) (B : otherParticles i → Patch)
    (a : MeshIndex J) (b : Patch) (w : otherParticles i → ℝ)
    (F : SourceSpace (otherParticles i) → Torus → ℝ) (U V : Configuration n → ℝ)
    (hc : MovingPoleDerivativeIdentification.SourceCalculus w J hJ a b (closedChart J A B) F)
    (hU : EqOn (fun X ↦ U (outsideCoordinates i X)) (rawLog w J hJ a b) (closedChart J A B))
    (hV : EqOn (fun X ↦ V (outsideCoordinates i X)) (conditionalMean w J hJ a b F)
      (closedChart J A B)) :
    ∀ᵐ X ∂(volume : Measure (SourceSpace (otherParticles i))).restrict (closedChart J A B),
      ∀ j : Fin n,
        coordinateOrdinaryGradient U j (outsideCoordinates i X) = logBlock w J hJ a b (otherIndexEquiv i j) X ∧
        coordinateOrdinaryGradient V j (outsideCoordinates i X) = meanBlock w J hJ a b F (otherIndexEquiv i j) X := by
  filter_upwards [hc.ordinary, ae_closedChart_mem_nhds J A B,
    ae_restrict_mem (isCompact_closedChart J A B).measurableSet] with X hd hn hX
  have hU' : (fun Y ↦ U (outsideCoordinates i Y)) =ᶠ[𝓝 X] rawLog w J hJ a b :=
    Filter.mem_of_superset hn fun Y hY ↦ hU hY
  have hV' : (fun Y ↦ V (outsideCoordinates i Y)) =ᶠ[𝓝 X] conditionalMean w J hJ a b F :=
    Filter.mem_of_superset hn fun Y hY ↦ hV hY
  intro j
  constructor
  · rw [coordinateOrdinaryGradient_of_sourceDerivative i U X _ (hU'.hasFDerivAt_iff.mpr hd.1) j]
    exact (hc.blocks X hX (otherIndexEquiv i j)).1
  · rw [coordinateOrdinaryGradient_of_sourceDerivative i V X _ (hV'.hasFDerivAt_iff.mpr hd.2) j]
    exact (hc.blocks X hX (otherIndexEquiv i j)).2

theorem ae_deletedOutsideDerivativeFormula (hJ : 0 < J) (hJ2 : 2 ≤ J) (i : Fin (n + 1))
    (A : otherParticles i → MeshIndex J) (B : otherParticles i → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (f : Configuration (n + 1) → ℝ)
    (hc : MovingPoleDerivativeIdentification.SourceCalculus
      (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) J hJ a b
      (closedChart J A B) (configurationFactor i f))
    (hf : SmoothOnChart (closedChart J A B) (patchClosed b)
      (torusFactor (configurationFactor i f) J a)) :
    ∀ᵐ X ∂(volume : Measure (SourceSpace (otherParticles i))).restrict (closedChart J A B),
      DeletedOutsideDerivativeFormula hJ i d β a b f (outsideCoordinates i X) := by
  have he (X : SourceSpace (otherParticles i)) (hX : X ∈ closedChart J A B) :=
    deletedOutsideKernel_eq_source hJ hJ2 i d β a b X (hc.normalization.normalizer_pos X hX)
  have hm : EqOn (fun X ↦ deletedOutsideMean hJ i d β a b f (outsideCoordinates i X))
      (conditionalMean (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k)
        J hJ a b (configurationFactor i f)) (closedChart J A B) := by
    intro X hX
    change (∫ z, f (insertSite i z (outsideCoordinates i X))
      ∂deletedOutsideKernel hJ i d β a b (outsideCoordinates i X)) = _
    rw [he X hX]
    simp only [conditionalMean, source_patchDomain, configurationFactor, insertedConfiguration]
  have hb := ae_pulled_source_blocks hJ i A B a b _ (configurationFactor i f)
    (deletedOutsideLog hJ i d β a b) (deletedOutsideMean hJ i d β a b f) hc
    (fun X _ ↦ deletedOutsideLog_comp hJ i d β a b X) hm
  filter_upwards [hb, ae_restrict_mem (isCompact_closedChart J A B).measurableSet] with X hX hXS
  intro j
  constructor
  · rw [(hX j).1, logBlock, source_patchDomain, ← he X hXS, otherIndexEquiv_val,
      DeletedPairEnsemble.coefficients_succAbove]
    rfl
  · rw [(hX j).2, meanBlock, source_patchDomain, ← he X hXS, otherIndexEquiv_val,
      DeletedPairEnsemble.coefficients_succAbove]
    congr 1
    apply integral_congr_ae
    rw [he X hXS]
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem (measurableSet_patchDomain J hJ a b)] with z hz
    exact configurationFactor_block_on_patch hJ i f a b hf hXS (subset_closure hz)
      (otherIndexEquiv i j)

/-- Actual optional-deletion endpoint under the literal physical product.
All analytic hypotheses are generated from caps and placement, and the
joint law is proved to be a probability before its a.e. conclusion is used. -/
theorem capped_deleted_jointLaw_derivatives (K : MovingPoleIntegrability.KernelBounds)
    (hJ : 0 < J) (hn : 2 ≤ n + 1) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch) (i : Fin (n + 1))
    (labels : SourceSpace (otherParticles i) → LabelVector J (n + 1))
    (hcap : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      OccupationCap (fixedDelta β₀ C₀ C₁) (labels X))
    (hplace : ∀ X ∈ closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k),
      ∀ k ∈ otherParticles i, extendedSources (otherParticles i) X k ∈
        closure (meshCell J hJ (labels X k)))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (closedChart J (fun k : otherParticles i ↦ A k) (fun k ↦ B k))
      (patchClosed (B i)) (torusFactor (configurationFactor i f) J (A i))) :
    IsProbabilityMeasure (DeletedPairConditionals.jointLaw hJ A B d β) ∧
      ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ A B d β,
        DeletedOutsideDerivativeFormula hJ i d β (A i) (B i) f (removeSite i X) := by
  refine ⟨DeletedPairConditionals.jointLaw_probability hJ (by omega) hn A B d hβ
    (hβ₀.trans_lt hsub), ?_⟩
  have hc := capped_sourceCalculus K hJ (Nat.succ_pos n) hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    (otherParticles i) _ (isCompact_closedChart J _ _) (convex_closedChart J _ _)
    labels hcap hplace (DeletedPairEnsemble.coefficients d β i)
    (fun k _ ↦ (DeletedPairEnsemble.coefficients_bounds d hβ i k).1)
    (fun k _ ↦ (DeletedPairEnsemble.coefficients_bounds d hβ i k).2) (A i) (B i) hf
  apply ae_jointLaw_of_outsideReference hJ A B d β i
  apply ae_outsideReference_of_chart hJ (by omega) i A B
  exact ae_deletedOutsideDerivativeFormula hJ (by omega) i _ _ d β (A i) (B i) f hc hf

theorem deleted_physical_finiteness (hJ : 0 < J) (hJ2 : 2 ≤ J) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (a : MeshIndex J) (b : Patch)
    (S : Set (SourceSpace (otherParticles i))) (f : Configuration (n + 1) → ℝ)
    (hc : MovingPoleDerivativeIdentification.SourceCalculus
      (fun k : otherParticles i ↦ DeletedPairEnsemble.coefficients d β i k) J hJ a b S
      (configurationFactor i f))
    (hf : SmoothOnChart S (patchClosed b) (torusFactor (configurationFactor i f) J a))
    (X : SourceSpace (otherParticles i)) (hX : X ∈ S) :
    let Y := outsideCoordinates i X
    let ν := deletedOutsideKernel hJ i d β a b Y
    Integrable (fun z ↦ f (insertSite i z Y)) ν ∧ ∀ j : Fin n,
      Integrable (fun z ↦ coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)) ν ∧
      Integrable (fun z ↦ greenGradient (z - Y j)) ν ∧
      Integrable (fun z ↦ f (insertSite i z Y) • greenGradient (z - Y j)) ν := by
  dsimp only
  rw [deletedOutsideKernel_eq_source hJ hJ2 i d β a b X (hc.normalization.normalizer_pos X hX)]
  have hfin := hc.finiteness X hX
  simp only [source_patchDomain] at hfin
  refine ⟨hfin.1, fun j ↦ ⟨?_, hfin.2.2 (outsideCoordinates i X j)⟩⟩
  have hi := hc.integrable_factorBlock X hX (otherIndexEquiv i j)
  rw [source_patchDomain] at hi
  apply hi.congr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem (measurableSet_patchDomain J hJ a b)] with z hz
  exact configurationFactor_block_on_patch hJ i f a b hf hX (subset_closure hz)
    (otherIndexEquiv i j)

section CappedEndpoints

variable (K : MovingPoleIntegrability.KernelBounds) (hJ : 0 < J) (hn : 2 ≤ n + 1)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)

include K hn hβ hβ₀ hsub hC₀ hC₁ hk₀ hk₁ hmesh

/-- Prescribed-cell law, with either no deleted pair or one specified pair.
Only cap, Green bounds, source parameter bounds, and local smoothness are inputs. -/
theorem deleted_cell_jointLaw_derivatives (η : LabelVector J (n + 1))
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed .cell)
      (torusFactor (configurationFactor i f) J (η i))) :
    IsProbabilityMeasure (DeletedPairConditionals.jointLaw hJ η (fun _ ↦ .cell) d β) ∧
      ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (fun _ ↦ .cell) d β,
        DeletedOutsideDerivativeFormula hJ i d β (η i) .cell f (removeSite i X) :=
  capped_deleted_jointLaw_derivatives K hJ hn hβ hβ₀ hsub hC₀ hC₁ hk₀ hk₁ hmesh
    η (fun _ ↦ .cell) i (fun _ ↦ η) (fun _ _ ↦ hη)
    (fun _ hX ↦ cellChart_placement hJ (otherParticles i) η hX) d f hf

/-- Both completed labels are capped. The adjacent coordinate can be the
integrated coordinate or any retained source; both orientations and periodic
wrap are handled by the literal chart placement theorem. -/
theorem deleted_adjacent_jointLaw_derivatives (η : LabelVector J (n + 1))
    (i t : Fin (n + 1)) (r : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁)
      (Function.update η t (nextCell J hJ (η t) r)))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (adjacentChart (otherParticles i) η t r)
      (patchClosed (OneCoordinateConditionals.adjacentShapes t r i))
      (torusFactor (configurationFactor i f) J (η i))) :
    IsProbabilityMeasure
      (DeletedPairConditionals.jointLaw hJ η (OneCoordinateConditionals.adjacentShapes t r) d β) ∧
      ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (OneCoordinateConditionals.adjacentShapes t r) d β,
        DeletedOutsideDerivativeFormula hJ i d β (η i)
          (OneCoordinateConditionals.adjacentShapes t r i) f (removeSite i X) := by
  obtain ⟨labels, hcap, hplace⟩ := exists_capped_labels_one_adjacent hJ (otherParticles i)
    (adjacentChart (otherParticles i) η t r) η t r (fixedDelta β₀ C₀ C₁) hη₀ hη₁
    (fun _ hX ↦ adjacentChart_cell_placement hJ (otherParticles i) η t r hX)
    (fun _ hX ht ↦ adjacentChart_edge_placement hJ (otherParticles i) η t r hX ht)
  exact capped_deleted_jointLaw_derivatives K hJ hn hβ hβ₀ hsub hC₀ hC₁ hk₀ hk₁ hmesh
    η (OneCoordinateConditionals.adjacentShapes t r) i labels
    (fun X _ ↦ hcap X)
    (by simpa only [retained_adjacentChart] using hplace) d f
    (by simpa only [retained_adjacentChart] using hf)

end CappedEndpoints

/-- The outside-coordinate formula is exactly the physical coordinate
formula for the full joint observable and the actual ambient conditional
kernel. This is an identity of ordinary gradients, not only of their norms. -/
theorem deletedFormula_joint_coordinate (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (f : Configuration (n + 1) → ℝ) (X : Configuration (n + 1))
    (hX : DeletedOutsideDerivativeFormula hJ i d β (A i) (B i) f (removeSite i X)) (j : Fin n) :
    coordinateOrdinaryGradient
      (fun Y ↦ deletedOutsideLog hJ i d β (A i) (B i) (removeSite i Y)) (i.succAbove j) X =
      (-DeletedPairEnsemble.sourceCoefficient d β i j) •
        ∫ z, greenGradient (z - X (i.succAbove j)) ∂DeletedPairConditionals.ambientKernels hJ A B d β i X ∧
    coordinateOrdinaryGradient
      (fun Y ↦ deletedOutsideMean hJ i d β (A i) (B i) f (removeSite i Y)) (i.succAbove j) X =
      (∫ z, coordinateOrdinaryGradient f (i.succAbove j) (Function.update X i z)
        ∂DeletedPairConditionals.ambientKernels hJ A B d β i X) -
      DeletedPairEnsemble.sourceCoefficient d β i j • vectorCovariance
        (DeletedPairConditionals.ambientKernels hJ A B d β i X)
        (fun z ↦ f (Function.update X i z)) (fun z ↦ greenGradient (z - X (i.succAbove j))) := by
  simpa only [coordinateOrdinaryGradient_removeSite, deletedOutsideKernel_eq_ambient,
    CoordinateConditionalKernels.insertSite_eq_update, removeSite] using hX j

/-- The derivative statements on the full physical configuration, with
the actual ambient conditional kernel and the retained `Fin.succAbove` index. -/
def JointDeletedDerivativeFormula (hJ : 0 < J) (i : Fin (n + 1))
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (f : Configuration (n + 1) → ℝ) (X : Configuration (n + 1)) : Prop :=
  ∀ j : Fin n,
    coordinateOrdinaryGradient
      (fun Y ↦ deletedOutsideLog hJ i d β (A i) (B i) (removeSite i Y)) (i.succAbove j) X =
      (-DeletedPairEnsemble.sourceCoefficient d β i j) •
        ∫ z, greenGradient (z - X (i.succAbove j))
          ∂DeletedPairConditionals.ambientKernels hJ A B d β i X ∧
    coordinateOrdinaryGradient
      (fun Y ↦ deletedOutsideMean hJ i d β (A i) (B i) f (removeSite i Y)) (i.succAbove j) X =
      (∫ z, coordinateOrdinaryGradient f (i.succAbove j) (Function.update X i z)
        ∂DeletedPairConditionals.ambientKernels hJ A B d β i X) -
      DeletedPairEnsemble.sourceCoefficient d β i j • vectorCovariance
        (DeletedPairConditionals.ambientKernels hJ A B d β i X)
        (fun z ↦ f (Function.update X i z)) (fun z ↦ greenGradient (z - X (i.succAbove j)))

section JointEndpoints

variable (K : MovingPoleIntegrability.KernelBounds) (hJ : 0 < J) (hn : 2 ≤ n + 1)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)

include K hn hβ hβ₀ hsub hC₀ hC₁ hk₀ hk₁ hmesh

/-- Physical prescribed-cell endpoint for both log-normalizer and
conditional-mean derivatives under the actual (possibly deleted-pair) law. -/
theorem deleted_cell_joint_coordinate_derivatives (η : LabelVector J (n + 1))
    (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η) (i : Fin (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed .cell)
      (torusFactor (configurationFactor i f) J (η i))) :
    IsProbabilityMeasure (DeletedPairConditionals.jointLaw hJ η (fun _ ↦ .cell) d β) ∧
      ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (fun _ ↦ .cell) d β,
        JointDeletedDerivativeFormula hJ i η (fun _ ↦ .cell) d β f X := by
  obtain ⟨hp, hd⟩ := deleted_cell_jointLaw_derivatives K hJ hn hβ hβ₀ hsub hC₀ hC₁
    hk₀ hk₁ hmesh η hη i d f hf
  refine ⟨hp, hd.mono fun X hX j ↦ ?_⟩
  exact deletedFormula_joint_coordinate hJ i η (fun _ ↦ .cell) d β f X hX j

/-- Physical adjacent-union endpoint with both occupation caps, arbitrary
edge orientation and periodic wrap. The single adjacent coordinate can be
the integrated coordinate or a retained source. -/
theorem deleted_adjacent_joint_coordinate_derivatives (η : LabelVector J (n + 1))
    (i t : Fin (n + 1)) (r : Fin 2)
    (hη₀ : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (hη₁ : OccupationCap (fixedDelta β₀ C₀ C₁)
      (Function.update η t (nextCell J hJ (η t) r)))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (adjacentChart (otherParticles i) η t r)
      (patchClosed (OneCoordinateConditionals.adjacentShapes t r i))
      (torusFactor (configurationFactor i f) J (η i))) :
    IsProbabilityMeasure
      (DeletedPairConditionals.jointLaw hJ η (OneCoordinateConditionals.adjacentShapes t r) d β) ∧
      ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (OneCoordinateConditionals.adjacentShapes t r) d β,
        JointDeletedDerivativeFormula hJ i η (OneCoordinateConditionals.adjacentShapes t r) d β f X := by
  obtain ⟨hp, hd⟩ := deleted_adjacent_jointLaw_derivatives K hJ hn hβ hβ₀ hsub hC₀ hC₁
    hk₀ hk₁ hmesh η i t r hη₀ hη₁ d f hf
  refine ⟨hp, hd.mono fun X hX j ↦ ?_⟩
  exact deletedFormula_joint_coordinate hJ i η (OneCoordinateConditionals.adjacentShapes t r)
    d β f X hX j

end JointEndpoints

end DeletedSource

end PeriodicAttractiveLogGas.ConditionalSourceCharts
