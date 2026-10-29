import LeanResearch.PeriodicAttractiveLogGas.ConditionalEntropyDisintegration
import LeanResearch.PeriodicAttractiveLogGas.ConditionalSourceCharts

/-! The compact-rectangle test in manuscript lines 2702–2708.

The physical Euclidean chart, including its closed boundary, is retained.
Only the representative used in the entropy calculation is extended by zero;
no energy or derivative of that extension is identified in this module.
-/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.SourceEntropyTests

open MeshCells MeshAdjacentCells LabelOccupations ConditionalParameters
open GreenPointWeights
open MovingPoleNumerators MovingPoleCharts ConditionalSourceCharts
open OneCoordinateConditionals CellRestrictions
open ReferenceSelfTerms ReferenceDensityChange ReferenceConditionalNormalization
open ConditionalEntropyDisintegration

/-- Image of the literal closed physical rectangle, without choosing a
fundamental-domain representative at a periodic seam. -/
def closedRectangle {J N : ℕ} (η : LabelVector J N) : Set (Configuration N) :=
  sources '' closedChart J η (fun _ => Patch.cell)

theorem continuous_configuration_sources (N : ℕ) :
    Continuous (sources : SourceSpace (Fin N) → Configuration N) :=
  continuous_pi continuous_sources

theorem isCompact_closedRectangle {J N : ℕ} (η : LabelVector J N) :
    IsCompact (closedRectangle η) :=
  (isCompact_closedChart J η (fun _ => Patch.cell)).image
    (continuous_configuration_sources N)

theorem mem_closedRectangle {J N : ℕ} (hJ : 0 < J) (η : LabelVector J N)
    (X : Configuration N) :
    X ∈ closedRectangle η ↔ ∀ i, X i ∈ closure (meshCell J hJ (η i)) := by
  constructor
  · rintro ⟨Z, hZ, rfl⟩ i
    exact source_mem_closure_patch hJ η (fun _ => Patch.cell) hZ i
  · intro hX
    have hex (i : Fin N) : ∃ Z ∈ patchClosed Patch.cell, meshChart J (η i) Z = X i := by
      have hi := hX i
      rw [closure_meshCell J hJ (η i)] at hi
      exact hi
    choose Z hZ he using hex
    let W : SourceSpace (Fin N) := WithLp.toLp 2
      (fun ik => meshAffine J (η ik.1) (Z ik.1) ik.2)
    refine ⟨W, ?_, ?_⟩
    · rw [mem_closedChart_iff]
      intro ik
      have hb : meshAffine J (η ik.1) (Z ik.1) ∈
          physicalBlock J (η ik.1) Patch.cell := by
        rw [physicalBlock_eq_image hJ]
        exact mem_image_of_mem _ (hZ ik.1)
      exact hb ik.2 (mem_univ _)
    · funext i
      change torusQuotient (sourceProjection i W) = X i
      have hw : sourceProjection i W = meshAffine J (η i) (Z i) := by ext k; rfl
      rw [hw]
      exact he i

theorem ae_closedRectangle_labelGibbs {J N : ℕ} (hJ : 0 < J)
    (η : LabelVector J N) (β : ℝ) :
    ∀ᵐ X ∂labelGibbsMeasure hJ η β, X ∈ closedRectangle η := by
  apply Measure.ae_smul_measure
  apply (withDensity_absolutelyContinuous _ _).ae_le
  rw [labelReference_eq]
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (measurableSet_labelFiber hJ η)] with X hX
  exact (mem_closedRectangle hJ η X).mpr fun i =>
    subset_closure ((mem_labelFiber hJ η X).mp hX i)

theorem inserted_mem_closedRectangle {J n : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) {Y : Configuration n}
    (hY : PrescribedOutside hJ η i Y) {z : Torus}
    (hz : z ∈ closure (meshCell J hJ (η i))) :
    insertSite i z Y ∈ closedRectangle η := by
  rw [mem_closedRectangle hJ]
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [insertSite_self] using hz
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simpa only [insertSite_succAbove] using hY k

def chartMap {J N : ℕ} (η : LabelVector J N) :
    closedChart J η (fun _ => Patch.cell) → Configuration N := fun Z => sources Z.val

theorem chartMap_embedding {J N : ℕ} (hJ3 : 3 ≤ J) (η : LabelVector J N) :
    Topology.IsClosedEmbedding (chartMap η) := by
  let : CompactSpace (closedChart J η (fun _ => Patch.cell)) :=
    (isCompact_iff_compactSpace).mp (isCompact_closedChart J η (fun _ => Patch.cell))
  apply ((continuous_configuration_sources N).comp continuous_subtype_val).isClosedEmbedding
  intro Z W he
  exact Subtype.ext (sources_injOn_closedChart hJ3 η (fun _ => Patch.cell)
    Z.property W.property he)

/-- Square of the physical chart test on its compact image, and zero elsewhere. -/
def squareExtension {J N : ℕ} (η : LabelVector J N) (f : SourceSpace (Fin N) → ℝ) :
    Configuration N → ℝ :=
  Function.extend (chartMap η) (fun Z => f Z.val ^ 2) (fun _ => 0)

theorem squareExtension_sources {J N : ℕ} (hJ3 : 3 ≤ J) (η : LabelVector J N)
    (f : SourceSpace (Fin N) → ℝ) {Z : SourceSpace (Fin N)}
    (hZ : Z ∈ closedChart J η (fun _ => Patch.cell)) :
    squareExtension η f (sources Z) = f Z ^ 2 :=
  (chartMap_embedding hJ3 η).injective.extend_apply _ _ ⟨Z, hZ⟩

theorem measurable_squareExtension {J N : ℕ} (hJ3 : 3 ≤ J) (η : LabelVector J N)
    {f : SourceSpace (Fin N) → ℝ}
    (hf : ContinuousOn f (closedChart J η (fun _ => Patch.cell))) :
    Measurable (squareExtension η f) :=
  (chartMap_embedding hJ3 η).measurableEmbedding.measurable_extend
    (hf.pow 2).domRestrict.measurable measurable_const

theorem squareExtension_agrees {J N : ℕ} (hJ3 : 3 ≤ J) (η : LabelVector J N)
    (f : Configuration N → ℝ) {X : Configuration N} (hX : X ∈ closedRectangle η) :
    squareExtension η (fun Z => f (sources Z)) X = f X ^ 2 := by
  obtain ⟨Z, hZ, rfl⟩ := hX
  exact squareExtension_sources hJ3 η _ hZ

theorem squareExtension_bounds {J N : ℕ} (η : LabelVector J N)
    {f : SourceSpace (Fin N) → ℝ}
    (hf : ContinuousOn f (closedChart J η (fun _ => Patch.cell))) :
    ∃ K : ℝ, ∀ X, 0 ≤ squareExtension η f X ∧ squareExtension η f X ≤ K := by
  classical
  obtain ⟨C, hC⟩ := (isCompact_closedChart J η (fun _ => Patch.cell)).exists_bound_of_continuousOn hf
  refine ⟨(max C 0) ^ 2, ?_⟩
  intro X
  unfold squareExtension
  rw [Function.extend_def]
  split_ifs with hx
  · let Z := Classical.choose hx
    have hb₀ : |f Z.val| ≤ C := by simpa only [Real.norm_eq_abs] using hC Z.val Z.property
    have hb : |f Z.val| ≤ max C 0 := hb₀.trans (le_max_left C 0)
    exact ⟨sq_nonneg _, by nlinarith [sq_abs (f Z.val), abs_nonneg (f Z.val), le_max_right C 0]⟩
  · exact ⟨le_rfl, sq_nonneg _⟩

theorem ae_squareExtension_labelGibbs {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (η : LabelVector J N) (β : ℝ) (f : Configuration N → ℝ) :
    squareExtension η (fun Z => f (sources Z)) =ᵐ[labelGibbsMeasure hJ η β] fun X => f X ^ 2 :=
  (ae_closedRectangle_labelGibbs hJ η β).mono fun _ hX => squareExtension_agrees hJ3 η f hX

theorem ae_prescribedOutside_labelGibbs {J n : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) (i : Fin (n + 1)) :
    ∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β), PrescribedOutside hJ η i Y := by
  have hm : MeasurableSet {Y | PrescribedOutside hJ η i Y} := by
    have hh := MeasurableSet.univ_pi (fun j : Fin n =>
      (isClosed_closure : IsClosed (closure (meshCell J hJ (η (i.succAbove j))))).measurableSet)
    convert hh using 1
    ext Y
    simp only [PrescribedOutside, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
  apply (ae_map_iff (measurable_removeSite i).aemeasurable hm).mpr
  filter_upwards [ae_closedRectangle_labelGibbs hJ η β] with X hX
  exact fun j => (mem_closedRectangle hJ η X).mp hX (i.succAbove j)

/-- Every real density on the prescribed cell has the same section values
at every admissible closed-cell placement. No fallback-kernel claim is made. -/
theorem ae_squareExtension_section {J n : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (η : LabelVector J (n + 1)) (f : Configuration (n + 1) → ℝ) (i : Fin (n + 1))
    {Y : Configuration n} (hY : PrescribedOutside hJ η i Y) {ν : Measure Torus}
    (hν : ν ≪ meshCellMeasure J hJ (η i)) :
    (fun z => squareExtension η (fun Z => f (sources Z)) (insertSite i z Y)) =ᵐ[ν]
      fun z => f (insertSite i z Y) ^ 2 := by
  apply hν.ae_le
  filter_upwards [ae_mem_meshCell J hJ (η i)] with z hz
  exact squareExtension_agrees hJ3 η f (inserted_mem_closedRectangle hJ η i hY (subset_closure hz))

theorem normalizedTilt_congr_ae {α : Type*} [MeasurableSpace α] {P : Measure α}
    {F G : α → ℝ} (h : F =ᵐ[P] G) : normalizedTilt P F = normalizedTilt P G := by
  unfold normalizedTilt
  rw [integral_congr_ae h]
  exact withDensity_congr_ae (h.mono fun _ hx => congrArg (fun t => ENNReal.ofReal (t / ∫ y, G y ∂P)) hx)

theorem conditionalEntropyValue_congr_ae {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) {F G : A × B → ℝ} (x : A)
    (h : (fun y => F (x, y)) =ᵐ[κ x] fun y => G (x, y)) :
    conditionalEntropyValue κ F x = conditionalEntropyValue κ G x := by
  unfold conditionalEntropyValue ConditionalEntropyDisintegration.sectionMass
  have hlog : (fun y => F (x, y) * Real.log (F (x, y))) =ᵐ[κ x]
      fun y => G (x, y) * Real.log (G (x, y)) :=
    h.mono fun _ hx => congrArg (fun t => t * Real.log t) hx
  rw [integral_congr_ae h, integral_congr_ae hlog]

theorem conditionalLogEntropy_congr_ae {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) {F G : A × B → ℝ} (x : A)
    (h : (fun y => F (x, y)) =ᵐ[κ x] fun y => G (x, y)) :
    conditionalLogEntropy κ F x = conditionalLogEntropy κ G x := by
  unfold conditionalLogEntropy ConditionalEntropyDisintegration.sectionMass
  rw [integral_congr_ae h, normalizedTilt_congr_ae h]
  apply integral_congr_ae
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact h.mono fun _ hx => congrArg (fun t => Real.log (t / ∫ y, G (x, y) ∂κ x)) hx

/-- The original test is integrable without any condition away from its
closed physical source rectangle. -/
theorem source_square_integrable {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    Integrable (fun X => f X ^ 2) (labelGibbsMeasure hJ η β) ∧
      Integrable (fun X => f X ^ 2 * Real.log (f X ^ 2)) (labelGibbsMeasure hJ η β) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  have hi := RelativeEntropyVariational.bounded_density_integrable
    (P := labelGibbsMeasure hJ η β) (measurable_squareExtension hJ3 η hf.continuousOn)
    (Eventually.of_forall hb)
  have he := ae_squareExtension_labelGibbs hJ hJ3 η β f
  exact ⟨hi.1.congr he, hi.2.congr (he.mono fun _ hx => congrArg (fun t => t * Real.log t) hx)⟩

theorem source_zero_mass {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (hS : ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β = 0) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) = 0 ∧
      normalizedTilt (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) = 0 := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  have he := ae_squareExtension_labelGibbs hJ hJ3 η β f
  have hz := zero_mass_entropy (measurable_squareExtension hJ3 η hf.continuousOn)
    (Eventually.of_forall hb) ((integral_congr_ae he).trans hS)
  exact ⟨(entropy_congr_ae he).symm.trans hz.2, normalizedTilt_zero_mass hS⟩

section ReferenceSections

variable {J n : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1)) {β : ℝ}
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))

include hformula in
omit [∀ a, IsProbabilityMeasure (μ a)] in
theorem reference_cell_absolutelyContinuous (a : MeshIndex J) :
    μ a ≪ meshCellMeasure J hJ a := by
  rw [hformula a]
  exact withDensity_absolutelyContinuous _ _

include hJ3 hformula

omit [∀ a, IsProbabilityMeasure (μ a)] in
theorem ae_squareExtension_real_section (f : Configuration (n + 1) → ℝ)
    (i : Fin (n + 1)) {Y : Configuration n} (hY : PrescribedOutside hJ η i Y) :
    (fun z => squareExtension η (fun Z => f (sources Z)) (insertSite i z Y)) =ᵐ[
      (μ (η i)).withDensity (fun z => ENNReal.ofReal
        (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y))]
      fun z => f (insertSite i z Y) ^ 2 :=
  ae_squareExtension_section hJ hJ3 η f i hY
    ((withDensity_absolutelyContinuous _ _).trans
      (reference_cell_absolutelyContinuous hJ μ η hformula (η i)))

/-- Equality for every admissible fixed placement uses the actual finite
source conditional section theorem, including repeated outside positions. -/
theorem ae_squareExtension_conditional_fixed {β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (hη : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η)
    (f : Configuration (n + 1) → ℝ) (i : Fin (n + 1)) {Y : Configuration n}
    (hY : PrescribedOutside hJ η i Y) :
    (fun z => squareExtension η (fun Z => f (sources Z)) (insertSite i z Y)) =ᵐ[
      PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y]
      fun z => f (insertSite i z Y) ^ 2 := by
  rw [conditionalKernel_eq_reference_density hJ μ η hβ hβ₀ hformula hmesh hη i Y hY]
  exact ae_squareExtension_real_section hJ hJ3 μ η hformula f i hY

/-- Only a null set of actual outside configurations is discarded. No
global measurability of the unextended source test is needed. -/
theorem ae_squareExtension_conditional (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hsub : β < 4)
    (f : Configuration (n + 1) → ℝ) (i : Fin (n + 1)) :
    ∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β),
      (fun z => squareExtension η (fun Z => f (sources Z)) (insertSite i z Y)) =ᵐ[
        PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
          (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y]
        fun z => f (insertSite i z Y) ^ 2 := by
  have hi := (change_of_reference hJ hN μ η hβ hsub hformula).1
  have hfin := (PositiveProductConditionals.normalizer_ne_top_iff_integrable
    (fun i => μ (η i)) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _)).mpr hi
  have hk := PositiveProductConditionals.conditionalKernel_ae_eq_real_density
    (fun i => μ (η i)) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i hfin
  change ∀ᵐ Y ∂Measure.map (removeSite i)
    (PositiveProductConditionals.productLaw (fun i => μ (η i)) (referenceTilt μ η β)), _ at hk
  rw [reference_productLaw_eq_labelGibbs hJ hN μ η hβ hsub hformula] at hk
  filter_upwards [hk, ae_prescribedOutside_labelGibbs hJ η β i] with Y hK hY
  rw [hK]
  exact ae_squareExtension_section hJ hJ3 η f i hY
    ((withDensity_absolutelyContinuous _ _).trans
      (reference_cell_absolutelyContinuous hJ μ η hformula (η i)))

omit hformula [∀ a, IsProbabilityMeasure (μ a)] in
theorem source_bounded_tilt (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (hS : 0 < ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) :
    IsProbabilityMeasure (normalizedTilt (labelGibbsMeasure hJ η β) (fun X => f X ^ 2)) ∧
      ∃ K : ℝ, ∀ᵐ X ∂labelGibbsMeasure hJ η β,
        0 ≤ f X ^ 2 / (∫ Y, f Y ^ 2 ∂labelGibbsMeasure hJ η β) ∧
        f X ^ 2 / (∫ Y, f Y ^ 2 ∂labelGibbsMeasure hJ η β) ≤ K := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  refine ⟨normalizedTilt_probability (Eventually.of_forall fun X => sq_nonneg (f X))
    (source_square_integrable hJ hJ3 hN η hβ hsub hf).1 hS, ?_⟩
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  refine ⟨K / (∫ Y, f Y ^ 2 ∂labelGibbsMeasure hJ η β), ?_⟩
  filter_upwards [ae_squareExtension_labelGibbs hJ hJ3 η β f] with X hX
  exact ⟨div_nonneg (sq_nonneg _) hS.le,
    div_le_div_of_nonneg_right (hX ▸ (hb X).2) hS.le⟩

/-- Exact source entropy identity for the literal squared particle test.
The only regularity premise is Lipschitz continuity on its physical closed
rectangle. The globally bounded representative is constructed internally. -/
theorem source_lipschitz_entropy_sum (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (hS : 0 < ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) :
    let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    let G := fun i (p : Configuration n × Torus) => f (insertSite i p.2 p.1) ^ 2
    (∀ i, Integrable (fun X => conditionalLogEntropy (κ i) (G i) (removeSite i X))
      (normalizedTilt (labelGibbsMeasure hJ η β) (fun X => f X ^ 2))) ∧
    (∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) *
      (∑ i, ∫ X, conditionalLogEntropy (κ i) (G i) (removeSite i X)
        ∂normalizedTilt (labelGibbsMeasure hJ η β) (fun X => f X ^ 2)) =
      ∑ i, ∫ X, conditionalEntropyValue (κ i) (G i) (removeSite i X)
        ∂labelGibbsMeasure hJ η β := by
  let P := labelGibbsMeasure hJ η β
  let F := squareExtension η (fun Z => f (sources Z))
  let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let F' := fun i (p : Configuration n × Torus) => F (insertSite i p.2 p.1)
  let G := fun i (p : Configuration n × Torus) => f (insertSite i p.2 p.1) ^ 2
  have hm : Measurable F := measurable_squareExtension hJ3 η hf.continuousOn
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  have he : F =ᵐ[P] fun X => f X ^ 2 := ae_squareExtension_labelGibbs hJ hJ3 η β f
  have hmass : (∫ X, F X ∂P) = ∫ X, f X ^ 2 ∂P := integral_congr_ae he
  have ht : normalizedTilt P F = normalizedTilt P (fun X => f X ^ 2) := normalizedTilt_congr_ae he
  have hsec (i : Fin (n + 1)) : ∀ᵐ X ∂P,
      (fun z => F' i (removeSite i X, z)) =ᵐ[κ i (removeSite i X)]
        fun z => G i (removeSite i X, z) :=
    ae_of_ae_map (measurable_removeSite i).aemeasurable
      (ae_squareExtension_conditional hJ hJ3 μ η hformula hN hβ hsub f i)
  have hlog (i : Fin (n + 1)) :
      (fun X => conditionalLogEntropy (κ i) (F' i) (removeSite i X)) =ᵐ[
        normalizedTilt P (fun X => f X ^ 2)]
      fun X => conditionalLogEntropy (κ i) (G i) (removeSite i X) := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact (hsec i).mono fun X hX => conditionalLogEntropy_congr_ae (κ i) (removeSite i X) hX
  have hval (i : Fin (n + 1)) :
      (fun X => conditionalEntropyValue (κ i) (F' i) (removeSite i X)) =ᵐ[P]
      fun X => conditionalEntropyValue (κ i) (G i) (removeSite i X) :=
    (hsec i).mono fun X hX => conditionalEntropyValue_congr_ae (κ i) (removeSite i X) hX
  constructor
  · intro i
    have hi := (source_entropy_disintegration hJ hN μ η hβ hsub hformula i hm hb
      (hmass.symm ▸ hS)).1
    change Integrable (fun X => conditionalLogEntropy (κ i) (F' i) (removeSite i X))
      (normalizedTilt P F) at hi
    rw [ht] at hi
    exact hi.congr (hlog i)
  · have hh := source_sum_entropy_disintegration hJ hN μ η hβ hsub hformula hm hb
      (hmass.symm ▸ hS)
    change (∫ X, F X ∂P) *
      (∑ i, ∫ X, conditionalLogEntropy (κ i) (F' i) (removeSite i X) ∂normalizedTilt P F) =
      ∑ i, ∫ X, conditionalEntropyValue (κ i) (F' i) (removeSite i X) ∂P at hh
    rw [hmass, ht] at hh
    calc
      _ = (∫ X, f X ^ 2 ∂P) *
          (∑ i, ∫ X, conditionalLogEntropy (κ i) (F' i) (removeSite i X)
            ∂normalizedTilt P (fun X => f X ^ 2)) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => (integral_congr_ae (hlog i)).symm
      _ = _ := hh
      _ = _ := Finset.sum_congr rfl fun i _ => integral_congr_ae (hval i)

theorem ae_source_conditionalEntropyValue_eq_entropy (hN : 2 ≤ n + 1)
    (hβ : 0 ≤ β) (hsub : β < 4) {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (i : Fin (n + 1)) :
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    let G := fun p : Configuration n × Torus => f (insertSite i p.2 p.1) ^ 2
    ∀ᵐ Y ∂Measure.map (removeSite i) (labelGibbsMeasure hJ η β),
      (conditionalEntropyValue κ G Y : EReal) = entropy (κ Y) (fun z => f (insertSite i z Y) ^ 2) := by
  let F := squareExtension η (fun Z => f (sources Z))
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  let F' := fun p : Configuration n × Torus => F (insertSite i p.2 p.1)
  let G := fun p : Configuration n × Torus => f (insertSite i p.2 p.1) ^ 2
  let : IsMarkovKernel κ := PositiveProductConditionals.isMarkovKernel_conditionalKernel
    (μ (η i)) (referenceTilt μ η β) (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  have hm : Measurable F' := (measurable_squareExtension hJ3 η hf.continuousOn).comp
    ((measurable_insertSite i).comp measurable_swap)
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  filter_upwards [ae_squareExtension_conditional hJ hJ3 μ η hformula hN hβ hsub f i] with Y hY
  have hv : conditionalEntropyValue κ F' Y = conditionalEntropyValue κ G Y :=
    conditionalEntropyValue_congr_ae κ Y hY
  change (conditionalEntropyValue κ G Y : EReal) = _
  rw [← hv]
  exact (conditionalEntropyValue_eq_entropy κ hm (fun Y z => hb (insertSite i z Y)) Y).trans
    (entropy_congr_ae hY)

end ReferenceSections

end PeriodicAttractiveLogGas.SourceEntropyTests
