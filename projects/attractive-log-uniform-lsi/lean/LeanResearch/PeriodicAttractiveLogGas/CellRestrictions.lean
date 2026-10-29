import LeanResearch.PeriodicAttractiveLogGas.MeshAdjacentCells
import LeanResearch.PeriodicAttractiveLogGas.GreenNormalization
import Mathlib.Probability.ConditionalProbability

/-! The actual specified-label and two-cell laws in
source lines 331–370. The product of normalized cell measures is proved equal
to the scaled product-Haar restriction. Actual Green normalizers are positive
and finite in the stated subcritical range. Conditioning means the existing
`ProbabilityTheory.cond` on the genuine measurable event. No arbitrary marginal
Gibbs representation, exchangeability or occupation multinomial is asserted.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.CellRestrictions

open MeshCells MeshAdjacentCells

/-- The actual product of prescribed half-open cells. -/
def labelFiber {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) : Set (Configuration N) :=
  Set.pi Set.univ fun i ↦ meshCell J hJ (η i)

theorem measurableSet_labelFiber {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) :
    MeasurableSet (labelFiber hJ η) :=
  MeasurableSet.univ_pi fun i ↦ measurableSet_meshCell J hJ (η i)

@[simp] theorem mem_labelFiber {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (X : Configuration N) : X ∈ labelFiber hJ η ↔ ∀ i, X i ∈ meshCell J hJ (η i) := by
  simp only [labelFiber, Set.mem_pi, Set.mem_univ, forall_const]

theorem labelFiber_eq_label_preimage {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) :
    labelFiber hJ η = configurationMeshLabel N J hJ ⁻¹' {η} := by
  ext X
  simp only [mem_labelFiber, mem_meshCell, Set.mem_preimage, Set.mem_singleton_iff,
    funext_iff, configurationMeshLabel]

theorem disjoint_labelFiber {N J : ℕ} (hJ : 0 < J) {η ζ : Fin N → MeshIndex J}
    (hηζ : η ≠ ζ) : Disjoint (labelFiber hJ η) (labelFiber hJ ζ) := by
  apply Set.disjoint_left.mpr
  intro X hX hX'
  apply hηζ
  have hη := (mem_labelFiber hJ η X).mp hX
  have hζ := (mem_labelFiber hJ ζ X).mp hX'
  funext i
  exact (hη i).symm.trans (hζ i)

def labelScale (J N : ℕ) : ℝ≥0∞ := (J : ℝ≥0∞) ^ (2 * N)

theorem labelScale_ne_zero {J : ℕ} (hJ : 0 < J) (N : ℕ) : labelScale J N ≠ 0 := by
  apply pow_ne_zero
  exact_mod_cast hJ.ne'

theorem labelScale_ne_top (J N : ℕ) : labelScale J N ≠ ⊤ := by
  unfold labelScale
  finiteness

/-- The source's product of normalized single-cell Haar measures. -/
def labelReference {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) :
    Measure (Configuration N) := Measure.pi fun i ↦ meshCellMeasure J hJ (η i)

instance isProbabilityMeasure_labelReference {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) : IsProbabilityMeasure (labelReference hJ η) := by
  unfold labelReference
  infer_instance

/-- Proved on measurable rectangles using actual product-measure uniqueness. -/
theorem labelReference_eq {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) :
    labelReference hJ η = labelScale J N • (referenceMeasure N).restrict (labelFiber hJ η) := by
  unfold labelReference
  apply Measure.pi_eq
  intro s hs
  have hcell (i : Fin N) : meshCellMeasure J hJ (η i) (s i) =
      (J : ℝ≥0∞) ^ 2 * torusMeasure (s i ∩ meshCell J hJ (η i)) :=
    meshCellMeasure_apply J hJ (η i) (hs i)
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  rw [labelFiber, ← Set.pi_inter_distrib, referenceMeasure, Measure.pi_pi]
  simp_rw [hcell]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  rfl

theorem referenceMeasure_labelFiber {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) :
    referenceMeasure N (labelFiber hJ η) = (labelScale J N)⁻¹ := by
  rw [referenceMeasure, labelFiber, Measure.pi_pi]
  simp_rw [torusMeasure_meshCell J hJ]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.inv_pow, ← pow_mul]
  rfl

theorem referenceMeasure_labelFiber_ne_zero {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) : referenceMeasure N (labelFiber hJ η) ≠ 0 := by
  rw [referenceMeasure_labelFiber]
  exact ENNReal.inv_ne_zero.mpr (labelScale_ne_top J N)

def greenWeightDensity (N : ℕ) (β : ℝ) (X : Configuration N) : ℝ≥0∞ :=
  ENNReal.ofReal (gibbsWeight greenRealRepresentative N β X)

theorem measurable_greenWeightDensity (N : ℕ) (β : ℝ) : Measurable (greenWeightDensity N β) :=
  (measurable_gibbsWeight greenRealRepresentative_measurable N β).ennreal_ofReal

theorem greenWeightDensity_pos (N : ℕ) (β : ℝ) (X : Configuration N) :
    0 < greenWeightDensity N β X := ENNReal.ofReal_pos.mpr (gibbsWeight_pos _ N β X)

def greenWeightedReference (N : ℕ) (β : ℝ) : Measure (Configuration N) :=
  (referenceMeasure N).withDensity (greenWeightDensity N β)

/-- The actual extended cell normalizer, before its positive finiteness is proved. -/
def labelPartitionFunction {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (β : ℝ) : ℝ≥0∞ := ∫⁻ X, greenWeightDensity N β X ∂labelReference hJ η

theorem labelPartitionFunction_eq_scale {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) (β : ℝ) :
    labelPartitionFunction hJ η β = labelScale J N *
      ∫⁻ X in labelFiber hJ η, greenWeightDensity N β X ∂referenceMeasure N := by
  rw [labelPartitionFunction, labelReference_eq, lintegral_smul_measure, smul_eq_mul]

theorem labelPartitionFunction_ne_zero {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) (β : ℝ) : labelPartitionFunction hJ η β ≠ 0 := by
  intro h
  have hae := (lintegral_eq_zero_iff (measurable_greenWeightDensity N β)).mp h
  obtain ⟨X, hX⟩ := hae.exists
  exact (greenWeightDensity_pos N β X).ne' hX

theorem labelPartitionFunction_ne_top {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    labelPartitionFunction hJ η β ≠ ⊤ := by
  rw [labelPartitionFunction_eq_scale]
  apply ENNReal.mul_ne_top (labelScale_ne_top J N)
  have hi : (∫⁻ X, greenWeightDensity N β X ∂referenceMeasure N) ≠ ⊤ :=
    green_partitionFunction_ne_top N hN hβ hsub
  exact ne_top_of_le_ne_top hi (setLIntegral_le_lintegral _ _)

theorem integrable_label_greenWeight {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Integrable (gibbsWeight greenRealRepresentative N β) (labelReference hJ η) :=
  (lintegral_ofReal_ne_top_iff_integrable
    (measurable_gibbsWeight greenRealRepresentative_measurable N β).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun X ↦ (gibbsWeight_pos _ N β X).le))).mp
      (labelPartitionFunction_ne_top hJ hN η hβ hsub)

theorem labelPartitionFunction_eq_ofReal_integral {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    labelPartitionFunction hJ η β =
      ENNReal.ofReal (∫ X, gibbsWeight greenRealRepresentative N β X ∂labelReference hJ η) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_label_greenWeight hJ hN η hβ hsub)
    (Filter.Eventually.of_forall (fun X ↦ (gibbsWeight_pos _ N β X).le))).symm

/-- The literal normalized exponential density relative to the product cell law. -/
def labelGibbsMeasure {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) (β : ℝ) :
    Measure (Configuration N) :=
  (labelPartitionFunction hJ η β)⁻¹ • (labelReference hJ η).withDensity (greenWeightDensity N β)

theorem isProbabilityMeasure_labelGibbsMeasure {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    IsProbabilityMeasure (labelGibbsMeasure hJ η β) := by
  constructor
  rw [labelGibbsMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (labelPartitionFunction_ne_zero hJ η β)
    (labelPartitionFunction_ne_top hJ hN η hβ hsub)

/-- Normalized restriction is invariant under a finite nonzero scalar. -/
theorem cond_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hct : c ≠ ⊤) :
    ProbabilityTheory.cond (c • μ) s = ProbabilityTheory.cond μ s := by
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_smul, smul_smul]
  rw [ENNReal.mul_inv (Or.inl hc₀) (Or.inl hct)]
  congr 1
  rw [mul_right_comm, ENNReal.inv_mul_cancel hc₀ hct, one_mul]

theorem cond_restrict_univ {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    ProbabilityTheory.cond (μ.restrict s) Set.univ = ProbabilityTheory.cond μ s := by
  simp only [ProbabilityTheory.cond, Measure.restrict_apply_univ, Measure.restrict_univ]

theorem labelGibbsMeasure_eq_cond_weighted {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) (β : ℝ) :
    labelGibbsMeasure hJ η β = ProbabilityTheory.cond (greenWeightedReference N β) (labelFiber hJ η) := by
  have hnorm : labelGibbsMeasure hJ η β = ProbabilityTheory.cond
      ((labelReference hJ η).withDensity (greenWeightDensity N β)) Set.univ := by
    simp only [labelGibbsMeasure, ProbabilityTheory.cond,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, labelPartitionFunction]
  rw [hnorm, labelReference_eq, withDensity_smul_measure,
    ← restrict_withDensity (measurableSet_labelFiber hJ η),
    cond_smul _ _ (labelScale_ne_zero hJ N) (labelScale_ne_top J N), cond_restrict_univ]
  rfl

/-- The actual Gibbs law conditioned on the specified complete label vector. -/
theorem labelGibbsMeasure_eq_cond {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    labelGibbsMeasure hJ η β =
      ProbabilityTheory.cond (gibbsMeasure greenRealRepresentative N β) (labelFiber hJ η) := by
  rw [labelGibbsMeasure_eq_cond_weighted]
  change ProbabilityTheory.cond (greenWeightedReference N β) (labelFiber hJ η) =
    ProbabilityTheory.cond ((partitionFunction greenRealRepresentative N β)⁻¹ •
      greenWeightedReference N β) (labelFiber hJ η)
  exact (cond_smul _ _
    (ENNReal.inv_ne_zero.mpr (green_partitionFunction_ne_top N hN hβ hsub))
    (ENNReal.inv_ne_top.mpr (partitionFunction_ne_zero greenRealRepresentative_measurable N β))).symm

def labelProbability {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) (β : ℝ) : ℝ≥0∞ :=
  gibbsMeasure greenRealRepresentative N β (labelFiber hJ η)

/-- Exact source mass: `J^(-2N) * Z^η / Z`. The normalizers are the actual integrals. -/
theorem labelProbability_eq {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J) (β : ℝ) :
    labelProbability hJ η β =
      (labelScale J N)⁻¹ * labelPartitionFunction hJ η β /
        partitionFunction greenRealRepresentative N β := by
  rw [labelProbability, gibbsMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurableSet_labelFiber hJ η), labelPartitionFunction_eq_scale,
    div_eq_mul_inv, ENNReal.inv_mul_cancel_left (labelScale_ne_zero hJ N) (labelScale_ne_top J N)]
  exact mul_comm _ _

theorem labelProbability_ne_zero {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    labelProbability hJ η β ≠ 0 := by
  rw [labelProbability_eq, div_eq_mul_inv]
  exact mul_ne_zero
    (mul_ne_zero (ENNReal.inv_ne_zero.mpr (labelScale_ne_top J N))
      (labelPartitionFunction_ne_zero hJ η β))
    (ENNReal.inv_ne_zero.mpr (green_partitionFunction_ne_top N hN hβ hsub))

theorem labelProbability_ne_top {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    labelProbability hJ η β ≠ ⊤ := by
  let hprob : IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β) :=
    isProbabilityMeasure_greenGibbs N hN hβ hsub
  change gibbsMeasure greenRealRepresentative N β (labelFiber hJ η) ≠ ⊤
  exact measure_ne_top _ _

@[simp] theorem labelPartitionFunction_zero_coupling {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) : labelPartitionFunction hJ η 0 = 1 := by
  simp [labelPartitionFunction, greenWeightDensity]

@[simp] theorem labelGibbsMeasure_zero_coupling {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) : labelGibbsMeasure hJ η 0 = labelReference hJ η := by
  have hd : greenWeightDensity N 0 = 1 := by
    funext X
    simp [greenWeightDensity]
  simp [labelGibbsMeasure, hd]

@[simp] theorem labelProbability_zero_coupling {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) : labelProbability hJ η 0 = (labelScale J N)⁻¹ := by
  simp [labelProbability_eq]

@[simp] theorem labelFiber_zero_particles {J : ℕ} (hJ : 0 < J) (η : Fin 0 → MeshIndex J) :
    labelFiber hJ η = Set.univ := by
  ext X
  simp [labelFiber]

@[simp] theorem labelPartitionFunction_zero_particles {J : ℕ} (hJ : 0 < J)
    (η : Fin 0 → MeshIndex J) (β : ℝ) : labelPartitionFunction hJ η β = 1 := by
  simp [labelPartitionFunction, greenWeightDensity, gibbsWeight, pairEnergy]

@[simp] theorem labelGibbsMeasure_zero_particles {J : ℕ} (hJ : 0 < J)
    (η : Fin 0 → MeshIndex J) (β : ℝ) : labelGibbsMeasure hJ η β = labelReference hJ η := by
  have hd : greenWeightDensity 0 β = 1 := by
    funext X
    simp [greenWeightDensity, gibbsWeight, pairEnergy]
  simp [labelGibbsMeasure, hd]

@[simp] theorem labelProbability_zero_particles {J : ℕ} (hJ : 0 < J)
    (η : Fin 0 → MeshIndex J) (β : ℝ) : labelProbability hJ η β = 1 := by
  rw [labelProbability_eq, labelPartitionFunction_zero_particles]
  simp [labelScale, partitionFunction, gibbsWeight, pairEnergy]

theorem labelGibbsMeasure_labelFiber {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    labelGibbsMeasure hJ η β (labelFiber hJ η) = 1 := by
  rw [labelGibbsMeasure_eq_cond hJ hN η hβ hsub]
  exact ProbabilityTheory.cond_apply_self (labelProbability_ne_zero hJ hN η hβ hsub)
    (labelProbability_ne_top hJ hN η hβ hsub)

theorem mem_labelFiber_update {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (i : Fin N) (a : MeshIndex J) (X : Configuration N) :
    X ∈ labelFiber hJ (Function.update η i a) ↔
      X i ∈ meshCell J hJ a ∧ ∀ k, k ≠ i → X k ∈ meshCell J hJ (η k) := by
  rw [mem_labelFiber]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Function.update_self] using h i
    · intro k hk
      simpa only [Function.update_of_ne hk] using h k
  · rintro ⟨hi, hrest⟩ k
    by_cases hk : k = i
    · subst k
      simpa only [Function.update_self] using hi
    · simpa only [Function.update_of_ne hk] using hrest k hk

/-- This event fixes every other prescribed label and allows exactly the two
listed cells for the distinguished particle. It is not a product approximation. -/
def twoCellFiber {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (i : Fin N) (a b : MeshIndex J) : Set (Configuration N) :=
  {X | X i ∈ meshCell J hJ a ∪ meshCell J hJ b ∧
    ∀ k, k ≠ i → X k ∈ meshCell J hJ (η k)}

theorem twoCellFiber_eq_union {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (i : Fin N) (a b : MeshIndex J) :
    twoCellFiber hJ η i a b = labelFiber hJ (Function.update η i a) ∪
      labelFiber hJ (Function.update η i b) := by
  ext X
  rw [Set.mem_union, mem_labelFiber_update, mem_labelFiber_update]
  change ((X i ∈ meshCell J hJ a ∨ X i ∈ meshCell J hJ b) ∧
    ∀ k, k ≠ i → X k ∈ meshCell J hJ (η k)) ↔ _
  constructor
  · rintro ⟨ha | hb, hrest⟩
    · exact Or.inl ⟨ha, hrest⟩
    · exact Or.inr ⟨hb, hrest⟩
  · rintro (⟨ha, hrest⟩ | ⟨hb, hrest⟩)
    · exact ⟨Or.inl ha, hrest⟩
    · exact ⟨Or.inr hb, hrest⟩

theorem measurableSet_twoCellFiber {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (i : Fin N) (a b : MeshIndex J) : MeasurableSet (twoCellFiber hJ η i a b) := by
  rw [twoCellFiber_eq_union]
  exact (measurableSet_labelFiber hJ _).union (measurableSet_labelFiber hJ _)

theorem disjoint_updated_labelFibers {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b) :
    Disjoint (labelFiber hJ (Function.update η i a)) (labelFiber hJ (Function.update η i b)) := by
  apply disjoint_labelFiber hJ
  intro h
  apply hab
  simpa only [Function.update_self] using congrFun h i

theorem twoCellFiber_eq_adjacent_event {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) (i : Fin N) (a : MeshIndex J) (j : Fin 2) :
    twoCellFiber hJ η i a (nextCell J hJ a j) =
      {X | X i ∈ edgeCellUnion J hJ a j ∧ ∀ k, k ≠ i → X k ∈ meshCell J hJ (η k)} := rfl

/-- A normalized restriction to a genuine disjoint union is the exact weighted
mixture of its two normalized restrictions. All cancellation gates are explicit. -/
theorem cond_union_mixture {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s t : Set α} (_hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t)
    (hs₀ : μ s ≠ 0) (hst : μ s ≠ ⊤) (ht₀ : μ t ≠ 0) (htt : μ t ≠ ⊤) :
    ProbabilityTheory.cond μ (s ∪ t) =
      (μ s / (μ s + μ t)) • ProbabilityTheory.cond μ s +
      (μ t / (μ s + μ t)) • ProbabilityTheory.cond μ t := by
  have hleft : (μ s / (μ s + μ t)) * (μ s)⁻¹ = (μ s + μ t)⁻¹ := by
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hs₀ hst, one_mul]
  have hright : (μ t / (μ s + μ t)) * (μ t)⁻¹ = (μ s + μ t)⁻¹ := by
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel ht₀ htt, one_mul]
  simp only [ProbabilityTheory.cond, measure_union hd ht, Measure.restrict_union hd ht,
    smul_add, smul_smul, hleft, hright]

theorem mass_ratios_add_one {p q : ℝ≥0∞} (hp₀ : p ≠ 0) (hpt : p ≠ ⊤) (hqt : q ≠ ⊤) :
    p / (p + q) + q / (p + q) = 1 := by
  have hpq₀ : p + q ≠ 0 := by
    intro h
    have hp : p ≤ 0 := by
      calc
        p ≤ p + q := le_add_of_nonneg_right zero_le
        _ = 0 := h
    exact hp₀ (le_antisymm hp zero_le)
  rw [ENNReal.div_add_div_same]
  exact ENNReal.div_self hpq₀ (ENNReal.add_ne_top.mpr ⟨hpt, hqt⟩)

theorem mass_ratio_complement {p q : ℝ≥0∞} (hp₀ : p ≠ 0) (hpt : p ≠ ⊤) (hqt : q ≠ ⊤) :
    q / (p + q) = 1 - p / (p + q) := by
  apply ENNReal.eq_sub_of_add_eq' (by finiteness)
  simpa only [add_comm] using mass_ratios_add_one hp₀ hpt hqt

def twoCellGibbsMeasure {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (i : Fin N) (a b : MeshIndex J) (β : ℝ) : Measure (Configuration N) :=
  ProbabilityTheory.cond (gibbsMeasure greenRealRepresentative N β) (twoCellFiber hJ η i a b)

def twoCellMixingWeight {N J : ℕ} (hJ : 0 < J) (η : Fin N → MeshIndex J)
    (i : Fin N) (a b : MeshIndex J) (β : ℝ) : ℝ≥0∞ :=
  labelProbability hJ (Function.update η i a) β /
    (labelProbability hJ (Function.update η i a) β + labelProbability hJ (Function.update η i b) β)

theorem greenGibbs_twoCellFiber {N J : ℕ} (hJ : 0 < J)
    (η : Fin N → MeshIndex J) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b) (β : ℝ) :
    gibbsMeasure greenRealRepresentative N β (twoCellFiber hJ η i a b) =
      labelProbability hJ (Function.update η i a) β + labelProbability hJ (Function.update η i b) β := by
  rw [twoCellFiber_eq_union, measure_union (disjoint_updated_labelFibers hJ η i hab)
    (measurableSet_labelFiber hJ _)]
  rfl

theorem greenGibbs_twoCellFiber_ne_zero {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    gibbsMeasure greenRealRepresentative N β (twoCellFiber hJ η i a b) ≠ 0 := by
  rw [greenGibbs_twoCellFiber hJ η i hab]
  intro h
  apply labelProbability_ne_zero hJ hN (Function.update η i a) hβ hsub
  apply le_antisymm _ zero_le
  calc
    _ ≤ labelProbability hJ (Function.update η i a) β +
        labelProbability hJ (Function.update η i b) β := le_add_of_nonneg_right zero_le
    _ = 0 := h

theorem isProbabilityMeasure_twoCellGibbsMeasure {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    IsProbabilityMeasure (twoCellGibbsMeasure hJ η i a b β) := by
  let hprob : IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β) :=
    isProbabilityMeasure_greenGibbs N hN hβ hsub
  exact ProbabilityTheory.cond_isProbabilityMeasure
    (greenGibbs_twoCellFiber_ne_zero hJ hN η i hab hβ hsub)

theorem twoCellMixingWeight_le_one {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) (i : Fin N) (a b : MeshIndex J)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) : twoCellMixingWeight hJ η i a b β ≤ 1 := by
  have hsum := mass_ratios_add_one
    (labelProbability_ne_zero hJ hN (Function.update η i a) hβ hsub)
    (labelProbability_ne_top hJ hN (Function.update η i a) hβ hsub)
    (labelProbability_ne_top hJ hN (Function.update η i b) hβ hsub)
  unfold twoCellMixingWeight
  rw [← hsum]
  exact le_add_of_nonneg_right zero_le

/-- Exact source mixture with its actual Gibbs event-mass coefficient. -/
theorem twoCellGibbsMeasure_eq_mixture {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η : Fin N → MeshIndex J) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    twoCellGibbsMeasure hJ η i a b β =
      twoCellMixingWeight hJ η i a b β • labelGibbsMeasure hJ (Function.update η i a) β +
      (1 - twoCellMixingWeight hJ η i a b β) • labelGibbsMeasure hJ (Function.update η i b) β := by
  have ha₀ := labelProbability_ne_zero hJ hN (Function.update η i a) hβ hsub
  have hat := labelProbability_ne_top hJ hN (Function.update η i a) hβ hsub
  have hb₀ := labelProbability_ne_zero hJ hN (Function.update η i b) hβ hsub
  have hbt := labelProbability_ne_top hJ hN (Function.update η i b) hβ hsub
  rw [twoCellGibbsMeasure, twoCellFiber_eq_union,
    cond_union_mixture _ (measurableSet_labelFiber hJ _) (measurableSet_labelFiber hJ _)
      (disjoint_updated_labelFibers hJ η i hab) ha₀ hat hb₀ hbt,
    ← labelGibbsMeasure_eq_cond hJ hN (Function.update η i a) hβ hsub,
    ← labelGibbsMeasure_eq_cond hJ hN (Function.update η i b) hβ hsub]
  let p := labelProbability hJ (Function.update η i a) β
  let q := labelProbability hJ (Function.update η i b) β
  change (p / (p + q)) • labelGibbsMeasure hJ (Function.update η i a) β +
      (q / (p + q)) • labelGibbsMeasure hJ (Function.update η i b) β =
    (p / (p + q)) • labelGibbsMeasure hJ (Function.update η i a) β +
      (1 - p / (p + q)) • labelGibbsMeasure hJ (Function.update η i b) β
  rw [mass_ratio_complement ha₀ hat hbt]

/-- Both cyclic orientations and wrap are included by the actual successor. -/
theorem adjacentCellGibbsMeasure_eq_mixture {N J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hN : 2 ≤ N) (η : Fin N → MeshIndex J) (i : Fin N) (a : MeshIndex J) (j : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    ProbabilityTheory.cond (gibbsMeasure greenRealRepresentative N β)
      {X | X i ∈ edgeCellUnion J hJ a j ∧ ∀ k, k ≠ i → X k ∈ meshCell J hJ (η k)} =
      twoCellMixingWeight hJ η i a (nextCell J hJ a j) β •
        labelGibbsMeasure hJ (Function.update η i a) β +
      (1 - twoCellMixingWeight hJ η i a (nextCell J hJ a j) β) •
        labelGibbsMeasure hJ (Function.update η i (nextCell J hJ a j)) β := by
  exact twoCellGibbsMeasure_eq_mixture hJ hN η i (Ne.symm (nextCell_ne J hJ hJ2 a j)) hβ hsub

end PeriodicAttractiveLogGas.CellRestrictions
