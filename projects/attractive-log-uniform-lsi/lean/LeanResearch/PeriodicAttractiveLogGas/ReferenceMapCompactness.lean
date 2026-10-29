import LeanResearch.PeriodicAttractiveLogGas.ReferenceConvolutionGradient
import LeanResearch.PeriodicAttractiveLogGas.ReferenceDensityDomain
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Relative compactness of the actual reference map, corresponding to the
Arzelà--Ascoli step at source lines 2386--2391. The representatives below are
defined on the whole compact torus. Their bounds depend on the fixed mesh
and inverse temperature, but not on the input family, occupation, or particle
number. Sharp invariance and fixed-point existence are separate statements.
See the development note for the exact verification status.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ReferenceMapCompactness

open MeshCells LabelOccupations ReferenceResidual ReferenceSelfTerms
  ReferencePotentialBounds ReferenceDensityChange ReferenceConvolutionContinuity

/-- Comparison of the attained Euclidean lift with the existing product norm. -/
theorem norm_centeredLift_le (z : Torus) :
    ‖centeredLift z‖ ≤ Real.sqrt 2 * ‖z‖ := by
  apply MeshNearbyGeometry.euclidean_norm_le_sqrt_two_mul (norm_nonneg z)
  intro k
  rw [← Real.norm_eq_abs, norm_centeredLift_apply]
  exact norm_le_pi_norm z k

/-- A physical-lift Lipschitz estimate descends to the unchanged torus metric.
The factor `sqrt 2` accounts for its product norm. -/
theorem lipschitzWith_of_physical_lift {F : Torus → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K (fun x : PlanarSpace => F (torusQuotient x))) :
    LipschitzWith ⟨(K : ℝ) * Real.sqrt 2, by positivity⟩ F := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have hh := lipschitzWith_iff_norm_sub_le.mp hF
    (centeredLift (x - y) + centeredLift y) (centeredLift y)
  simp only [torusQuotient_add, torusQuotient_centeredLift, sub_add_cancel,
    add_sub_cancel_right] at hh
  exact hh.trans (by
    change (K : ℝ) * ‖centeredLift (x - y)‖ ≤
      ((K : ℝ) * Real.sqrt 2) * ‖x - y‖
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (norm_centeredLift_le (x - y)) K.coe_nonneg)

/-- A non-sharp bound at the fixed radius `1/2`, sufficient for compactness. -/
def potentialLipschitzConstant (J : ℕ) : ℝ :=
  ConditionalLawEstimates.kernelConstant *
    (2 * Real.pi * (Real.exp 1 * (J : ℝ)^2) * (1 / 2) + (1 / 2 : ℝ)⁻¹) *
      Real.sqrt 2

theorem potentialLipschitzConstant_nonneg (J : ℕ) :
    0 ≤ potentialLipschitzConstant J := by
  unfold potentialLipschitzConstant
  have := ConditionalLawEstimates.kernelConstant_pos
  positivity

theorem family_potential_lipschitz {J : ℕ} {hJ : 0 < J}
    (φ : DensityFamily hJ) (a : MeshIndex J) :
    LipschitzWith ⟨potentialLipschitzConstant J, potentialLipschitzConstant_nonneg J⟩
      (potential (familyMeasures φ a)) := by
  have hh := ReferenceConvolutionGradient.lipschitzWith_potential
    (B := Real.exp 1 * (J : ℝ)^2) (s := (1 / 2 : ℝ)) (by positivity)
    (reference_le_haar hJ a (familyMeasures φ a) (φ a).law_le)
    ConditionalLawEstimates.kernelConstant_pos.le ConditionalLawEstimates.kernel_gradient_bound
    (by norm_num) le_rfl
  exact lipschitzWith_of_physical_lift hh

/-- Averaging uses the original positive particle count; its factor cancels
the number of summands without any exchangeability or occupancy hypothesis. -/
theorem averagePotential_lipschitz {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) (φ : DensityFamily hJ) :
    LipschitzWith ⟨potentialLipschitzConstant J, potentialLipschitzConstant_nonneg J⟩
      (averagePotential (familyMeasures φ) η) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  change |averagePotential (familyMeasures φ) η x -
    averagePotential (familyMeasures φ) η y| ≤ potentialLipschitzConstant J * ‖x - y‖
  rw [averagePotential, averagePotential, ← sub_div, ← Finset.sum_sub_distrib,
    abs_div, abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  calc
    |∑ i, (potential (familyMeasures φ (η i)) x - potential (familyMeasures φ (η i)) y)| ≤
        ∑ i, |potential (familyMeasures φ (η i)) x - potential (familyMeasures φ (η i)) y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, potentialLipschitzConstant J * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact lipschitzWith_iff_norm_sub_le.mp (family_potential_lipschitz φ (η i)) x y
    _ = _ := by simp [mul_comm]

private theorem exp_sub_le (a b : ℝ) :
    Real.exp a - Real.exp b ≤ Real.exp a * (a - b) := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b - a)) (Real.exp_pos a).le
  have he : Real.exp a * Real.exp (b - a) = Real.exp b := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  nlinarith

/-- A two-sided exponential difference bound using only an upper bound on
the two arguments. -/
theorem abs_exp_sub_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  rcases le_total b a with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact (exp_sub_le a b).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (sub_nonneg.mpr hba))
  · rw [abs_sub_comm (Real.exp a), abs_sub_comm a,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact (exp_sub_le b a).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) (sub_nonneg.mpr hab))

def densityBound (J : ℕ) (β : ℝ) : ℝ :=
  Real.exp (β * globalPotentialBound J) / Real.exp (-β * globalPotentialBound J)

theorem densityBound_pos (J : ℕ) (β : ℝ) : 0 < densityBound J β :=
  div_pos (Real.exp_pos _) (Real.exp_pos _)

def densityLipschitzConstant (J : ℕ) (β : ℝ) : ℝ :=
  densityBound J β * β * potentialLipschitzConstant J

theorem densityLipschitzConstant_nonneg (J : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ densityLipschitzConstant J β :=
  mul_nonneg (mul_nonneg (densityBound_pos J β).le hβ) (potentialLipschitzConstant_nonneg J)

/-- Every actual normalized density has a uniformly Lipschitz representative
on the whole torus, including cells unoccupied by the label vector. -/
theorem referenceMapValue_lipschitz {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) :
    LipschitzWith ⟨densityLipschitzConstant J β, densityLipschitzConstant_nonneg J hβ⟩
      (referenceMapValue η β φ a) := by
  let M : ℝ := β * globalPotentialBound J
  let Z : ℝ := cellNormalizer hJ (familyMeasures φ) η β a
  have hh := reference_exponential_normalizer hJ hN (familyMeasures φ)
    (fun a => (φ a).law_le) η hβ (meshCellMeasure J hJ a)
  have hZ : 0 < Z := hh.2.2.1
  have hZlo : Real.exp (-M) ≤ Z := by
    simpa only [M, Z, cellNormalizer, neg_mul] using hh.2.2.2.1
  have hU (x : Torus) : β * averagePotential (familyMeasures φ) η x ≤ M :=
    mul_le_mul_of_nonneg_left (abs_le.mp (family_averagePotential_bound hN η φ x)).2 hβ
  have hC : 0 ≤ potentialLipschitzConstant J := potentialLipschitzConstant_nonneg J
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have hL := lipschitzWith_iff_norm_sub_le.mp (averagePotential_lipschitz hN η φ) x y
  change |referenceMapValue η β φ a x - referenceMapValue η β φ a y| ≤
    densityLipschitzConstant J β * ‖x - y‖
  change |Real.exp (β * averagePotential (familyMeasures φ) η x) / Z -
    Real.exp (β * averagePotential (familyMeasures φ) η y) / Z| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hZ]
  calc
    _ ≤ (Real.exp M * |β * averagePotential (familyMeasures φ) η x -
        β * averagePotential (familyMeasures φ) η y|) / Z :=
      div_le_div_of_nonneg_right (abs_exp_sub_le (hU x) (hU y)) hZ.le
    _ ≤ (Real.exp M * (β * (potentialLipschitzConstant J * ‖x - y‖))) / Z := by
      apply div_le_div_of_nonneg_right _ hZ.le
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos M).le
      rw [← mul_sub, abs_mul, abs_of_nonneg hβ]
      exact mul_le_mul_of_nonneg_left hL hβ
    _ ≤ (Real.exp M * (β * (potentialLipschitzConstant J * ‖x - y‖))) /
        Real.exp (-M) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hZlo
    _ = _ := by
      unfold densityLipschitzConstant densityBound
      dsimp [M]
      rw [neg_mul]
      ring

/-- The bounded continuous function is the actual normalized exponential,
not a new choice of an AE representative. -/
def referenceRepresentative {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) : BoundedContinuousFunction Torus ℝ :=
  ContinuousMap.linearIsometryBoundedOfCompact Torus ℝ ℝ
    ⟨referenceMapValue η β φ a, (referenceMapValue_lipschitz hN η hβ φ a).continuous⟩

@[simp] theorem referenceRepresentative_apply {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) (x : Torus) :
    referenceRepresentative hN η hβ φ a x = referenceMapValue η β φ a x := rfl

/-- Arzelà--Ascoli with explicitly uniform boundedness and Lipschitz inputs.
The topology on bounded continuous functions is uniform convergence. -/
theorem isCompact_closure_lipschitz_range {α ι : Type*}
    [PseudoMetricSpace α] [CompactSpace α] (f : ι → BoundedContinuousFunction α ℝ)
    {K : ℝ≥0} {M : ℝ} (hbound : ∀ i x, |f i x| ≤ M)
    (hlip : ∀ i, LipschitzWith K (f i)) :
    IsCompact (closure (Set.range f)) := by
  apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-M) M) isCompact_Icc
  · rintro g x ⟨i, rfl⟩
    exact abs_le.mp (hbound i x)
  · apply (LipschitzWith.uniformEquicontinuous
      (fun g : Set.range f => (g.val : α → ℝ)) K ?_).equicontinuous
    rintro ⟨g, i, rfl⟩
    exact hlip i

/-- The actual representatives have compact closure in the uniform topology,
simultaneously for all admissible input families at a fixed output cell. -/
theorem isCompact_closure_representative_range {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (a : MeshIndex J) :
    IsCompact (closure (Set.range
      (fun φ : DensityFamily hJ => referenceRepresentative hN η hβ φ a))) := by
  apply isCompact_closure_lipschitz_range
    (K := ⟨densityLipschitzConstant J β, densityLipschitzConstant_nonneg J hβ⟩)
    (M := densityBound J β)
  · intro φ x
    exact (referenceMapValue_bound hN η hβ φ a x).2
  · intro φ
    exact referenceMapValue_lipschitz hN η hβ φ a

/-- The continuous map into the genuine normalized-cell L1 space produces
exactly the released output class. No full-support property of the cell law
on the whole torus is used. -/
theorem referenceRepresentative_toLp {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) :
    BoundedContinuousFunction.toLp 1 (meshCellMeasure J hJ a) ℝ
      (referenceRepresentative hN η hβ φ a) = referenceMap hN η hβ φ a := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 1 (meshCellMeasure J hJ a) ℝ
      (referenceRepresentative hN η hβ φ a),
    (referenceMapValue_memLp hN η hβ φ a).coeFn_toLp] with x hx hy
  simp only [referenceMap, hx, hy, referenceRepresentative_apply]

/-- A concrete compact envelope in the actual cell L1 space. -/
def cellCompactSet {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (a : MeshIndex J) :
    Set (Lp ℝ 1 (meshCellMeasure J hJ a)) :=
  BoundedContinuousFunction.toLp 1 (meshCellMeasure J hJ a) ℝ ''
    closure (Set.range (fun φ : DensityFamily hJ => referenceRepresentative hN η hβ φ a))

theorem cellCompactSet_isCompact {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (a : MeshIndex J) :
    IsCompact (cellCompactSet (hJ := hJ) hN η hβ a) :=
  (isCompact_closure_representative_range hN η hβ a).image
    (BoundedContinuousFunction.toLp 1 (meshCellMeasure J hJ a) ℝ).continuous

theorem referenceMap_mem_cellCompactSet {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (φ : DensityFamily hJ)
    (a : MeshIndex J) : referenceMap hN η hβ φ a ∈ cellCompactSet hN η hβ a :=
  ⟨referenceRepresentative hN η hβ φ a, subset_closure ⟨φ, rfl⟩,
    referenceRepresentative_toLp hN η hβ φ a⟩

/-- Relative compactness of the actual reference map in the existing finite
product of normalized-cell L1 spaces. The constants used above depend only
on `J` and `beta`; no particle count, occupation, or density is fixed inside
an assumed compactness or regularity premise. -/
theorem isCompact_closure_referenceMap_range {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) :
    IsCompact (closure (Set.range (referenceMap hN η hβ :
      DensityFamily hJ → ReferenceDensityDomain.Ambient hJ))) := by
  have hcompact : IsCompact (Set.pi Set.univ (cellCompactSet (hJ := hJ) hN η hβ)) :=
    isCompact_univ_pi fun a => cellCompactSet_isCompact (hJ := hJ) hN η hβ a
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  rintro f ⟨φ, rfl⟩ a _
  exact referenceMap_mem_cellCompactSet hN η hβ φ a

/-- The same conclusion when the input is written as the literal closed
convex domain in the ambient L1 product, using its released homeomorphism. -/
theorem isCompact_closure_referenceMap_domain {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) :
    IsCompact (closure (Set.range (fun φ : ↥(ReferenceDensityDomain.admissibleDomain hJ) =>
      referenceMap hN η hβ ((ReferenceDensityDomain.familyHomeomorph hJ).symm φ)))) := by
  have hrange : Set.range (fun φ : ↥(ReferenceDensityDomain.admissibleDomain hJ) =>
      referenceMap hN η hβ ((ReferenceDensityDomain.familyHomeomorph hJ).symm φ)) =
      Set.range (referenceMap hN η hβ : DensityFamily hJ → ReferenceDensityDomain.Ambient hJ) := by
    ext f
    constructor
    · rintro ⟨φ, rfl⟩
      exact ⟨(ReferenceDensityDomain.familyHomeomorph hJ).symm φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      refine ⟨ReferenceDensityDomain.familyHomeomorph hJ φ, ?_⟩
      simp only [Homeomorph.symm_apply_apply]
  rw [hrange]
  exact isCompact_closure_referenceMap_range hN η hβ

end PeriodicAttractiveLogGas.ReferenceMapCompactness
