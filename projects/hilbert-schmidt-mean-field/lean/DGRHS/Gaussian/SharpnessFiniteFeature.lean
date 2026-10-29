import DGRHS.Gaussian.SharpnessFiniteGram

noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {X α ι : Type*} [MeasurableSpace X] [Fintype α] [DecidableEq α] [Fintype ι]

/-- The actual finite feature is the corresponding matrix-root column on
its partition atom. It is defined everywhere, including the remainder. -/
def sharpnessFiniteFeature (B : Matrix α α ℝ) (A : α → Set X) (x : X) :
    EuclideanSpace ℝ α := ∑ i, (A i).indicator (fun _ => sharpnessMatrixFeature B i) x

lemma stronglyMeasurable_sharpnessFiniteFeature (B : Matrix α α ℝ) (A : α → Set X)
    (hA : ∀ i, MeasurableSet (A i)) : StronglyMeasurable (sharpnessFiniteFeature B A) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact stronglyMeasurable_const.indicator (hA i)

omit [MeasurableSpace X] in
lemma norm_sharpnessFiniteFeature_le (B : Matrix α α ℝ) (A : α → Set X) (x : X) :
    ‖sharpnessFiniteFeature B A x‖ ≤ ∑ i, ‖sharpnessMatrixFeature B i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x ∈ A i <;> simp [hx]

lemma sharpnessFiniteFeature_memLp (μ : Measure X) [IsFiniteMeasure μ]
    (B : Matrix α α ℝ) (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (sharpnessFiniteFeature B A) 2 μ := by
  let K := ∑ i, ‖sharpnessMatrixFeature B i‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact (memLp_const K).of_le
    (stronglyMeasurable_sharpnessFiniteFeature B A hA).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_of_nonneg hK] using norm_sharpnessFiniteFeature_le B A x)

omit [MeasurableSpace X] in
lemma sharpnessFiniteFeature_on_atom (B : Matrix α α ℝ) (A : α → Set X)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) {i : α} {x : X} (hx : x ∈ A i) :
    sharpnessFiniteFeature B A x = sharpnessMatrixFeature B i := by
  unfold sharpnessFiniteFeature
  rw [Finset.sum_eq_single i]
  · simp [hx]
  · intro j _ hji
    have hj : x ∉ A j := fun hj => (Set.disjoint_left.mp (hd hji)) hj hx
    simp [hj]
  · simp

lemma integral_sharpnessFiniteFeature (μ : Measure X) [IsFiniteMeasure μ]
    (B : Matrix α α ℝ) (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    (∫ x, sharpnessFiniteFeature B A x ∂μ) =
      ∑ i, (μ (A i)).toReal • sharpnessMatrixFeature B i := by
  unfold sharpnessFiniteFeature
  rw [integral_finsetSum _ (fun i _ => (integrable_const _).indicator (hA i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_indicator_const _ (hA i)

lemma sharpnessFiniteFeature_gram (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (A : α → Set X)
    (hB : Matrix.PosSemidef (fun (i j : α) => sharpnessAtomAverage μ H (A i) (A j)))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hc : ∀ x, ∃ i, x ∈ A i) (p : X × X) :
    inner ℝ (sharpnessFiniteFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) A p.1)
      (sharpnessFiniteFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) A p.2) =
      sharpnessCompression μ H A p := by
  obtain ⟨i,hi⟩ := hc p.1
  obtain ⟨j,hj⟩ := hc p.2
  rcases p with ⟨x,y⟩
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  change inner ℝ (sharpnessFiniteFeature B A x) (sharpnessFiniteFeature B A y) = _
  rw [sharpnessFiniteFeature_on_atom B A hd hi, sharpnessFiniteFeature_on_atom B A hd hj,
    inner_sharpnessMatrixFeature B hB]
  exact (sharpnessCompression_on_atom μ H A hd hi hj).symm

/-- Actual finite-dimensional Gram realization of the physical singular
Riesz compression. Positivity, measurability and L2 properness are derived;
the full singular physical kernel is required only in L1. -/
theorem sharpness_physical_finite_feature (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A : α → Set (EuclideanSpace ℝ ι)) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hc : ∀ x, ∃ i, x ∈ A i) :
    let μ := gaussianRieszDensityMeasure ρ
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let k := sharpnessFiniteFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) A
    StronglyMeasurable k ∧ MemLp k 2 μ ∧
      ∀ p, inner ℝ (k p.1) (k p.2) = sharpnessCompression μ H A p := by
  refine ⟨stronglyMeasurable_sharpnessFiniteFeature _ A hA,
    sharpnessFiniteFeature_memLp _ _ A hA, ?_⟩
  exact sharpnessFiniteFeature_gram _ _ A
    (sharpness_riesz_average_matrix_posSemidef s hs ha ρ M hM hρ A hA) hd hc

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.integral_sharpnessFiniteFeature
#print axioms DGRHS.Gaussian.sharpness_physical_finite_feature
#check @DGRHS.Gaussian.sharpness_physical_finite_feature
