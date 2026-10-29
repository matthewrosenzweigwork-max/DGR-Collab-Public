import DGRHS.Gaussian.SharpnessFiniteFeature
import DGRHS.Gaussian.SharpnessPartition

noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {X α ι : Type*} [MeasurableSpace X] [Fintype α] [DecidableEq α] [Fintype ι]

omit [MeasurableSpace X] [DecidableEq α] in
lemma sharpnessAtomStep_one (A : α → Set X)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hc : ∀ x, ∃ i, x ∈ A i) :
    sharpnessAtomStep A (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  obtain ⟨i,hi⟩ := hc x
  unfold sharpnessAtomStep
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hj : x ∉ A j := fun hj => (Set.disjoint_left.mp (hd hji)) hj hi
    simp [hj]
  · simp

omit [DecidableEq α] in
lemma sharpness_sum_atom_integrals (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hiH : Integrable H (μ.prod μ))
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hc : ∀ x, ∃ i, x ∈ A i) :
    (∑ i, ∑ j, sharpnessAtomIntegral μ H (A i) (A j)) = ∫ p, H p ∂μ.prod μ := by
  have he := sharpness_atom_form_identity μ H hiH A hA (fun _ => 1)
  rw [sharpnessAtomStep_one A hd hc] at he
  simpa using he.symm

lemma integral_sharpnessFiniteFeature_eq_zero (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hiH : Integrable H (μ.prod μ))
    (hH0 : (∫ p, H p ∂μ.prod μ) = 0)
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hc : ∀ x, ∃ i, x ∈ A i)
    (hm : ∀ i, (μ (A i)).toReal ≠ 0)
    (hB : Matrix.PosSemidef (fun (i j : α) => sharpnessAtomAverage μ H (A i) (A j))) :
    (∫ x, sharpnessFiniteFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) A x ∂μ) = 0 := by
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  change (∫ x, sharpnessFiniteFeature B A x ∂μ) = 0
  rw [integral_sharpnessFiniteFeature μ B A hA]
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    inner_sharpnessMatrixFeature B hB]
  have he (i j : α) : (μ (A i)).toReal*((μ (A j)).toReal*B i j) =
      sharpnessAtomIntegral μ H (A i) (A j) := by
    dsimp [B,sharpnessAtomAverage]
    field_simp [hm i,hm j]
  have hsym (i j : α) : sharpnessAtomAverage μ H (A j) (A i) = sharpnessAtomAverage μ H (A i) (A j) := by
    have ht := congrArg (fun D : Matrix α α ℝ => D i j) hB.isHermitian.eq
    change star (sharpnessAtomAverage μ H (A j) (A i)) = sharpnessAtomAverage μ H (A i) (A j) at ht
    simpa only [star_trivial] using ht
  dsimp only [B] at he ⊢
  calc
    _ = ∑ i, ∑ j, sharpnessAtomIntegral μ H (A i) (A j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym i j]
      convert he i j using 1 <;> ring
    _ = 0 := by rw [sharpness_sum_atom_integrals μ H hiH A hA hd hc,hH0]

lemma integral_sharpness_centered_riesz_eq_zero (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) = 0 := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
  have hW := sharpness_riesz_pair_integrable s hs ha ρ M hM hρ
  have hH := sharpness_centered_riesz_integrable s hs ha ρ M hM hρ
  rw [integral_prod _ hH]
  have he : (fun x => ∫ y, hoeffdingCentered μ (gaussianRieszPhysicalPair s) (x,y) ∂μ) =ᵐ[μ]
      (fun _ => 0) := DGRHS.integral_centeredKernel_right μ W hW
  rw [integral_congr_ae he]
  simp

/-- Genuine zero Bochner mean of the same finite matrix-root feature. -/
theorem sharpness_physical_finite_feature_mean (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A : α → Set (EuclideanSpace ℝ ι)) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hc : ∀ x, ∃ i, x ∈ A i)
    (hm : ∀ i, 0 < (gaussianRieszDensityMeasure ρ (A i)).toReal) :
    (∫ x, sharpnessFiniteFeature (fun i j => sharpnessAtomAverage (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) (A i) (A j)) A x
      ∂gaussianRieszDensityMeasure ρ) = 0 := by
  exact integral_sharpnessFiniteFeature_eq_zero _ _
    (sharpness_centered_riesz_integrable s hs ha ρ M hM hρ)
    (integral_sharpness_centered_riesz_eq_zero s hs ha ρ M hM hρ)
    A hA hd hc (fun i => ne_of_gt (hm i))
    (sharpness_riesz_average_matrix_posSemidef s hs ha ρ M hM hρ A hA)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_physical_finite_feature_mean
#check @DGRHS.Gaussian.sharpness_physical_finite_feature_mean
