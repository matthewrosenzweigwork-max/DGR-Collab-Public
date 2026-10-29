import DGRHS.Gaussian.SharpnessFiniteFeatureMean

noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {X α ι : Type*} [MeasurableSpace X] [Fintype α] [DecidableEq α] [Fintype ι]

lemma sharpness_weighted_feature_norm_sq (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (A : α → Set X) (hm : ∀ i, (μ (A i)).toReal ≠ 0)
    (hB : Matrix.PosSemidef (fun (i j : α) => sharpnessAtomAverage μ H (A i) (A j)))
    (z : α → ℝ) :
    ‖∑ i, ((μ (A i)).toReal*z i) •
      sharpnessMatrixFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) i‖^2 =
      ∑ i, ∑ j,z i*z j*sharpnessAtomIntegral μ H (A i) (A j) := by
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  change ‖∑ i, ((μ (A i)).toReal*z i) • sharpnessMatrixFeature B i‖^2 = _
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    inner_sharpnessMatrixFeature B hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [B,sharpnessAtomAverage]
  field_simp [hm i,hm j]
  <;> ring

/-- Actual scale-independent weighted synthesis bound, derived from the
full singular physical Schur form and its true matrix-root Gram vectors. -/
theorem sharpness_physical_weighted_feature_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A : α → Set (EuclideanSpace ℝ ι)) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hm : ∀ i, (gaussianRieszDensityMeasure ρ (A i)).toReal ≠ 0) (z : α → ℝ) :
    let μ := gaussianRieszDensityMeasure ρ
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    ‖∑ i, ((μ (A i)).toReal*z i) •
      sharpnessMatrixFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) i‖^2 ≤
      (4*gaussianRieszPhysicalPotentialConstant s M ι)*∑ i,(z i)^2*(μ (A i)).toReal := by
  dsimp only
  rw [sharpness_weighted_feature_norm_sq _ _ A hm
    (sharpness_riesz_average_matrix_posSemidef s hs ha ρ M hM hρ A hA)]
  exact (le_abs_self _).trans (sharpness_finite_atom_form_le s hs ha ρ M hM hρ A hA hd z)

/-- Actual finite-feature weak variance. Its uniform constant is supplied by
physical rows, not by a presumed operator norm or variance conclusion. -/
theorem sharpness_physical_feature_weak_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A : α → Set (EuclideanSpace ℝ ι)) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hm : ∀ i, (gaussianRieszDensityMeasure ρ (A i)).toReal ≠ 0)
    (v : EuclideanSpace ℝ α) :
    let μ := gaussianRieszDensityMeasure ρ
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    (∑ i, (inner ℝ (sharpnessMatrixFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) i) v)^2*
      (μ (A i)).toReal) ≤ (4*gaussianRieszPhysicalPotentialConstant s M ι)*‖v‖^2 := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  let z := fun i => inner ℝ (sharpnessMatrixFeature B i) v
  let q := ∑ i,(z i)^2*(μ (A i)).toReal
  let w := ∑ i,((μ (A i)).toReal*z i) • sharpnessMatrixFeature B i
  let L := 4*gaussianRieszPhysicalPotentialConstant s M ι
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
  have hform : ‖w‖^2 ≤ L*q := sharpness_physical_weighted_feature_bound s hs ha ρ M hM hρ A hA hd hm z
  have he : inner ℝ w v = q := by
    dsimp only [w,q,z]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left]
    ring
  have hcs : |q| ≤ ‖w‖*‖v‖ := by
    rw [← he]
    exact abs_real_inner_le_norm w v
  have hcs2 : q^2 ≤ ‖w‖^2*‖v‖^2 := by
    rw [abs_of_nonneg hq] at hcs
    nlinarith [mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg (by positivity : 0 ≤ ‖w‖*‖v‖) hq)]
  have hmul := mul_le_mul_of_nonneg_right hform (sq_nonneg ‖v‖)
  change q ≤ L*‖v‖^2
  by_cases hz : q = 0
  · rw [hz]
    have hL : 0 ≤ L := by
      exact mul_nonneg (by norm_num) (((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
        (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2)
    positivity
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    nlinarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_physical_weighted_feature_bound
#print axioms DGRHS.Gaussian.sharpness_physical_feature_weak_bound
#check @DGRHS.Gaussian.sharpness_physical_feature_weak_bound
