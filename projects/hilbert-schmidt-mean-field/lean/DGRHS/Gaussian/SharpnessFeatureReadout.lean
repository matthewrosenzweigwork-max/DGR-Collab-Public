import DGRHS.Gaussian.SharpnessWeightedFeature
import DGRHS.Gaussian.FeatureKernel

noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {X α ι : Type*} [MeasurableSpace X] [Fintype α] [DecidableEq α] [Fintype ι]

lemma sharpnessFiniteFeature_readout (B : Matrix α α ℝ) (A : α → Set X)
    (v : EuclideanSpace ℝ α) (x : X) :
    inner ℝ (sharpnessFiniteFeature B A x) v =
      sharpnessAtomStep A (fun i => inner ℝ (sharpnessMatrixFeature B i) v) x := by
  unfold sharpnessFiniteFeature sharpnessAtomStep
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ A i <;> simp [hx]

lemma norm_sharpness_featureReadout_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (B : Matrix α α ℝ) (A : α → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (v : EuclideanSpace ℝ α) :
    ‖featureReadout (sharpnessFiniteFeature B A) (sharpnessFiniteFeature_memLp μ B A hA) v‖^2 =
      ∑ i,(inner ℝ (sharpnessMatrixFeature B i) v)^2*(μ (A i)).toReal := by
  calc
    _ = ∫ x,(inner ℝ (sharpnessFiniteFeature B A x) v)^2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq,inner_featureReadout_apply_apply]
      congr 1
      funext x
      ring
    _ = ∫ x,(sharpnessAtomStep A (fun i => inner ℝ (sharpnessMatrixFeature B i) v) x)^2 ∂μ := by
      congr 1
      funext x
      rw [sharpnessFiniteFeature_readout]
    _ = _ := sharpness_atom_step_sq_integral μ A hA hd _

/-- The actual finite readout has a scale-independent squared norm bound
from singular physical rows. This is the needed operator-bound input. -/
theorem sharpness_physical_featureReadout_sq_bound (s : ℝ) (hs : 0 < s)
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
    let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
    ‖featureReadout (sharpnessFiniteFeature B A) (sharpnessFiniteFeature_memLp μ B A hA) v‖^2 ≤
      (4*gaussianRieszPhysicalPotentialConstant s M ι)*‖v‖^2 := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  change ‖featureReadout (sharpnessFiniteFeature B A) (sharpnessFiniteFeature_memLp μ B A hA) v‖^2 ≤ _
  rw [norm_sharpness_featureReadout_sq μ B A hA hd]
  exact sharpness_physical_feature_weak_bound s hs ha ρ M hM hρ A hA hd hm v

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_physical_featureReadout_sq_bound
#check @DGRHS.Gaussian.sharpness_physical_featureReadout_sq_bound
