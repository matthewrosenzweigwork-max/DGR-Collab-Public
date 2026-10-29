import DGRHS.Gaussian.SharpnessFeatureDiagonal

noncomputable section
open MeasureTheory Set Matrix Filter BoxIntegral
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- A named actual finite feature at one physical dyadic refinement. -/
def sharpnessDyadicFeature (s : ℝ) (ρ : EuclideanSpace ℝ ι → ℝ) (a : ℝ)
    (I : Box ι) (m : ℕ) : EuclideanSpace ℝ ι →
      EuclideanSpace ℝ (sharpnessAtomIndex ρ a (sharpnessDyadicPartition I m)) :=
  let A := sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m)
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  sharpnessFiniteFeature (fun i j => sharpnessAtomAverage μ H (A i) (A j)) A

/-- The actual physical dyadic feature satisfies every finite feature input,
including proper Bochner mean zero and an EVERY-point diagonal cap. All atom
properties are derived from the geometric dyadic partition and half-mass cube. -/
theorem sharpness_dyadic_feature_data (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (I : Box ι) (L : ℝ) (hL : 0 < L) (hw : ∀ i, I.upper i-I.lower i = L)
    (hI : gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤ ENNReal.ofReal (1/2:ℝ))
    (m : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let A := sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m)
    let k := sharpnessDyadicFeature s ρ a I m
    StronglyMeasurable k ∧ MemLp k 2 μ ∧ (∫ x,k x ∂μ) = 0 ∧
      (∀ p, inner ℝ (k p.1) (k p.2) = sharpnessCompression μ H A p) ∧
      ∀ x, ‖k x‖^2 ≤ sharpnessGoodDiagonalCoefficient s M a ι*(L/(2:ℝ)^m)^(-s) +
        8*gaussianRieszPhysicalPotentialConstant s M ι := by
  let P := sharpnessDyadicPartition I m
  let A := sharpnessPartitionAtom ρ a P
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let B : Matrix (sharpnessAtomIndex ρ a P) (sharpnessAtomIndex ρ a P) ℝ :=
    fun i j => sharpnessAtomAverage μ H (A i) (A j)
  have hA := measurableSet_sharpnessPartitionAtom ρ hρm a P
  have hd := sharpnessPartitionAtom_pairwise_disjoint ρ a P
  have hc := sharpnessPartitionAtom_covers ρ a P
  have hf := sharpness_physical_finite_feature s hs ha ρ M hM hρ A hA hd hc
  have hm := sharpness_physical_finite_feature_mean s hs ha ρ M hM hρ A hA hd hc
    (sharpnessPartitionAtom_mass_pos ρ hρm a ha0 I L hL hw m hI)
  refine ⟨hf.1,hf.2.1,hm,hf.2.2,?_⟩
  intro x
  obtain ⟨i,hi⟩ := hc x
  change ‖sharpnessFiniteFeature B A x‖^2 ≤ _
  rw [sharpnessFiniteFeature_on_atom B A hd hi,
    norm_sq_sharpnessMatrixFeature B (sharpness_riesz_average_matrix_posSemidef s hs ha ρ M hM hρ A hA)]
  exact sharpness_partition_diagonal_bound s hs ha ρ hρm M hM hρ a ha0 I L hL hw hI m i

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_dyadic_feature_data
#check @DGRHS.Gaussian.sharpness_dyadic_feature_data
