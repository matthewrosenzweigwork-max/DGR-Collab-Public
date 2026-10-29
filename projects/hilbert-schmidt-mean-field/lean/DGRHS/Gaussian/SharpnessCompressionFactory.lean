import DGRHS.Gaussian.SharpnessOperatorBound
import DGRHS.Gaussian.SharpnessCommonSquare
import DGRHS.Gaussian.SharpnessDyadicFeature

noncomputable section
open MeasureTheory Set Matrix Filter BoxIntegral
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_initial_box_subset_cube (z : ι → ℝ) (q : ℝ) (hq : 0 < q) :
    WithLp.ofLp ⁻¹' (sharpnessInitialBox z q hq : Set (ι → ℝ)) ⊆ sharpnessCenteredCube z q := by
  intro x hx
  change (∀ i, z i-q ≤ x i) ∧ (∀ i, x i ≤ z i+q)
  change ∀ i, x i ∈ Ioc (z i-q) (z i+q) at hx
  exact ⟨fun i => (hx i).1.le,fun i => (hx i).2⟩

/-- One actual critical physical construction supplies its finite feature,
uniform operator cap and divergent HS square simultaneously. No favorable
cube, masses, feature, spectrum, proper moment or HS bound is an input. -/
theorem sharpness_exists_critical_compression_factory (s : ℝ) (hs : 0 < s)
    (hcrit : 2*s = (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ a : ℝ, 0 < a ∧ ∃ z : ι → ℝ, ∃ q : ℝ, ∃ hq : 0 < q, ∃ K : ℝ, 0 < K ∧
      gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (sharpnessInitialBox z q hq : Set (ι → ℝ))) ≤
        ENNReal.ofReal (1/2:ℝ) ∧
      ∀ m : ℕ, 4 ≤ m →
        let I := sharpnessInitialBox z q hq
        let μ := gaussianRieszDensityMeasure ρ
        let A := sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m)
        let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
        let κ := sharpnessCompression μ H A
        let hk := sharpnessCompression_memLp μ H A (measurableSet_sharpnessPartitionAtom ρ hρm a _)
        let k := sharpnessDyadicFeature s ρ a I m
        StronglyMeasurable k ∧ MemLp k 2 μ ∧ (∫ x,k x ∂μ) = 0 ∧
          (∀ p,inner ℝ (k p.1) (k p.2) = κ p) ∧
          (∀ x, ‖k x‖^2 ≤ sharpnessGoodDiagonalCoefficient s M a ι*((2*q)/(2:ℝ)^m)^(-s) +
            8*gaussianRieszPhysicalPotentialConstant s M ι) ∧
          ‖DGRHS.Kernel.integralOperator κ hk‖ ≤ 4*gaussianRieszPhysicalPotentialConstant s M ι ∧
          K*((m-3:ℕ):ℝ) ≤ ∫ p,κ p^2 ∂μ.prod μ := by
  have ha : 0 < (Fintype.card ι : ℝ)-s := by linarith
  obtain ⟨a,ha0,z,q,hq,K,hK,hmass,hlocal,hHS⟩ :=
    sharpness_exists_common_critical_compression s hs hcrit ρ hρm M hM hρ
  let I := sharpnessInitialBox z q hq
  have hI := (measure_mono (sharpness_initial_box_subset_cube z q hq)).trans hmass
  have hwidth : ∀ i, I.upper i-I.lower i = 2*q := by
    intro i
    dsimp [I,sharpnessInitialBox]
    ring
  refine ⟨a,ha0,z,q,hq,K,hK,hI,?_⟩
  intro m hm
  let P := sharpnessDyadicPartition I m
  let A := sharpnessPartitionAtom ρ a P
  have hf := sharpness_dyadic_feature_data s hs ha ρ hρm M hM hρ a ha0 I (2*q)
    (by positivity) hwidth hI m
  have hop := sharpness_physical_compression_operator_bound s hs ha ρ M hM hρ A
    (measurableSet_sharpnessPartitionAtom ρ hρm a P)
    (sharpnessPartitionAtom_pairwise_disjoint ρ a P)
    (sharpnessPartitionAtom_covers ρ a P)
    (fun i => ne_of_gt (sharpnessPartitionAtom_mass_pos ρ hρm a ha0 I (2*q)
      (by positivity) hwidth m hI i))
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,hop,hHS m hm⟩

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_exists_critical_compression_factory
#check @DGRHS.Gaussian.sharpness_exists_critical_compression_factory
