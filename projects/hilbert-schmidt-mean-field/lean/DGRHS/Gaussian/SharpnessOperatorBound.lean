import DGRHS.Gaussian.SharpnessFeatureReadout
import DGRHS.Gaussian.FeatureRateSourceKernel

noncomputable section
open MeasureTheory Set Matrix Filter
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

lemma sharpness_feature_operator_norm_of_readout (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ v, ‖featureReadout k hk2 v‖^2 ≤ L*‖v‖^2) :
    ‖DGRHS.Kernel.integralOperator (featureKernel k) (memLp_featureKernel k hk hk2)‖ ≤ L := by
  let R := featureReadout k hk2
  have hR : ‖R‖ ≤ Real.sqrt L := by
    apply R.opNorm_le_bound (Real.sqrt_nonneg L)
    intro v
    have hsq : ‖R v‖^2 ≤ (Real.sqrt L*‖v‖)^2 := by
      rw [mul_pow,Real.sq_sqrt hL]
      exact hb v
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  rw [integralOperator_featureKernel_eq k hk hk2]
  change ‖R.comp R.adjoint‖ ≤ L
  calc
    _ ≤ ‖R‖*‖R.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖R‖^2 := by rw [LinearIsometryEquiv.norm_map]; ring
    _ ≤ (Real.sqrt L)^2 := pow_le_pow_left₀ (norm_nonneg R) hR 2
    _ = L := Real.sq_sqrt hL

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
/-- Uniform actual finite-compression operator bound throughout 0<s<d.
The full singular physical kernel is never passed to an L2 operator factory. -/
theorem sharpness_physical_compression_operator_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A : α → Set (EuclideanSpace ℝ ι)) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hc : ∀ x, ∃ i, x ∈ A i)
    (hm : ∀ i, (gaussianRieszDensityMeasure ρ (A i)).toReal ≠ 0) :
    let μ := gaussianRieszDensityMeasure ρ
    let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let κ := sharpnessCompression μ H A
    ‖DGRHS.Kernel.integralOperator κ (sharpnessCompression_memLp μ H A hA)‖ ≤
      4*gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  let k := sharpnessFiniteFeature B A
  let hk := stronglyMeasurable_sharpnessFiniteFeature B A hA
  let hk2 := sharpnessFiniteFeature_memLp μ B A hA
  let L := 4*gaussianRieszPhysicalPotentialConstant s M ι
  have hL : 0 ≤ L := mul_nonneg (by norm_num)
    (((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
      (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2)
  have hn := sharpness_feature_operator_norm_of_readout k hk hk2 L hL
    (sharpness_physical_featureReadout_sq_bound s hs ha ρ M hM hρ A hA hd hm)
  have heq : sharpnessCompression μ H A =ᵐ[μ.prod μ] featureKernel k :=
    Eventually.of_forall (fun p =>
      (sharpnessFiniteFeature_gram μ H A
        (sharpness_riesz_average_matrix_posSemidef s hs ha ρ M hM hρ A hA) hd hc p).symm)
  have hop := integralOperator_eq_of_ae_kernel (sharpnessCompression_memLp μ H A hA)
    (memLp_featureKernel k hk hk2) heq
  dsimp only
  rw [hop]
  exact hn

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_physical_compression_operator_bound
#check @DGRHS.Gaussian.sharpness_physical_compression_operator_bound
