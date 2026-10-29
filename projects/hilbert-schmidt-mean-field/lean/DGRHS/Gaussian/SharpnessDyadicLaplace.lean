import DGRHS.Gaussian.SharpnessFeatureWeight
import DGRHS.Gaussian.FeatureRateSourceKernel

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

/-- Quantitative finite-N Laplace theorem for the actual physical finite
compression. The feature, its proper exponential moment, zero mean, spectrum
and Gaussian field are all constructed from the same genuine partition. -/
theorem sharpness_dyadic_laplace_rate (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (I : Box ι) (L : ℝ) (hL : 0 < L) (hw : ∀ i, I.upper i-I.lower i = L)
    (hI : gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤ ENNReal.ofReal (1/2:ℝ))
    (m : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    let μ := gaussianRieszDensityMeasure ρ
    let A := sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m)
    let κ := sharpnessCompression μ (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) A
    let hk := sharpnessCompression_memLp μ _ A (measurableSet_sharpnessPartitionAtom ρ hρm a _)
    let D := sharpnessGoodDiagonalCoefficient s M a ι*(L/(2:ℝ)^m)^(-s) +
      8*gaussianRieszPhysicalPotentialConstant s M ι
    ∃ (j : Type u) (eig : j → ℝ) (e : HilbertBasis j ℝ (Lp ℝ 2 μ)),
      Countable j ∧ (∀ i, DGRHS.Kernel.integralOperator κ hk (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      (∑' i,eig i) = ∫ x, ‖sharpnessDyadicFeature s ρ a I m x‖^2 ∂μ ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic κ N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β/2*sourceKernelParticleStatistic κ N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹| ≤
          (26*β^2+12*β^3)*(Real.exp (β*D/2)*(1+D^4))^2/(N:ℝ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let P := sharpnessDyadicPartition I m
  let A := sharpnessPartitionAtom ρ a P
  let κ := sharpnessCompression μ (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) A
  let k := sharpnessDyadicFeature s ρ a I m
  let D := sharpnessGoodDiagonalCoefficient s M a ι*(L/(2:ℝ)^m)^(-s) +
    8*gaussianRieszPhysicalPotentialConstant s M ι
  have hf := sharpness_dyadic_feature_data s hs ha ρ hρm M hM hρ a ha0 I L hL hw hI m
  have hM' := sharpness_dyadic_feature_weight s hs ha ρ hρm M hM hρ a ha0 I L hL hw hI m β hβ
  have heq : κ =ᵐ[μ.prod μ] featureKernel k :=
    Eventually.of_forall (fun p => (hf.2.2.2.1 p).symm)
  obtain ⟨j,eig,e,hj,he,hn,hsum,htrace,hRate⟩ :=
    exists_sourceKernelParticleStatistic_feature_rate β hβ κ
      (sharpnessCompression_memLp μ _ A (measurableSet_sharpnessPartitionAtom ρ hρm a P))
      k hf.1 hM'.1 hf.2.2.1 heq
  refine ⟨j,eig,e,hj,he,hn,hsum,htrace,?_⟩
  intro N hN
  refine ⟨(hRate N hN).1,(hRate N hN).2.trans ?_⟩
  have hm0 : 0 ≤ ∫ x,featureExponentialMomentWeight β k x ∂μ :=
    (by norm_num : (0:ℝ) ≤ 1).trans (one_le_integral_featureExponentialMomentWeight β hβ k hM'.1)
  have hb2 := pow_le_pow_left₀ hm0 hM'.2 2
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by positivity)) hN0

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_dyadic_laplace_rate
#check @DGRHS.Gaussian.sharpness_dyadic_laplace_rate
