import DGRHS.Attractive.SignedFeatureJointMoments

/-! The actual separable source field retains the same-process fiber witness
and genuine Gaussian section law, in addition to the exact particle identities.
These outputs allow all later moments and spectral laws to refer to one field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u v
variable {H : Type v} {X : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

theorem exists_separable_positiveFeature_fibers
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ) (hmean : (∫ x, k x ∂μ) = 0)
    (hp : ∀ N : ℕ, 1 ≤ N → Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ))) :
    ∃ (j : Type v) (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
      (g : X × (ℕ → ℝ) → ℝ), Countable j ∧ StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ,(fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      (∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω))
        (gaussianReal 0 (Real.toNNReal (‖k x‖^2))) IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x,ω)) μ) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x,ω) ∂μ) = 0) ∧
      ∀ N : ℕ, 1 ≤ N →
        (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
          Integrable (fun x => positiveFeatureWick β k g N (x,ω)) μ ∧
          0 < positiveFeatureFactor μ β k g N ω) ∧
        Integrable (positiveFeatureFactor μ β k g N) IsonormalProcess.iidStdGaussian ∧
        (∫ ω, positiveFeatureFactor μ β k g N ω ∂IsonormalProcess.iidStdGaussian) = 1 ∧
        Integrable (fun ω => positiveFeatureFactor μ β k g N ω ^ N)
          IsonormalProcess.iidStdGaussian ∧
        (∫ x, positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ)) =
          (∫ ω, positiveFeatureFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian) ∧
        Integrable (fun ω => positiveFeatureFactor μ β k g N ω ^ (2*N))
          IsonormalProcess.iidStdGaussian ∧
        (∫ ω, positiveFeatureFactor μ β k g N ω ^ (2*N) ∂IsonormalProcess.iidStdGaussian) =
          (∫ x, positiveFeatureParticleExp (2*β) k (2*N) x
            ∂Measure.pi (fun _ : Fin (2*N) => μ)) := by
  classical
  have hk2 := feature_memLp_two_of_diagonal_exponential k hk a ha hM
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℝ H
  letI : Countable s := HilbertBasis.countable_of_separable_index b
  let f : s ↪ ℕ := countableGaussianIndex
  obtain ⟨g, hg, hg2, hW, hG, hI, hC⟩ :=
    exists_centered_featureGaussian_representative b f f.injective hk.measurable hk2 hmean
  refine ⟨s,b,f,f.injective,g,inferInstance,hg,hg2,hW,ae_feature_gaussian_law b f f.injective k g hW,hI,hC,?_⟩
  intro N hN
  have hhalf := integrable_positiveFeatureParticleExp_of_doubled β k hk N (hp N hN)
  obtain ⟨hi, he⟩ := positiveFeature_linearization b f f.injective β hβ k hk g hg hW N hhalf
  obtain ⟨hi2, he2⟩ := positiveFeature_doubled_linearization b f f.injective β hβ
    k hk g hg hW N (hp (2*N) (by omega))
  obtain ⟨hpos, hia, hma⟩ := positiveFeatureFactor_proper_positive_mean b f f.injective
    β hβ k hk g hg hW N
  exact ⟨hpos, hia, hma, hi, he, hi2, he2⟩

end DGRHS.Attractive
#check DGRHS.Attractive.exists_separable_positiveFeature_fibers
#print axioms DGRHS.Attractive.exists_separable_positiveFeature_fibers
