import DGRHS.Attractive.SignedFeatureWickProper
import DGRHS.Gaussian.SeparableFeatureEvaluation
import DGRHS.Gaussian.FeatureRatePhysical

/-! Actual separable centered feature construction for the positive-sign
linearization. The Gaussian field is constructed; neither its existence nor
its finite-particle Laplace identity is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

lemma positiveFeatureParticleExp_eq_source (β : ℝ) (k : X → H)
    (N : ℕ) (x : Fin N → X) :
    positiveFeatureParticleExp β k N x = Real.exp
      (β / (2*(N:ℝ)) * ∑ i : Fin N, ∑ j : Fin N,
        if i = j then 0 else inner ℝ (k (x i)) (k (x j))) := by
  rw [feature_particle_off_diagonal_sum]
  rfl

/-- The genuine source doubled positive particle weights give a constructed
isonormal field and both proper Gaussian power identities, for every N>=1.
No rate inequality, Gaussian-field premise, trace-class assumption or
compact-support restriction is introduced. -/
theorem exists_separable_positiveFeature_linearization
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (hmean : (∫ x, k x ∂μ) = 0)
    (hp : ∀ N : ℕ, 1 ≤ N → Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ))) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
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
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℝ H
  letI : Countable s := HilbertBasis.countable_of_separable_index b
  let f : s ↪ ℕ := countableGaussianIndex
  obtain ⟨g, hg, hg2, hW, hG, hI, hC⟩ :=
    exists_centered_featureGaussian_representative b f f.injective hk.measurable hk2 hmean
  refine ⟨g, hg, hg2, hI, hC, ?_⟩
  intro N hN
  have hhalf := integrable_positiveFeatureParticleExp_of_doubled β k hk N (hp N hN)
  obtain ⟨hi, he⟩ := positiveFeature_linearization b f f.injective β hβ k hk g hg hW N hhalf
  obtain ⟨hi2, he2⟩ := positiveFeature_doubled_linearization b f f.injective β hβ
    k hk g hg hW N (hp (2*N) (by omega))
  obtain ⟨hpos, hia, hma⟩ := positiveFeatureFactor_proper_positive_mean b f f.injective
    β hβ k hk g hg hW N
  exact ⟨hpos, hia, hma, hi, he, hi2, he2⟩

end DGRHS.Attractive
#check DGRHS.Attractive.positiveFeatureParticleExp_eq_source
#print axioms DGRHS.Attractive.positiveFeatureParticleExp_eq_source
#check DGRHS.Attractive.exists_separable_positiveFeature_linearization
#print axioms DGRHS.Attractive.exists_separable_positiveFeature_linearization
