import DGRHS.Attractive.SignedFeatureLinearization
import DGRHS.Gaussian.FeatureRateSourceKernel
import DGRHS.Concentration.SourcePartitionRate

/-! Exact source off-diagonal statistic adapter. Product-a.e. feature equality
is pulled back only along genuinely distinct iid coordinates, never onto the
diagonal. Actual source exponential properness supplies the factory input. -/
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure X} [IsProbabilityMeasure μ]

lemma positiveFeatureParticleExp_eq_source_statistic (β : ℝ) (k : X → H)
    (N : ℕ) (hN : 1≤N) (x : Fin N → X) :
    positiveFeatureParticleExp β k N x=
      Real.exp (β/2*sourceKernelParticleStatistic (featureKernel k) N x) := by
  unfold positiveFeatureParticleExp sourceKernelParticleStatistic featureKernel
  rw [feature_particle_off_diagonal_sum]
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma ae_positiveFeatureParticleExp_eq_source (β : ℝ) (h : X × X → ℝ) (k : X → H)
    (heq : h =ᵐ[μ.prod μ] featureKernel k) (N : ℕ) (hN : 1≤N) :
    positiveFeatureParticleExp β k N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => Real.exp (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
  filter_upwards [ae_sourceKernelParticleStatistic_eq_feature h k heq N] with x hx
  rw [positiveFeatureParticleExp_eq_source_statistic β k N hN,
    ←hx,DGRHS.Concentration.sourceKernelParticleStatistic_eq_normalized]

lemma integrable_positiveFeatureParticleExp_of_source (β : ℝ) (h : X × X → ℝ)
    (k : X → H) (heq : h =ᵐ[μ.prod μ] featureKernel k) (N : ℕ) (hN : 1≤N)
    (hp : Integrable (fun x : Fin N → X => Real.exp
      (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N => μ))) :
    Integrable (positiveFeatureParticleExp (2*β) k N) (Measure.pi (fun _ : Fin N => μ)) := by
  have he := ae_positiveFeatureParticleExp_eq_source (2*β) h k heq N hN
  have he' : positiveFeatureParticleExp (2*β) k N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    filter_upwards [he] with x hx
    convert hx using 1 <;> congr 1 <;> ring
  exact hp.congr he'.symm

end DGRHS.Attractive
#check DGRHS.Attractive.positiveFeatureParticleExp_eq_source_statistic
#print axioms DGRHS.Attractive.positiveFeatureParticleExp_eq_source_statistic
#check DGRHS.Attractive.ae_positiveFeatureParticleExp_eq_source
#print axioms DGRHS.Attractive.ae_positiveFeatureParticleExp_eq_source
#check DGRHS.Attractive.integrable_positiveFeatureParticleExp_of_source
#print axioms DGRHS.Attractive.integrable_positiveFeatureParticleExp_of_source
