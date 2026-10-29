import DGRHS.Attractive.SignedFeatureAllNRate
import DGRHS.Attractive.SignedFeatureStatistic
import DGRHS.Gaussian.FeatureRateSourceSpectrum

/-! Literal positive-sign source off-diagonal rate and actual source operator.
Product-a.e. Gram equality is pulled back only along distinct coordinates.
The proper source second moment is the explicit original hypothesis; all
field, polynomial, determinant, and rate conclusions are derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace.CountablyGenerated X]

theorem exists_sourceKernel_positive_feature_rate
    (β : ℝ) (hβ : 0≤β) (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (hmean : (∫ x,k x ∂μ)=0) (heq : h =ᵐ[μ.prod μ] featureKernel k)
    (hp : ∀ N : ℕ,1≤N → Integrable
      (fun x : Fin N → X => Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)))
    (U : ℝ) (hU : ∀ N : ℕ,1≤N →
      (∫ x : Fin N → X,Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ))≤U)
    (hgap : |2*β| * ‖DGRHS.Kernel.integralOperator h hh‖<1) :
    let M := ∫ x,Real.exp (a*‖k x‖^2) ∂μ
    let cb := positiveFeatureQuadraticFourthConstant β a
    let cr := positiveFeatureCubicFourthConstant β a
    let ce := positiveFeatureRemainderFourthConstant β a
    let L := Real.exp ((2*β)^2*(∫ p,h p^2 ∂μ.prod μ)/
      (2*(1-|2*β| * ‖DGRHS.Kernel.integralOperator h hh‖)))
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)),Countable ι ∧
      (∀ i,DGRHS.Kernel.integralOperator h hh (b i)=eig i • b i) ∧
      ∀ N : ℕ,1≤N →
        Integrable (fun x : Fin N → X => Real.exp
          (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x : Fin N → X,Real.exp (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
            ∂Measure.pi (fun _ : Fin N => μ))-
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β*eig i)))⁻¹| ≤
          (Real.sqrt (32*β/a)+8+3*cr+3*ce+756*(cb+cr+ce))*M*
            (Real.sqrt U+Real.sqrt L)/Real.sqrt (N:ℝ) := by
  dsimp only
  have hk2 := feature_memLp_two_of_diagonal_exponential k hk a ha hM
  have hop := integralOperator_eq_of_ae_kernel hh (memLp_featureKernel k hk hk2) heq
  have hp' : ∀ N : ℕ,1≤N → Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ)) :=
    fun N hN => integrable_positiveFeatureParticleExp_of_source β h k heq N hN (hp N hN)
  have hu' : ∀ N : ℕ,1≤N →
      (∫ x,positiveFeatureParticleExp (2*β) k N x ∂Measure.pi (fun _ : Fin N => μ))≤U := by
    intro N hN
    have hcongr := ae_positiveFeatureParticleExp_eq_source (2*β) h k heq N hN
    have he' : positiveFeatureParticleExp (2*β) k N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
        (fun x => Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
      filter_upwards [hcongr] with x hx
      convert hx using 1 <;> congr 1 <;> ring
    exact (integral_congr_ae he').trans_le (hU N hN)
  have hg' : |2*β| * ‖DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2)‖<1 := by rw [←hop];exact hgap
  obtain ⟨ι,eig,e,hι,he,hRate⟩ := exists_positiveFeature_allN_partition_rate β hβ k hk a ha hM hmean hp' U hu' hg'
  have hHS : (∫ p,featureKernel k p^2 ∂μ.prod μ)=(∫ p,h p^2 ∂μ.prod μ) := by
    apply integral_congr_ae
    filter_upwards [heq] with p hp
    rw [hp]
  refine ⟨ι,eig,e,hι,?_,fun N hN => ?_⟩
  · intro i
    rw [hop]
    exact he i
  · obtain ⟨hi,hb⟩ := hRate N hN
    have hc := ae_positiveFeatureParticleExp_eq_source β h k heq N hN
    refine ⟨hi.congr hc,?_⟩
    rw [←integral_congr_ae hc]
    rw [←hop,hHS] at hb
    exact hb

end DGRHS.Attractive
#check DGRHS.Attractive.exists_sourceKernel_positive_feature_rate
#print axioms DGRHS.Attractive.exists_sourceKernel_positive_feature_rate
