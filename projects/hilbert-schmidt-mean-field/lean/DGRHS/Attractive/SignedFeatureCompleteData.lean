import DGRHS.Attractive.SignedFeatureMomentFactory
import DGRHS.Attractive.SignedFeatureQuadraticBound

/-! Actual same-field data for the source good-set comparison. All L2 and
fourth-moment conclusions are derived from the constructed field, original
proper doubled particle moments, diagonal exponential moment and actual
operator margin. No Taylor, field, Laplace or rate conclusion is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]

lemma second_moment_le_one_add_fourth {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (z : Ω → ℝ)
    (hm : AEStronglyMeasurable z P) (h4 : Integrable (fun ω => z ω^4) P) :
    Integrable (fun ω => z ω^2) P ∧
      (∫ ω,z ω^2 ∂P) ≤ 1+(∫ ω,z ω^4 ∂P) := by
  have h2 := (integrable_lower_powers_of_fourth z hm h4).2
  refine ⟨h2,?_⟩
  have hb := integral_mono h2 ((integrable_const (1:ℝ)).add h4)
    (fun ω => by
      change z ω^2≤1+z ω^4
      nlinarith [sq_nonneg (z ω^2-1/2)])
  have he := integral_add (integrable_const (1:ℝ)) h4
  change (∫ ω,1+z ω^4 ∂P)=(∫ ω,(1:ℝ) ∂P)+(∫ ω,z ω^4 ∂P) at he
  change (∫ ω,z ω^2 ∂P)≤(∫ ω,1+z ω^4 ∂P) at hb
  rw [he] at hb
  simpa using hb

def positiveFeatureQuadraticFourthConstant (β a : ℝ) : ℝ :=
  27*(β/2)^4*(gaussianDiagonalMomentConstant a 0 4+gaussianDiagonalMomentConstant a 4 0)
def positiveFeatureCubicFourthConstant (β a : ℝ) : ℝ :=
  27*(β*Real.sqrt β/6)^4*
    (gaussianDiagonalMomentConstant a 0 6+81*gaussianDiagonalMomentConstant a 4 2)
def positiveFeatureRemainderFourthConstant (β a : ℝ) : ℝ :=
  β^8*(6912*gaussianDiagonalMomentConstant a 0 8+
    432*gaussianDiagonalMomentConstant a 4 4+27*gaussianDiagonalMomentConstant a 8 0)

theorem exists_positiveFeature_goodSet_data [MeasurableSpace.CountablyGenerated X]
    (β : ℝ) (hβ : 0≤β) (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (hmean : (∫ x,k x ∂μ)=0)
    (hp : ∀ N : ℕ,1≤N → Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ)))
    (U : ℝ) (hU : ∀ N : ℕ,1≤N →
      (∫ x,positiveFeatureParticleExp (2*β) k N x ∂Measure.pi (fun _ : Fin N => μ))≤U)
    (hgap : |2*β| *‖DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖<1) :
    let M := ∫ x,Real.exp (a*‖k x‖^2) ∂μ
    let L := Real.exp ((2*β)^2*(∫ p,featureKernel k p^2 ∂μ.prod μ)/
      (2*(1-|2*β| *‖DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖)))
    ∃ (j : Type v) (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
      (g : X × (ℕ → ℝ) → ℝ), Countable j ∧ StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ,(fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      MemLp (fun ω => Real.exp (positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω))
        2 IsonormalProcess.iidStdGaussian ∧
      (∫ ω,Real.exp (positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω)^2
        ∂IsonormalProcess.iidStdGaussian)≤L ∧
      Integrable (fun ω => positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω^4)
        IsonormalProcess.iidStdGaussian ∧
      (∫ ω,positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω^4
        ∂IsonormalProcess.iidStdGaussian)≤positiveFeatureQuadraticFourthConstant β a*M ∧
      Integrable (fun ω => positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^4)
        IsonormalProcess.iidStdGaussian ∧
      (∫ ω,positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^4
        ∂IsonormalProcess.iidStdGaussian)≤positiveFeatureCubicFourthConstant β a*M ∧
      Integrable (fun ω => positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^2)
        IsonormalProcess.iidStdGaussian ∧
      (∫ ω,positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^2
        ∂IsonormalProcess.iidStdGaussian)≤1+positiveFeatureCubicFourthConstant β a*M ∧
      ∀ N : ℕ,1≤N →
        (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,0<positiveFeatureFactor μ β k g N ω) ∧
        MemLp (fun ω => positiveFeatureFactor μ β k g N ω^N) 2 IsonormalProcess.iidStdGaussian ∧
        (∫ ω,(positiveFeatureFactor μ β k g N ω^N)^2 ∂IsonormalProcess.iidStdGaussian)≤U ∧
        (∫ x,positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ))=
          (∫ ω,positiveFeatureFactor μ β k g N ω^N ∂IsonormalProcess.iidStdGaussian) ∧
        (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,positiveFeatureFactor μ β k g N ω=
          1+positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω/(N:ℝ)+
            positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω/((N:ℝ)*Real.sqrt (N:ℝ))+
            positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω/(N:ℝ)^2) ∧
        (32*β≤a*(N:ℝ) →
          Integrable (fun ω => positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^4)
            IsonormalProcess.iidStdGaussian ∧
          (∫ ω,positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^4
            ∂IsonormalProcess.iidStdGaussian)≤positiveFeatureRemainderFourthConstant β a*M ∧
          Integrable (fun ω => positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^2)
            IsonormalProcess.iidStdGaussian ∧
          (∫ ω,positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^2
            ∂IsonormalProcess.iidStdGaussian)≤1+positiveFeatureRemainderFourthConstant β a*M) := by
  dsimp only
  obtain ⟨j,b,f,hf,g,hj,hg,hg2,hW,hiB,hbB,hiR,hbR,hNdata⟩ :=
    exists_positiveFeature_moment_data β hβ k hk a ha hM hmean hp
  letI : Countable j := hj
  have hDm : StronglyMeasurable (fun x => ‖k x‖^2) := hk.norm.pow 2
  have hBs := stronglyMeasurable_positiveQuadraticCoefficient (μ := μ) β _ hDm g hg
  have hRs := stronglyMeasurable_positiveCubicCoefficient (μ := μ) β _ hDm g hg
  obtain ⟨h2B,hbound⟩ := positiveQuadraticCoefficient_exponential_bound
    b f hf β k hk a ha hM hmean g hg hg2 hW 2 hgap
  have heq : (fun ω => Real.exp (positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω)^2)=
      fun ω => Real.exp (2*positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω) := by
    funext ω
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have h2exp : Integrable (fun ω => Real.exp (positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω)^2)
      IsonormalProcess.iidStdGaussian := by rw [heq]; exact h2B
  have hexp := (memLp_two_iff_integrable_sq (Real.continuous_exp.comp_stronglyMeasurable hBs).aestronglyMeasurable).2 h2exp
  obtain ⟨hiR2,hbR2⟩ := second_moment_le_one_add_fourth _ hRs.aestronglyMeasurable hiR
  refine ⟨j,b,f,hf,g,hj,hg,hg2,hW,hexp,by rw [heq];exact hbound,hiB,hbB,hiR,hbR,hiR2,
    hbR2.trans (add_le_add_right hbR 1),?_⟩
  intro N hN
  obtain ⟨hpos,_,_,_,heAN,hiA2N,heA2N,htaylor,hEn⟩ := hNdata N hN
  have h2pow : Integrable (fun ω => (positiveFeatureFactor μ β k g N ω^N)^2)
      IsonormalProcess.iidStdGaussian := by
    simpa only [←pow_mul,Nat.mul_comm] using hiA2N
  have hpow := (memLp_two_iff_integrable_sq
    ((stronglyMeasurable_positiveFeatureFactor β k hk g hg N).pow N).aestronglyMeasurable).2 h2pow
  have hboundPow : (∫ ω,(positiveFeatureFactor μ β k g N ω^N)^2 ∂IsonormalProcess.iidStdGaussian)≤U := by
    simpa only [←pow_mul,Nat.mul_comm] using heA2N.trans_le (hU (2*N) (by omega))
  refine ⟨hpos,hpow,hboundPow,heAN,htaylor,?_⟩
  intro hscale
  obtain ⟨hiE,hbE⟩ := hEn hscale
  have hEs : StronglyMeasurable (positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N) :=
    (stronglyMeasurable_positiveIntegratedWickRemainder β _ hDm g hg (featureRateScale N)).const_mul _
  obtain ⟨hiE2,hbE2⟩ := second_moment_le_one_add_fourth _ hEs.aestronglyMeasurable hiE
  exact ⟨hiE,hbE,hiE2,hbE2.trans (add_le_add_right hbE 1)⟩

end DGRHS.Attractive
#check DGRHS.Attractive.exists_positiveFeature_goodSet_data
#print axioms DGRHS.Attractive.exists_positiveFeature_goodSet_data
