import DGRHS.Attractive.SignedFeatureFibers
import DGRHS.Attractive.SignedFeatureExpansion

/-! One constructed field supplies the genuine positive-factor identities,
coefficient moments and all-positive-N AE expansion. The diagonal exponential
parameter is independent of beta. The original explicit doubled particle
properness assumption is retained; no field or Taylor conclusion is assumed. -/
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

lemma one_le_integral_featureDiagonalExponential (k : X → H) (a : ℝ) (ha : 0≤a)
    (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ) :
    1≤∫ x,Real.exp (a*‖k x‖^2) ∂μ := by
  calc
    1 = ∫ x,(1:ℝ) ∂μ := by simp
    _ ≤ _ := integral_mono (integrable_const (1:ℝ)) hM
      (fun x => Real.one_le_exp_iff.mpr (mul_nonneg ha (sq_nonneg _)))

theorem exists_positiveFeature_moment_data
    (β : ℝ) (hβ : 0≤β) (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (hmean : (∫ x,k x ∂μ)=0)
    (hp : ∀ N : ℕ,1≤N → Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ))) :
    ∃ (j : Type v) (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
      (g : X × (ℕ → ℝ) → ℝ),Countable j ∧ StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ,(fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      Integrable (fun ω => positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω^4)
        IsonormalProcess.iidStdGaussian ∧
      (∫ ω,positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω^4
        ∂IsonormalProcess.iidStdGaussian) ≤
        27*(β/2)^4*(gaussianDiagonalMomentConstant a 0 4+gaussianDiagonalMomentConstant a 4 0)*
          (∫ x,Real.exp (a*‖k x‖^2) ∂μ) ∧
      Integrable (fun ω => positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^4)
        IsonormalProcess.iidStdGaussian ∧
      (∫ ω,positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω^4
        ∂IsonormalProcess.iidStdGaussian) ≤
        27*(β*Real.sqrt β/6)^4*
          (gaussianDiagonalMomentConstant a 0 6+81*gaussianDiagonalMomentConstant a 4 2)*
            (∫ x,Real.exp (a*‖k x‖^2) ∂μ) ∧
      ∀ N : ℕ,1≤N →
        (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,0<positiveFeatureFactor μ β k g N ω) ∧
        Integrable (positiveFeatureFactor μ β k g N) IsonormalProcess.iidStdGaussian ∧
        (∫ ω,positiveFeatureFactor μ β k g N ω ∂IsonormalProcess.iidStdGaussian)=1 ∧
        Integrable (fun ω => positiveFeatureFactor μ β k g N ω^N) IsonormalProcess.iidStdGaussian ∧
        (∫ x,positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ))=
          (∫ ω,positiveFeatureFactor μ β k g N ω^N ∂IsonormalProcess.iidStdGaussian) ∧
        Integrable (fun ω => positiveFeatureFactor μ β k g N ω^(2*N)) IsonormalProcess.iidStdGaussian ∧
        (∫ ω,positiveFeatureFactor μ β k g N ω^(2*N) ∂IsonormalProcess.iidStdGaussian)=
          (∫ x,positiveFeatureParticleExp (2*β) k (2*N) x ∂Measure.pi (fun _ : Fin (2*N) => μ)) ∧
        (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,positiveFeatureFactor μ β k g N ω=
          1+positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω/(N:ℝ)+
            positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω/((N:ℝ)*Real.sqrt (N:ℝ))+
            positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω/(N:ℝ)^2) ∧
        (32*β≤a*(N:ℝ) →
          Integrable (fun ω => positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^4)
            IsonormalProcess.iidStdGaussian ∧
          (∫ ω,positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω^4
            ∂IsonormalProcess.iidStdGaussian) ≤
              β^8*(6912*gaussianDiagonalMomentConstant a 0 8+
                432*gaussianDiagonalMomentConstant a 4 4+27*gaussianDiagonalMomentConstant a 8 0)*
                  (∫ x,Real.exp (a*‖k x‖^2) ∂μ)) := by
  obtain ⟨j,b,f,hf,g,hj,hg,hg2,hW,hLaw,hI,hC,hNdata⟩ :=
    exists_separable_positiveFeature_fibers β hβ k hk a ha hM hmean hp
  letI : Countable j := hj
  have hDm : StronglyMeasurable (fun x => ‖k x‖^2) := hk.norm.pow 2
  have hD : ∀ x,0≤‖k x‖^2 := fun x => sq_nonneg _
  obtain ⟨_,hiB,hbB⟩ := positive_quadratic_fourth_moment β _ hDm hD g hg hLaw a ha hM
  obtain ⟨_,hiR,hbR⟩ := positive_cubic_fourth_moment β _ hDm hD g hg hLaw a ha hM
  refine ⟨j,b,f,hf,g,hj,hg,hg2,hW,hiB,hbB,hiR,hbR,?_⟩
  intro N hN
  obtain ⟨hpos,hiA,hmA,hiAN,heAN,hiA2N,heA2N⟩ := hNdata N hN
  have hw : ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      Integrable (fun x => positiveFeatureWick β k g N (x,ω)) μ := hpos.mono (fun _ h => h.1)
  refine ⟨hpos.mono (fun _ h => h.2),hiA,hmA,hiAN,heAN,hiA2N,heA2N,
    ae_positiveFeatureFactor_expansion β k hk g hg hLaw hI hC a ha hM N hN hw,?_⟩
  intro hscale
  exact positiveFeatureNormalizedRemainder_fourth_moment β hβ _ hDm hD g hg hLaw a ha hM N hN hscale

end DGRHS.Attractive
#check DGRHS.Attractive.exists_positiveFeature_moment_data
#print axioms DGRHS.Attractive.exists_positiveFeature_moment_data

#check DGRHS.Attractive.one_le_integral_featureDiagonalExponential
#print axioms DGRHS.Attractive.one_le_integral_featureDiagonalExponential
