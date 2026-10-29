import DGRHS.Gaussian.GaussianLogInfiniteFeatureGram
import DGRHS.Gaussian.GaussianLogAdaptiveComparison
import DGRHS.Gaussian.FeatureRateSourceDiagonalTail
import DGRHS.Gaussian.FeatureRateSourceSpectrum
import DGRHS.Concentration.SourcePartitionRate

/-! Original repulsive logarithmic rate, source1939–2040. The actual SAME
infinite-phase centered feature and its physical diagonal derive the proper
weighted moment under the original exp(-4 beta h_full) hypothesis. -/
noncomputable section
open MeasureTheory Real Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.SourceRepulsiveLogRate
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma feature_diagonal_uniform (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (x : EuclideanSpace ℝ ι) :
    ‖gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair x‖^2 ≤
      (2*gaussianLogShortConstant M ι+1/4+
        |∫ p,logPhysicalPair p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)|)+
        Real.log (1/η)-2*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x := by
  have hs := norm_sq_gaussianLogCenteredInfiniteFeature_le_sourcePotential η hη hd ρ M hM hρ hpair x
  have hp : η^(Fintype.card ι:ℝ)≤1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hη.le hη1 hd.le
  have hC : 0≤M*((2*Real.pi)^((Fintype.card ι:ℝ)/2)/(Fintype.card ι:ℝ)) := by positivity
  have hb := mul_le_mul_of_nonneg_left hp hC
  rw [show 1/η=η⁻¹ by simp only [one_div],Real.log_inv]
  unfold gaussianLogShortConstant
  nlinarith only [hs,hb,le_abs_self (∫ p,logPhysicalPair p
    ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))]

 theorem exists_feature_moment_uniform (β : ℝ) (hβ : 0<β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    ∃ K : ℝ,0≤K ∧ ∀ (η : ℝ) (hη : 0<η),η≤1 →
      Integrable (featureExponentialMomentWeight β
        (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair)) (gaussianRieszDensityMeasure ρ) ∧
      (∫ x,featureExponentialMomentWeight β
        (gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair) x ∂gaussianRieszDensityMeasure ρ) ≤
        K*Real.exp (2*β*Real.log (1/η)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let A := 2*gaussianLogShortConstant M ι+1/4+|∫ p,logPhysicalPair p ∂μ.prod μ|
  let K := featureDiagonalMomentConstant β*Real.exp (2*β*A)*
    (∫ x,Real.exp (-4*β*logPhysicalPotential μ x) ∂μ)
  have hK : 0≤K := by
    have hi : 0≤∫ x,Real.exp (-4*β*logPhysicalPotential μ x) ∂μ := integral_nonneg (fun _=>Real.exp_nonneg _)
    dsimp [K,featureDiagonalMomentConstant]
    positivity
  refine ⟨K,hK,?_⟩
  intro η hη hη1
  let k := gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  have hk := stronglyMeasurable_gaussianLogCenteredInfiniteFeature η hη hd ρ M hM hρ hpair
  have he : Integrable (fun x=>Real.exp (4*β*(-logPhysicalPotential μ x))) μ := by
    convert htail using 1
    funext x
    congr 1
    ring
  have hD : ∀ᵐ x ∂μ,‖k x‖^2≤(A+Real.log (1/η))+2*(-logPhysicalPotential μ x) :=
    Eventually.of_forall (fun x=>by
      have h := feature_diagonal_uniform η hη hη1 hd ρ M hM hρ hpair x
      dsimp only [k,A,μ]
      linarith only [h])
  obtain ⟨hi,hb⟩ := featureRateMoment_of_source_diagonal β (A+Real.log (1/η)) hβ k hk
    (fun x=> -logPhysicalPotential μ x) hD he
  refine ⟨hi,hb.trans_eq ?_⟩
  have ht : (∫ x,Real.exp (4*β*(-logPhysicalPotential μ x)) ∂μ)=
      (∫ x,Real.exp (-4*β*logPhysicalPotential μ x) ∂μ) := by
    congr 1
    funext x
    congr 1
    ring
  rw [ht,show 2*β*(A+Real.log (1/η))=2*β*A+2*β*Real.log (1/η) by ring,Real.exp_add]
  dsimp only [K]
  ring

end DGRHS.SourceRepulsiveLogRate
#check @DGRHS.SourceRepulsiveLogRate.feature_diagonal_uniform
#print axioms DGRHS.SourceRepulsiveLogRate.feature_diagonal_uniform
#check @DGRHS.SourceRepulsiveLogRate.exists_feature_moment_uniform
#print axioms DGRHS.SourceRepulsiveLogRate.exists_feature_moment_uniform
