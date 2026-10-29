import DGRHS.Gaussian.GaussianLogBandCanonical
import DGRHS.Gaussian.FeatureKernel
import DGRHS.Gaussian.GaussianRieszOperatorDifference

/-! Supporting development. Finite-band positivity follows from the actual centered
Fourier Gram feature; no positivity field is assumed. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma stronglyMeasurable_centeredGaussianLogBandFeature (η T : ℝ) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) :
    StronglyMeasurable (centeredGaussianLogBandFeature η T hη μ) :=
  (stronglyMeasurable_gaussianLogBandFeature η T hη).sub stronglyMeasurable_const

lemma memLp_centeredGaussianLogBandFeature (η T : ℝ) (hη : 0 < η) (hηT : η ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    MemLp (centeredGaussianLogBandFeature η T hη μ) 2 μ := by
  apply (memLp_const (2*‖gaussianLogBandFeature (ι := ι) η T hη 0‖)).of_le
    (stronglyMeasurable_centeredGaussianLogBandFeature η T hη μ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_centeredGaussianLogBandFeature_le η T hη hηT μ x)

lemma gaussianLogCenteredBand_operator_nonnegative (η T : ℝ) (hη : 0 < η) (hηT : η ≤ T)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hh : MemLp (hoeffdingCentered μ (gaussianLogBandPair η T)) 2 (μ.prod μ))
    (v : Lp ℝ 2 μ) :
    0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator
      (hoeffdingCentered μ (gaussianLogBandPair η T)) hh v) := by
  let k := centeredGaussianLogBandFeature (ι := ι) η T hη μ
  have hk := stronglyMeasurable_centeredGaussianLogBandFeature η T hη μ
  have hk2 := memLp_centeredGaussianLogBandFeature η T hη hηT μ
  have he : featureKernel k =ᵐ[μ.prod μ] hoeffdingCentered μ (gaussianLogBandPair η T) :=
    Filter.Eventually.of_forall (fun p => inner_centeredGaussianLogBandFeature η T hη hηT μ p.1 p.2)
  have hop := gaussian_integralOperator_congr μ _ _ (memLp_featureKernel k hk hk2) hh he
  rw [← hop, real_inner_comm]
  exact integralOperator_featureKernel_nonneg k hk hk2 v

end DGRHS.Gaussian
#check @DGRHS.Gaussian.stronglyMeasurable_centeredGaussianLogBandFeature
#print axioms DGRHS.Gaussian.stronglyMeasurable_centeredGaussianLogBandFeature
#check @DGRHS.Gaussian.memLp_centeredGaussianLogBandFeature
#print axioms DGRHS.Gaussian.memLp_centeredGaussianLogBandFeature
#check @DGRHS.Gaussian.gaussianLogCenteredBand_operator_nonnegative
#print axioms DGRHS.Gaussian.gaussianLogCenteredBand_operator_nonnegative
