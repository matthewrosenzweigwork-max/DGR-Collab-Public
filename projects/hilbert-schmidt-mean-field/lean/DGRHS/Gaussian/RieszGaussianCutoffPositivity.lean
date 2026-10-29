/- Positivity of the SAME source cutoff integral operator follows from its
constructed real Hilbert Gram feature. No favorable spectral sign is a premise. -/
import DGRHS.Gaussian.RieszGaussianEuclideanCentering
import DGRHS.Gaussian.FeatureKernel
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

theorem sourceGaussianRieszCutoff_positive (s η : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hh : MemLp (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) 2 (μ.prod μ)) :
    ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator
      (fun p => centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) hh v) := by
  let k := centeredGaussianRieszEuclideanFourierFeature (ι := ι) s η hs hη μ
  have hk : StronglyMeasurable k := stronglyMeasurable_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ
  have hk2 : MemLp k 2 μ := memLp_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ 2
  have he : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      centeredGaussianRieszEuclideanTruncatedKernel s η μ p.1 p.2) = featureKernel k := by
    funext p
    exact (inner_centeredGaussianRieszEuclideanFourierFeature s η hs hη μ p.1 p.2).symm
  intro v
  have hp := integralOperator_featureKernel_nonneg k hk hk2 v
  simpa only [←he,real_inner_comm] using hp
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sourceGaussianRieszCutoff_positive
#check @DGRHS.Gaussian.sourceGaussianRieszCutoff_positive
