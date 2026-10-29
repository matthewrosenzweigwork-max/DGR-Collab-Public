/- The mean-zero covariance resolvent is uniquely identified by actual
inverse identities. Separate Gaussian constructions cannot choose different
covariance operators for the SAME original canonical kernel. -/
import DGRHS.Kernel.LinearCentering
noncomputable section
open MeasureTheory
namespace DGRHS.Kernel
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma meanZeroResolvent_unique (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ z ∂μ.prod μ,h z.swap=h z)
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0) (β : ℝ)
    (R T : meanZeroL2 μ →L[ℝ] meanZeroL2 μ)
    (hR : ∀ v,R v+β • integralOperatorOnMeanZero h hh hs hc (R v)=v)
    (hT : ∀ v,T (v+β • integralOperatorOnMeanZero h hh hs hc v)=v) : R=T := by
  let A : meanZeroL2 μ →L[ℝ] meanZeroL2 μ :=
    ContinuousLinearMap.id ℝ (meanZeroL2 μ)+β • integralOperatorOnMeanZero h hh hs hc
  apply twoSidedInverse_unique A R T
  · intro v
    exact hR v
  · intro v
    exact hT v
end DGRHS.Kernel
#print axioms DGRHS.Kernel.meanZeroResolvent_unique
#check @DGRHS.Kernel.meanZeroResolvent_unique
