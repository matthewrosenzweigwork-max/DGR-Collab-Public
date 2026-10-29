import DGRHS.Gaussian.FeatureSynthesis
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! UNCHECKED DEVELOPMENT DRAFT. The actual covariance is a Bochner integral
of rank-one compact operators. This does not assume compactness as a premise.
Candidate code may only be compiled through the registered campaign route. -/

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

namespace DGRHS.Gaussian
noncomputable section

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem isCompactOperator_rankOne (v w : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℝ v w) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ w)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℝ v)

theorem integrable_featureRankOne (k : X → H) (hk2 : MemLp k 2 μ) :
    Integrable (fun x => InnerProductSpace.rankOne ℝ (k x) (k x)) μ := by
  have hc : Continuous (fun v : H => InnerProductSpace.rankOne ℝ v v) := by
    exact (InnerProductSpace.rankOne ℝ).continuous.clm_apply continuous_id
  have hi := (memLp_two_iff_integrable_sq_norm hk2.aestronglyMeasurable).1 hk2
  apply hi.mono' (hc.comp_aestronglyMeasurable hk2.aestronglyMeasurable)
  filter_upwards [] with x
  simp [pow_two]

theorem featureCovariance_eq_integral_rankOne (k : X → H) (hk2 : MemLp k 2 μ) :
    featureCovariance k hk2 =
      ∫ x, InnerProductSpace.rankOne ℝ (k x) (k x) ∂μ := by
  ext v
  rw [ContinuousLinearMap.integral_apply (integrable_featureRankOne k hk2),
    featureCovariance_eq_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp)

theorem featureCovariance_isCompactOperator (k : X → H) (hk2 : MemLp k 2 μ) :
    IsCompactOperator (featureCovariance k hk2) := by
  rw [featureCovariance_eq_integral_rankOne]
  let K : Submodule ℝ (H →L[ℝ] H) := compactOperator (RingHom.id ℝ) H H
  have hc : Convex ℝ (K : Set (H →L[ℝ] H)) := K.convex
  have hclosed : IsClosed (K : Set (H →L[ℝ] H)) :=
    isClosed_setOfPred_isCompactOperator
  exact hc.integral_mem hclosed
    (Filter.Eventually.of_forall (fun x => isCompactOperator_rankOne (k x) (k x)))
    (integrable_featureRankOne k hk2)

end
end DGRHS.Gaussian

#check DGRHS.Gaussian.isCompactOperator_rankOne
#print axioms DGRHS.Gaussian.isCompactOperator_rankOne
#check DGRHS.Gaussian.integrable_featureRankOne
#print axioms DGRHS.Gaussian.integrable_featureRankOne
#check DGRHS.Gaussian.featureCovariance_eq_integral_rankOne
#print axioms DGRHS.Gaussian.featureCovariance_eq_integral_rankOne
#check DGRHS.Gaussian.featureCovariance_isCompactOperator
#print axioms DGRHS.Gaussian.featureCovariance_isCompactOperator
