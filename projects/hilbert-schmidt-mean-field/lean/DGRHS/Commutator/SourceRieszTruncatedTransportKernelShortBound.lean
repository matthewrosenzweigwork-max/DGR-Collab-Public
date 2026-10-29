import DGRHS.Commutator.SourceRieszTruncatedTransportKernelIntegralBound
import DGRHS.Commutator.SourceRieszTruncatedTransportKernelFirst

/-! Actual all-order short Gaussian Riesz profile and transport absorption. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

lemma sourceRieszShortRange_iteratedFDeriv_formula (n : ℕ) (s η : ℝ) (hs : 0<s)
    {z : EuclideanSpace ℝ ι} (hz : z≠0) :
    iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η) z =
      DGRHS.Gaussian.gaussianRieszSourceCoefficient s •
        ∫ t in Ioc 0 η,t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z := by
  exact sourceRieszGaussian_iteratedFDeriv_scale_integral n
    (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s (Ioc 0 η)
    measurableSet_Ioc Ioc_subset_Ioi_self hs hz

lemma sourceRieszShortRange_all_order_transport_bound (n : ℕ) (s η : ℝ)
    (hs : 0<s) (hη : 0<η) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    {x y : EuclideanSpace ℝ ι} (hxy : x≠y) :
    |iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η) (x-y) (fun _=>v x-v y)| ≤
      (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*
        DGRHS.Gaussian.gaussianRieszEuclideanShortRange s (2*η) (x-y) := by
  have h := sourceRieszGaussian_scale_integral_transport_bound n
    (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s (Ioc 0 η)
    (DGRHS.Gaussian.gaussianRieszSourceCoefficient_pos s hs).le hs
    measurableSet_Ioc Ioc_subset_Ioi_self hv hxy
  change |iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η) (x-y) (fun _=>v x-v y)| ≤ _ at h
  rw [sourceRieszShortScale_widen s η ‖x-y‖ hη] at h
  convert h using 1
  unfold DGRHS.Gaussian.gaussianRieszEuclideanShortRange
  ring

lemma sourceRieszShortTransportKernel_all_order_bound (n : ℕ) (s η : ℝ)
    (hs : 0<s) (hη : 0<η) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
    |sourceRieszShortTransportKernel n s η v p| ≤
      (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*
        DGRHS.Gaussian.gaussianRieszEuclideanShortRange s (2*η) (p.1-p.2) := by
  unfold sourceRieszShortTransportKernel
  split_ifs with hp
  · simp only [abs_zero]
    exact mul_nonneg (by have h:0<sourceRieszGaussianDerivativeConstant n:=sourceRieszGaussianDerivativeConstant_pos n;positivity)
      (DGRHS.Gaussian.gaussianRieszEuclideanShortRange_nonneg s (2*η) hs _)
  · exact sourceRieszShortRange_all_order_transport_bound n s η hs hη hv hp

end DGRHS.Commutator
#check DGRHS.Commutator.sourceRieszShortRange_iteratedFDeriv_formula
#print axioms DGRHS.Commutator.sourceRieszShortRange_iteratedFDeriv_formula
#check DGRHS.Commutator.sourceRieszShortRange_all_order_transport_bound
#print axioms DGRHS.Commutator.sourceRieszShortRange_all_order_transport_bound
#check DGRHS.Commutator.sourceRieszShortTransportKernel_all_order_bound
#print axioms DGRHS.Commutator.sourceRieszShortTransportKernel_all_order_bound
