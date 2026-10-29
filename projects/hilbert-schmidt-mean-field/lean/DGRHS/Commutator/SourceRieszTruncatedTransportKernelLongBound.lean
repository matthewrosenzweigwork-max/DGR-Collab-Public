import DGRHS.Commutator.SourceRieszTruncatedTransportKernelShortBound
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual all-order long Gaussian Riesz profile transport estimate.
The derivative, scale change and scale monotonicity are proved here. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

lemma sourceRieszLongScale_widen (s η r : ℝ) (hη : 0<η) :
    (∫ t in Ioi η,t^(-s-1)*Real.exp (-r^2/(8*t^2))) =
      (2:ℝ)^s * ∫ t in Ioi (2*η),t^(-s-1)*Real.exp (-r^2/(2*t^2)) := by
  let f : ℝ→ℝ := fun t=>t^(-s-1)*Real.exp (-r^2/(2*t^2))
  have he : (∫ t in Ioi η,f (2*t)) =
      (2:ℝ)^(-s-1)*(∫ t in Ioi η,t^(-s-1)*Real.exp (-r^2/(8*t^2))) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [f]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (hη.trans ht).le]
    have hg : -r^2/(2*(2*t)^2) = -r^2/(8*t^2) := by ring
    rw [hg]
    ring
  have hc := integral_comp_mul_left_Ioi f η (by norm_num : (0:ℝ)<2)
  simp only [smul_eq_mul] at hc
  rw [he] at hc
  have hp : (2:ℝ)^s*(2:ℝ)^(-s-1) = (2:ℝ)⁻¹ := by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    rw [show s+(-s-1)=(-1:ℝ) by ring,Real.rpow_neg_one]
  have hh := congrArg (fun a : ℝ=>2*(2:ℝ)^s*a) hc
  dsimp [f] at hh
  calc
    _ = 2*((2:ℝ)^s*(2:ℝ)^(-s-1))*(∫ t in Ioi η,t^(-s-1)*Real.exp (-r^2/(8*t^2))) := by rw [hp];ring
    _ = 2*(2:ℝ)^s*((2:ℝ)^(-s-1)*(∫ t in Ioi η,t^(-s-1)*Real.exp (-r^2/(8*t^2)))) := by ring
    _ = 2*(2:ℝ)^s*((2:ℝ)⁻¹*(∫ t in Ioi (2*η),t^(-s-1)*Real.exp (-r^2/(2*t^2)))) := hh
    _ = _ := by ring

lemma sourceRieszLongRange_scale_mono (s η θ : ℝ) (hs : 0<s) (hη : 0<η)
    (hηθ : η≤θ) {z : EuclideanSpace ℝ ι} (hz : z≠0) :
    DGRHS.Gaussian.gaussianRieszEuclideanTruncation s θ z ≤
      DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η z := by
  apply mul_le_mul_of_nonneg_left _ (DGRHS.Gaussian.gaussianRieszSourceCoefficient_pos s hs).le
  have hi := (DGRHS.Gaussian.integrableOn_gaussianRieszEuclidean_full_scale s hs z hz).mono_set
    (Ioi_subset_Ioi hη.le)
  apply setIntegral_mono_set hi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (hη.trans ht).le _) (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall (fun t ht=>hηθ.trans_lt ht)

lemma sourceRieszLongRange_iteratedFDeriv_formula (n : ℕ) (s η : ℝ) (hs : 0<s)
    (hη : 0<η) {z : EuclideanSpace ℝ ι} (hz : z≠0) :
    iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) z =
      DGRHS.Gaussian.gaussianRieszSourceCoefficient s •
        ∫ t in Ioi η,t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z := by
  exact sourceRieszGaussian_iteratedFDeriv_scale_integral n
    (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s (Ioi η)
    measurableSet_Ioi (Ioi_subset_Ioi hη.le) hs hz

lemma sourceRieszLongRange_all_order_transport_bound (n : ℕ) (s η : ℝ)
    (hs : 0<s) (hη : 0<η) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    {x y : EuclideanSpace ℝ ι} (hxy : x≠y) :
    |iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (x-y) (fun _=>v x-v y)| ≤
      (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*
        DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η (x-y) := by
  have h := sourceRieszGaussian_scale_integral_transport_bound n
    (DGRHS.Gaussian.gaussianRieszSourceCoefficient s) s (Ioi η)
    (DGRHS.Gaussian.gaussianRieszSourceCoefficient_pos s hs).le hs
    measurableSet_Ioi (Ioi_subset_Ioi hη.le) hv hxy
  change |iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (x-y) (fun _=>v x-v y)| ≤ _ at h
  rw [sourceRieszLongScale_widen s η ‖x-y‖ hη] at h
  have h' : |iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (x-y) (fun _=>v x-v y)| ≤
      (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*
        DGRHS.Gaussian.gaussianRieszEuclideanTruncation s (2*η) (x-y) := by
    convert h using 1
    unfold DGRHS.Gaussian.gaussianRieszEuclideanTruncation
    ring
  exact h'.trans (mul_le_mul_of_nonneg_left
    (sourceRieszLongRange_scale_mono s η (2*η) hs hη (by linarith) (sub_ne_zero.mpr hxy))
    (by have hC:=sourceRieszGaussianDerivativeConstant_pos n;positivity))

end DGRHS.Commutator
#check DGRHS.Commutator.sourceRieszLongScale_widen
#print axioms DGRHS.Commutator.sourceRieszLongScale_widen
#check DGRHS.Commutator.sourceRieszLongRange_scale_mono
#print axioms DGRHS.Commutator.sourceRieszLongRange_scale_mono
#check DGRHS.Commutator.sourceRieszLongRange_iteratedFDeriv_formula
#print axioms DGRHS.Commutator.sourceRieszLongRange_iteratedFDeriv_formula
#check DGRHS.Commutator.sourceRieszLongRange_all_order_transport_bound
#print axioms DGRHS.Commutator.sourceRieszLongRange_all_order_transport_bound
