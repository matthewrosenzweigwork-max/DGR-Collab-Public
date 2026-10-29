import DGRHS.Commutator.SourceRieszTruncatedTransportKernelDerivative
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual first-order short-profile transport absorption. -/
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal RealInnerProductSpace
namespace DGRHS.Commutator

lemma sourceRieszShortScale_widen (s η r : ℝ) (hη : 0<η) :
    (∫ t in Ioc 0 η,t^(-s-1)*Real.exp (-r^2/(8*t^2))) =
      (2:ℝ)^s * ∫ t in Ioc 0 (2*η),t^(-s-1)*Real.exp (-r^2/(2*t^2)) := by
  let f : ℝ→ℝ := fun t=>t^(-s-1)*Real.exp (-r^2/(2*t^2))
  have he : (∫ t in Ioc 0 η,f (2*t)) =
      (2:ℝ)^(-s-1)*(∫ t in Ioc 0 η,t^(-s-1)*Real.exp (-r^2/(8*t^2))) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp [f]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) ht.1.le]
    have hg : -r^2/(2*(2*t)^2) = -r^2/(8*t^2) := by ring
    rw [hg]
    ring
  have hc := intervalIntegral.integral_comp_mul_left (f:=f) (a:=0) (b:=η) (by norm_num : (2:ℝ)≠0)
  simp only [mul_zero] at hc
  rw [intervalIntegral.integral_of_le hη.le,intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*η)] at hc
  simp only [mul_zero,smul_eq_mul] at hc
  rw [he] at hc
  have hp : (2:ℝ)^s*(2:ℝ)^(-s-1) = (2:ℝ)⁻¹ := by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<2)]
    rw [show s+(-s-1)=(-1:ℝ) by ring,Real.rpow_neg_one]
  have hh := congrArg (fun a : ℝ=>2*(2:ℝ)^s*a) hc
  dsimp [f] at hh
  calc
    _ = 2*((2:ℝ)^s*(2:ℝ)^(-s-1))*(∫ t in Ioc 0 η,t^(-s-1)*Real.exp (-r^2/(8*t^2))) := by rw [hp];ring
    _ = 2*(2:ℝ)^s*((2:ℝ)^(-s-1)*(∫ t in Ioc 0 η,t^(-s-1)*Real.exp (-r^2/(8*t^2)))) := by ring
    _ = 2*(2:ℝ)^s*((2:ℝ)⁻¹*(∫ t in Ioc 0 (2*η),t^(-s-1)*Real.exp (-r^2/(2*t^2)))) := hh
    _ = _ := by ring

lemma integrable_sourceRieszShortScaleDerivative {ι : Type*} [Fintype ι]
    (s η : ℝ) (hs : 0<s) {z : EuclideanSpace ℝ ι} (hz : z≠0) :
    Integrable (fun t : ℝ=>t^(-s-1) • sourceRieszGaussianScaleDerivative t z)
      (volume.restrict (Ioc 0 η)) := by
  have hi := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale (s+2) (‖z‖^2/8)
    (by linarith) (by have h:=norm_pos_iff.mpr hz;positivity)).mono_set (s:=Ioc 0 η) Ioc_subset_Ioi_self
  have hb : Integrable (fun t : ℝ=>(3*‖z‖/2)*t^(-(s+2)-1)*Real.exp (-‖z‖^2/(8*t^2))) (volume.restrict (Ioc 0 η)) := by
    convert hi.const_mul (3*‖z‖/2) using 1
    ext t
    have he : -‖z‖^2/(8*t^2)=-(‖z‖^2/8)/t^2 := by ring
    rw [he]
    ring
  have ht : ∀ᵐ t ∂volume.restrict (Ioc 0 η),t∈Ioc 0 η := self_mem_ae_restrict measurableSet_Ioc
  exact hb.mono' ((sourceRieszGaussianScale_derivative_weight_continuousOn s η z).aestronglyMeasurable measurableSet_Ioc)
    (ht.mono (fun t ht=>
      sourceRieszGaussianScaleDerivative_local_bound s t ht.1 (mem_ball_self (half_pos (norm_pos_iff.mpr hz)))))

lemma sourceRieszShortRange_fderiv_transport_bound {ι : Type*} [Fintype ι]
    (s η : ℝ) (hs : 0<s) (hη : 0<η) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    {x y : EuclideanSpace ℝ ι} (hxy : x≠y) :
    |fderiv ℝ (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η) (x-y) (v x-v y)| ≤
      (4*(2:ℝ)^s)*(K:ℝ)*DGRHS.Gaussian.gaussianRieszEuclideanShortRange s (2*η) (x-y) := by
  let c := DGRHS.Gaussian.gaussianRieszSourceCoefficient s
  have hc : 0<c := DGRHS.Gaussian.gaussianRieszSourceCoefficient_pos s hs
  have hz : x-y≠0 := sub_ne_zero.mpr hxy
  have hi := integrable_sourceRieszShortScaleDerivative s η hs hz
  have hF := (hasFDerivAt_sourceRieszShortRange s η hs hη hz).fderiv
  rw [hF,smul_apply,smul_eq_mul,abs_mul,abs_of_pos hc,ContinuousLinearMap.integral_apply hi]
  have hEval : Integrable (fun t : ℝ=>(t^(-s-1) • sourceRieszGaussianScaleDerivative t (x-y)) (v x-v y)) (volume.restrict (Ioc 0 η)) :=
    (ContinuousLinearMap.apply ℝ ℝ (v x-v y)).integrable_comp hi
  have hG : Integrable (fun t : ℝ=>t^(-s-1)*Real.exp (-‖x-y‖^2/(8*t^2))) (volume.restrict (Ioc 0 η)) := by
    have hh := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale s (‖x-y‖^2/8) hs
      (by have h:=norm_pos_iff.mpr hz;positivity)).mono_set (s:=Ioc 0 η) Ioc_subset_Ioi_self
    change Integrable (fun t : ℝ=>t^(-s-1)*Real.exp (-(‖x-y‖^2/8)/t^2)) (volume.restrict (Ioc 0 η)) at hh
    convert hh using 1
    ext t
    congr 2
    ring
  have hB : (∫ t in Ioc 0 η,|(t^(-s-1) • sourceRieszGaussianScaleDerivative t (x-y)) (v x-v y)|) ≤
      4*(K:ℝ)*(∫ t in Ioc 0 η,t^(-s-1)*Real.exp (-‖x-y‖^2/(8*t^2))) := by
    rw [←integral_const_mul]
    have hAbs : Integrable (fun t : ℝ=>|(t^(-s-1) • sourceRieszGaussianScaleDerivative t (x-y)) (v x-v y)|) (volume.restrict (Ioc 0 η)) := by
      simpa only [Real.norm_eq_abs] using hEval.norm
    apply integral_mono_ae hAbs ((hG.const_mul (4*(K:ℝ))))
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    have hb := sourceRieszGaussianScale_transport_bound t ht.1 hv x y
    have he : Real.exp (-‖x-y‖^2/(4*t^2)) ≤ Real.exp (-‖x-y‖^2/(8*t^2)) := by
      apply Real.exp_le_exp.mpr
      have heq : -‖x-y‖^2/(4*t^2) = 2*(-‖x-y‖^2/(8*t^2)) := by ring
      rw [heq]
      have hn : -‖x-y‖^2/(8*t^2)≤0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
      linarith
    calc
      _ ≤ t^(-s-1)*(4*(K:ℝ)*Real.exp (-‖x-y‖^2/(8*t^2))) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left he (by positivity))) (Real.rpow_nonneg ht.1.le _)
      _ = _ := by ring
  calc
    _ ≤ c*(∫ t in Ioc 0 η,|(t^(-s-1) • sourceRieszGaussianScaleDerivative t (x-y)) (v x-v y)|) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t : ℝ=>(t^(-s-1) • sourceRieszGaussianScaleDerivative t (x-y)) (v x-v y))
    _ ≤ c*(4*(K:ℝ)*(∫ t in Ioc 0 η,t^(-s-1)*Real.exp (-‖x-y‖^2/(8*t^2)))) := mul_le_mul_of_nonneg_left hB hc.le
    _ = _ := by
      rw [sourceRieszShortScale_widen s η ‖x-y‖ hη]
      unfold DGRHS.Gaussian.gaussianRieszEuclideanShortRange
      dsimp [c]
      ring
end DGRHS.Commutator
#check DGRHS.Commutator.sourceRieszShortScale_widen
#print axioms DGRHS.Commutator.sourceRieszShortScale_widen
#check DGRHS.Commutator.integrable_sourceRieszShortScaleDerivative
#print axioms DGRHS.Commutator.integrable_sourceRieszShortScaleDerivative
#check DGRHS.Commutator.sourceRieszShortRange_fderiv_transport_bound
#print axioms DGRHS.Commutator.sourceRieszShortRange_fderiv_transport_bound
