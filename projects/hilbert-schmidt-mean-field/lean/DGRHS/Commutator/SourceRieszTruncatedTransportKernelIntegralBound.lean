import DGRHS.Commutator.SourceRieszTruncatedTransportKernelIteratedIntegral

/-! Actual integrated transport majorization on positive Gaussian scales. -/
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
-- Explicit local instances select the existing native operator-norm topologies.
-- They change neither the norm nor any imported instance declaration.
local instance sourceRieszTruncatedKernelMultilinearAddCommMonoid (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance sourceRieszTruncatedKernelMultilinearModule (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance sourceRieszTruncatedKernelMultilinearUniformSpace (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance sourceRieszTruncatedKernelMultilinearTopologicalSpace (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance sourceRieszTruncatedKernelDerivativeUniformSpace (n : ℕ) : UniformSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace
local instance sourceRieszTruncatedKernelDerivativeTopologicalSpace (n : ℕ) : TopologicalSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace
local instance sourceRieszTruncatedKernelDerivativeAddCommMonoid (n : ℕ) : AddCommMonoid (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toAddCommMonoid
local instance sourceRieszTruncatedKernelDerivativeModule (n : ℕ) : Module ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedSpace ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toModule


lemma sourceRieszGaussian_scale_integral_transport_bound (n : ℕ) (c s : ℝ) (S : Set ℝ)
    (hc : 0≤c) (hs : 0<s) (hSm : MeasurableSet S) (hS : S⊆Ioi 0)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) {x y : E} (hxy : x≠y) :
    |iteratedFDeriv ℝ n (fun z : E=>c*(∫ t in S,t^(-s-1)*sourceRieszGaussianScale t z)) (x-y) (fun _=>v x-v y)| ≤
      c*sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*(∫ t in S,t^(-s-1)*Real.exp (-‖x-y‖^2/(8*t^2))) := by
  have hz : x-y≠0 := sub_ne_zero.mpr hxy
  have hi := integrable_sourceRieszGaussian_scale_on n s S hSm hS hs hz
  have hF := sourceRieszGaussian_iteratedFDeriv_scale_integral n c s S hSm hS hs hz
  rw [hF,smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hc,ContinuousMultilinearMap.integral_apply hi]
  have hEval : Integrable (fun t : ℝ=>(t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)) (fun _=>v x-v y)) (volume.restrict S) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n=>E) ℝ (fun _=>v x-v y)).integrable_comp hi
  have hG : Integrable (fun t : ℝ=>t^(-s-1)*Real.exp (-‖x-y‖^2/(8*t^2))) (volume.restrict S) := by
    have hh := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale s (‖x-y‖^2/8) hs
      (by have h:=norm_pos_iff.mpr hz;positivity)).mono_set hS
    change Integrable (fun t : ℝ=>t^(-s-1)*Real.exp (-(‖x-y‖^2/8)/t^2)) (volume.restrict S) at hh
    convert hh using 1
    ext t
    congr 2
    ring
  have hC : 0≤sourceRieszGaussianDerivativeConstant n := (sourceRieszGaussianDerivativeConstant_pos n).le
  have hB : (∫ t in S,|(t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)) (fun _=>v x-v y)|) ≤
      sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*(∫ t in S,t^(-s-1)*Real.exp (-‖x-y‖^2/(8*t^2))) := by
    rw [←integral_const_mul]
    have hAbs : Integrable (fun t : ℝ=>|(t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)) (fun _=>v x-v y)|) (volume.restrict S) := by
      simpa only [Real.norm_eq_abs] using hEval.norm
    apply integral_mono_ae hAbs (hG.const_mul (sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n))
    filter_upwards [self_mem_ae_restrict hSm] with t ht
    simp only [smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg (hS ht).le _)]
    have hb := sourceRieszGaussian_all_order_transport_bound n t (hS ht) hv x y
    calc
      _ ≤ t^(-s-1)*(sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*Real.exp (-‖x-y‖^2/(8*t^2))) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (hS ht).le _)
      _ = _ := by ring
  calc
    _ ≤ c*(∫ t in S,|(t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)) (fun _=>v x-v y)|) := by
      apply mul_le_mul_of_nonneg_left _ hc
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t : ℝ=>(t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)) (fun _=>v x-v y))
    _ ≤ c*(sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*(∫ t in S,t^(-s-1)*Real.exp (-‖x-y‖^2/(8*t^2)))) := mul_le_mul_of_nonneg_left hB hc
    _ = _ := by ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszGaussian_scale_integral_transport_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_scale_integral_transport_bound
