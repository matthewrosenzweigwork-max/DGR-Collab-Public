import DGRHS.Commutator.SourceRieszTruncatedTransportKernelScaleIntegral

/-! The actual all-order scale-integral derivative identity, by successive
proper dominated differentiation. No derivative interchange is assumed. -/
noncomputable section
open MeasureTheory Set Metric
open scoped Topology
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
-- Explicit local instances select the existing native operator-norm topologies.
-- They change neither the norm nor any imported instance declaration.
local instance (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance (n : ℕ) : UniformSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace
local instance (n : ℕ) : TopologicalSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace
local instance (n : ℕ) : AddCommMonoid (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toAddCommMonoid
local instance (n : ℕ) : Module ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedSpace ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toModule


lemma sourceRieszGaussian_iteratedFDeriv_scale_integral (n : ℕ) (c s : ℝ) (S : Set ℝ)
    (hSm : MeasurableSet S) (hS : S⊆Ioi 0) (hs : 0<s) {z : E} (hz : z≠0) :
    iteratedFDeriv ℝ n (fun y : E=>c*(∫ t in S,t^(-s-1)*sourceRieszGaussianScale t y)) z =
      c • ∫ t in S,t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z := by
  induction n generalizing z with
  | zero =>
    ext m
    rw [iteratedFDeriv_zero_apply,smul_apply,
      ContinuousMultilinearMap.integral_apply (integrable_sourceRieszGaussian_scale_on 0 s S hSm hS hs hz)]
    simp only [smul_apply,iteratedFDeriv_zero_apply,smul_eq_mul]
  | succ n IH =>
    have he : iteratedFDeriv ℝ n (fun y : E=>c*(∫ t in S,t^(-s-1)*sourceRieszGaussianScale t y)) =ᶠ[𝓝 z]
        (fun y : E=>c • ∫ t in S,t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y) := by
      filter_upwards [eventually_ne_nhds hz] with y hy
      exact IH hy
    have hf := (hasFDerivAt_sourceRieszGaussian_scale_integral n s S hSm hS hs hz).const_smul c
    change HasFDerivAt
      (fun y : E=>c • ∫ t in S,t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y)
      (c • ∫ t in S,t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t)) z) z at hf
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,he.fderiv_eq,hf.fderiv,map_smul]
    let U := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1)=>E) ℝ).symm
    have hc := U.toContinuousLinearEquiv.integral_comp_comm
      (μ:=volume.restrict S) (fun t : ℝ=>t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E→ℝ)) z)
    change (∫ t in S,U (t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E→ℝ)) z)) =
      U (∫ t in S,t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E→ℝ)) z) at hc
    change c • U (∫ t in S,t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E→ℝ)) z) = _
    rw [←hc]
    congr 1

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_scale_integral
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_scale_integral
