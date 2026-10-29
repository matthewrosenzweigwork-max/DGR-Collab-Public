import DGRHS.Commutator.SourceRieszTruncatedTransportKernelGaussianIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual dominated differentiation of Gaussian derivative scale integrals on
any measurable positive-scale restriction. Both short and long profiles qualify. -/
noncomputable section
open MeasureTheory Set Metric
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

lemma sourceRieszGaussian_derivative_scale_continuousOn (n : ℕ) (s : ℝ) (S : Set ℝ)
    (hS : S⊆Ioi 0) (z : E) :
    ContinuousOn (fun t : ℝ=>t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z) S := by
  have hD : Continuous (iteratedFDeriv ℝ n (sourceRieszGaussianScale 1 : E→ℝ)) :=
    (contDiff_sourceRieszGaussianScale n 1).continuous_iteratedFDeriv le_rfl
  apply ContinuousOn.congr (f:=fun t : ℝ=>t^(-s-1) • ((t⁻¹)^n • iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z))) _
    (fun t ht=>by rw [sourceRieszGaussian_iteratedFDeriv_scale_eq n t (hS ht)])
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have ht0 : t≠0 := (hS ht).ne'
  have harg : ContinuousAt (fun u : ℝ=>u⁻¹ • z) t := by fun_prop (disch:=aesop)
  exact (by fun_prop (disch:=aesop) : ContinuousAt (fun u : ℝ=>u^(-s-1)) t).smul
    ((by fun_prop (disch:=aesop) : ContinuousAt (fun u : ℝ=>(u⁻¹)^n) t).smul (hD.continuousAt.comp harg))

lemma integrable_sourceRieszGaussian_scale_majorant_on (n : ℕ) (s : ℝ) (S : Set ℝ)
    (hS : S⊆Ioi 0) (hs : 0<s) {z : E} (hz : z≠0) :
    Integrable (fun t : ℝ=>sourceRieszGaussianDerivativeConstant n*t^(-(s+n)-1)*Real.exp (-‖z‖^2/(32*t^2))) (volume.restrict S) := by
  have hi := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale (s+n) (‖z‖^2/32)
    (by positivity) (by have h:=norm_pos_iff.mpr hz;positivity)).mono_set hS
  convert hi.const_mul (sourceRieszGaussianDerivativeConstant n) using 1
  ext t
  have he : -‖z‖^2/(32*t^2)=-(‖z‖^2/32)/t^2 := by ring
  rw [he]
  ring

lemma integrable_sourceRieszGaussian_scale_on (n : ℕ) (s : ℝ) (S : Set ℝ)
    (hSm : MeasurableSet S) (hS : S⊆Ioi 0) (hs : 0<s) {z : E} (hz : z≠0) :
    Integrable (fun t : ℝ=>t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z) (volume.restrict S) := by
  have ht : ∀ᵐ t ∂(volume.restrict S),t∈S := self_mem_ae_restrict hSm
  exact (integrable_sourceRieszGaussian_scale_majorant_on n s S hS hs hz).mono'
    ((sourceRieszGaussian_derivative_scale_continuousOn n s S hS z).aestronglyMeasurable hSm)
    (ht.mono (fun t ht=>sourceRieszGaussian_iteratedFDeriv_local_scale_bound n s t (hS ht)
      (by simpa only [mem_ball,dist_self] using half_pos (norm_pos_iff.mpr hz))))

lemma integrable_sourceRieszGaussian_scale_fderiv_on (n : ℕ) (s : ℝ) (S : Set ℝ)
    (hSm : MeasurableSet S) (hS : S⊆Ioi 0) (hs : 0<s) {z : E} (hz : z≠0) :
    Integrable (fun t : ℝ=>t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E→ℝ)) z) (volume.restrict S) := by
  let C : (E [×(n+1)]→L[ℝ] ℝ) →L[ℝ] (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1)=>E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hc : ContinuousOn (fun t : ℝ=>t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E→ℝ)) z) S := by
    have hc0 := C.continuous.comp_continuousOn (sourceRieszGaussian_derivative_scale_continuousOn (n+1) s S hS z)
    apply hc0.congr
    intro t ht
    dsimp only [Function.comp_apply]
    rw [map_smul]
    rfl
  have ht : ∀ᵐ t ∂(volume.restrict S),t∈S := self_mem_ae_restrict hSm
  exact (integrable_sourceRieszGaussian_scale_majorant_on (n+1) s S hS hs hz).mono'
    (hc.aestronglyMeasurable hSm) (ht.mono (fun t ht=>by
      simpa only [norm_smul,norm_fderiv_iteratedFDeriv] using
        sourceRieszGaussian_iteratedFDeriv_local_scale_bound (n+1) s t (hS ht) (z:=z) (y:=z)
          (by simpa only [mem_ball,dist_self] using half_pos (norm_pos_iff.mpr hz))))

lemma hasFDerivAt_sourceRieszGaussian_scale_integral (n : ℕ) (s : ℝ) (S : Set ℝ)
    (hSm : MeasurableSet S) (hS : S⊆Ioi 0) (hs : 0<s) {z : E} (hz : z≠0) :
    HasFDerivAt (fun y : E=>∫ t in S,t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y)
      (∫ t in S,t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t)) z) z := by
  have ht : ∀ᵐ t ∂(volume.restrict S),t∈S := self_mem_ae_restrict hSm
  have hdiff (t : ℝ) : Differentiable ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t : E→ℝ)) :=
    (contDiff_sourceRieszGaussianScale (n+1) t).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F:=fun y (t : ℝ)=>t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y)
    (F':=fun y (t : ℝ)=>t^(-s-1) • fderiv ℝ (iteratedFDeriv ℝ n (sourceRieszGaussianScale t)) y)
    (bound:=fun t : ℝ=>sourceRieszGaussianDerivativeConstant (n+1)*t^(-(s+(n+1))-1)*Real.exp (-‖z‖^2/(32*t^2)))
    (μ:=volume.restrict S) (ball_mem_nhds z (half_pos (norm_pos_iff.mpr hz)))
    (Filter.Eventually.of_forall (fun y=>(sourceRieszGaussian_derivative_scale_continuousOn n s S hS y).aestronglyMeasurable hSm))
    (integrable_sourceRieszGaussian_scale_on n s S hSm hS hs hz)
    (integrable_sourceRieszGaussian_scale_fderiv_on n s S hSm hS hs hz).aestronglyMeasurable
    ?_ (by simpa only [Nat.cast_add,Nat.cast_one] using integrable_sourceRieszGaussian_scale_majorant_on (n+1) s S hS hs hz) ?_
  · apply ht.mono
    intro t ht y hy
    have h := sourceRieszGaussian_iteratedFDeriv_local_scale_bound (n+1) s t (hS ht) hy
    simpa only [norm_smul,norm_fderiv_iteratedFDeriv,Nat.cast_add,Nat.cast_one] using h
  · exact ht.mono (fun t ht y _=>(hdiff t).differentiableAt.hasFDerivAt.const_smul (t^(-s-1)))

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszGaussian_derivative_scale_continuousOn
#print axioms DGRHS.Commutator.sourceRieszGaussian_derivative_scale_continuousOn
#check @DGRHS.Commutator.integrable_sourceRieszGaussian_scale_majorant_on
#print axioms DGRHS.Commutator.integrable_sourceRieszGaussian_scale_majorant_on
#check @DGRHS.Commutator.integrable_sourceRieszGaussian_scale_on
#print axioms DGRHS.Commutator.integrable_sourceRieszGaussian_scale_on
#check @DGRHS.Commutator.integrable_sourceRieszGaussian_scale_fderiv_on
#print axioms DGRHS.Commutator.integrable_sourceRieszGaussian_scale_fderiv_on
#check @DGRHS.Commutator.hasFDerivAt_sourceRieszGaussian_scale_integral
#print axioms DGRHS.Commutator.hasFDerivAt_sourceRieszGaussian_scale_integral
