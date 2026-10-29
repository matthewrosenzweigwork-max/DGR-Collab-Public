import DGRHS.Commutator.SourceLogGaussianShortDerivative
import DGRHS.Gaussian.GaussianLogShortRangeSource

/-! Coefficient-one Gaussian LOG short kernel, with collision value zero.
Continuity, measurability and symmetry are derived from the checked actual
finite-Ioc derivative, not assumed. Generic all orders support source n>=1. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
-- Explicit local instances select the existing native operator-norm topologies.
-- They change neither the norm nor any imported instance declaration.
local instance sourceLogGaussianShortNative1 (n : ℕ) : AddCommMonoid (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toAddCommMonoid
local instance sourceLogGaussianShortNative2 (n : ℕ) : Module ℝ (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E [×n]→L[ℝ] ℝ)).toModule
local instance sourceLogGaussianShortNative3 (n : ℕ) : UniformSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace
local instance sourceLogGaussianShortNative4 (n : ℕ) : TopologicalSpace (E [×n]→L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E [×n]→L[ℝ] ℝ)).toUniformSpace.toTopologicalSpace
local instance sourceLogGaussianShortNative5 (n : ℕ) : UniformSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace
local instance sourceLogGaussianShortNative6 (n : ℕ) : TopologicalSpace (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toUniformSpace.toTopologicalSpace
local instance sourceLogGaussianShortNative7 (n : ℕ) : AddCommMonoid (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedAddCommGroup (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toAddCommMonoid
local instance sourceLogGaussianShortNative8 (n : ℕ) : Module ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
  (inferInstance : NormedSpace ℝ (E→L[ℝ] (E [×n]→L[ℝ] ℝ))).toModule


def sourceLogGaussianShortTransportKernel (n : ℕ) (η : ℝ) (v : E→E) (p : E×E) : ℝ := by
  classical
  exact if p.1=p.2 then 0 else
    iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) (p.1-p.2) (fun _=>v p.1-v p.2)

lemma continuousAt_sourceLogGaussianShortRange_iteratedFDeriv (η : ℝ) (n : ℕ)
    (hη : 0<η) {z : E} (hz : z≠0) :
    ContinuousAt (iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η)) z := by
  have hf := (hasFDerivAt_sourceLogGaussian_scale_integral n η hη hz).continuousAt
  have he : (iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η)) =ᶠ[𝓝 z]
      (fun y : E=>∫ t in Ioc 0 η,t⁻¹ • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y) :=
    (eventually_ne_nhds hz).mono (fun y hy=>sourceLogShortRange_iteratedFDeriv_formula n η hη hy)
  exact (continuousAt_congr he).mpr hf

lemma sourceLogGaussianShortRange_iteratedFDeriv_neg (η : ℝ) (n : ℕ) (z : E) (w : Fin n→E) :
    iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) (-z) (fun i=>-w i)=
      iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) z w := by
  let g : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E (-1:ℝ) (by norm_num)).toContinuousLinearEquiv
  have hg : ∀ u,g u=-u := by intro u;change (-1:ℝ) • u=-u;simp
  have he : (DGRHS.Gaussian.gaussianLogShortRange η ∘ g)=
      DGRHS.Gaussian.gaussianLogShortRange (ι:=ι) η := by
    funext u
    simp [Function.comp_apply,hg,DGRHS.Gaussian.gaussianLogShortRange]
  have hc : iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η ∘ g) z=
      (iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) (g z)).compContinuousLinearMap
        (fun _=>g.toContinuousLinearMap) := by
    simpa only [preimage_univ,iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right (DGRHS.Gaussian.gaussianLogShortRange η) uniqueDiffOn_univ (mem_univ z) n
  rw [he] at hc
  have hm := congrArg (fun F : E [×n]→L[ℝ] ℝ=>F w) hc
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply,hg] using hm.symm

lemma sourceLogGaussianShortTransportKernel_symmetric (η : ℝ) (n : ℕ) (v : E→E) (p : E×E) :
    sourceLogGaussianShortTransportKernel n η v p.swap=sourceLogGaussianShortTransportKernel n η v p := by
  classical
  by_cases hp : p.1=p.2
  · simp [sourceLogGaussianShortTransportKernel,hp]
  have hp' : p.2≠p.1 := Ne.symm hp
  simp only [sourceLogGaussianShortTransportKernel,Prod.fst_swap,Prod.snd_swap,ite_eq_right hp,ite_eq_right hp']
  simpa only [neg_sub] using sourceLogGaussianShortRange_iteratedFDeriv_neg η n (p.1-p.2) (fun _=>v p.1-v p.2)

lemma measurable_sourceLogGaussianShortTransportKernel (η : ℝ) (n : ℕ) (hη : 0<η)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    Measurable (sourceLogGaussianShortTransportKernel n η v) := by
  classical
  let d : Set (E×E) := {p |p.1=p.2}
  let f : E×E→ℝ := fun p=>iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) (p.1-p.2) (fun _=>v p.1-v p.2)
  have hf : ContinuousOn f dᶜ := by
    intro p hp
    have hp' : p.1≠p.2 := hp
    have hz : p.1-p.2≠0 := sub_ne_zero.mpr hp'
    have hd : ContinuousAt (fun q : E×E=>iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianLogShortRange η) (q.1-q.2)) p :=
      (continuousAt_sourceLogGaussianShortRange_iteratedFDeriv η n hη hz).comp (f := fun q : E×E=>q.1-q.2)
        (continuous_fst.sub continuous_snd).continuousAt
    have hw : ContinuousAt (fun q : E×E=>fun _ : Fin n=>v q.1-v q.2) p :=
      (continuous_pi (fun _=>(hv.continuous.comp continuous_fst).sub
        (hv.continuous.comp continuous_snd))).continuousAt
    have heval : Continuous (fun q : (E [×n]→L[ℝ] ℝ)×(Fin n→E)=>q.1 q.2) :=
      (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] ℝ)).continuous_uncurry_of_multilinear
    exact (heval.continuousAt.comp (hd.prodMk hw)).continuousWithinAt
  have h0 : ContinuousOn (fun _ : E×E=>(0:ℝ)) d := continuous_const.continuousOn
  have hd : MeasurableSet d := (isClosed_eq continuous_fst continuous_snd).measurableSet
  change Measurable (d.piecewise (fun _=>(0:ℝ)) f)
  exact h0.measurable_piecewise hf hd

lemma sourceLogGaussianShortTransportKernel_bound (n : ℕ) (η : ℝ) (hη : 0<η)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (p : E×E) :
    |sourceLogGaussianShortTransportKernel n η v p| ≤
      sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*
        DGRHS.Gaussian.gaussianLogShortRange (2*η) (p.1-p.2) := by
  classical
  by_cases hp : p.1=p.2
  · simp only [sourceLogGaussianShortTransportKernel,ite_eq_left hp,abs_zero]
    exact mul_nonneg (mul_nonneg (sourceRieszGaussianDerivativeConstant_pos n).le
      (pow_nonneg K.coe_nonneg n)) (DGRHS.Gaussian.gaussianLogShortRange_nonneg _ _)
  · rw [sourceLogGaussianShortTransportKernel,ite_eq_right hp]
    exact sourceLogShortRange_all_order_transport_bound n η hη hv hp
end DGRHS.Commutator
