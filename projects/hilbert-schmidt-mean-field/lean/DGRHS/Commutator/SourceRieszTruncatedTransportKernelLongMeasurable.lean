import DGRHS.Commutator.SourceRieszTruncatedTransportKernelLongBound

/-! All-order measurable and symmetric collision-zero long transport kernel.
Continuity off the collision is derived from the actual scale integral. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
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


def sourceRieszLongTransportKernel (n : ℕ) (s η : ℝ) (v : E→E) (p : E×E) : ℝ :=
  if p.1=p.2 then 0 else
    iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (p.1-p.2) (fun _=>v p.1-v p.2)

lemma continuousAt_sourceRieszLongRange_iteratedFDeriv (s η : ℝ) (n : ℕ)
    (hs : 0<s) (hη : 0<η) {z : E} (hz : z≠0) :
    ContinuousAt (iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η)) z := by
  have hf := (hasFDerivAt_sourceRieszGaussian_scale_integral n s (Ioi η)
    measurableSet_Ioi (Ioi_subset_Ioi hη.le) hs hz).continuousAt.const_smul
      (DGRHS.Gaussian.gaussianRieszSourceCoefficient s)
  have he : (iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η)) =ᶠ[𝓝 z]
      (fun y : E=>DGRHS.Gaussian.gaussianRieszSourceCoefficient s •
        ∫ t in Ioi η,t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y) :=
    (eventually_ne_nhds hz).mono (fun y hy=>sourceRieszLongRange_iteratedFDeriv_formula n s η hs hη hy)
  exact (continuousAt_congr he).mpr hf

lemma sourceRieszLongRange_iteratedFDeriv_neg (s η : ℝ) (n : ℕ) (z : E) (w : Fin n→E) :
    iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (-z) (fun i=>-w i)=
      iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) z w := by
  let g : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E (-1:ℝ) (by norm_num)).toContinuousLinearEquiv
  have hg : ∀ u,g u=-u := by intro u;change (-1:ℝ) • u=-u;simp
  have he : (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η ∘ g)=
      DGRHS.Gaussian.gaussianRieszEuclideanTruncation (ι:=ι) s η := by
    funext u
    simp [Function.comp_apply,hg,DGRHS.Gaussian.gaussianRieszEuclideanTruncation]
  have hc : iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η ∘ g) z=
      (iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (g z)).compContinuousLinearMap
        (fun _=>g.toContinuousLinearMap) := by
    simpa only [preimage_univ,iteratedFDerivWithin_univ] using
      g.iteratedFDerivWithin_comp_right (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) uniqueDiffOn_univ (mem_univ z) n
  rw [he] at hc
  have hm := congrArg (fun F : E [×n]→L[ℝ] ℝ=>F w) hc
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply,hg] using hm.symm

lemma sourceRieszLongTransportKernel_all_order_symmetric (s η : ℝ) (n : ℕ) (v : E→E) (p : E×E) :
    sourceRieszLongTransportKernel n s η v p.swap=sourceRieszLongTransportKernel n s η v p := by
  classical
  by_cases hp : p.1=p.2
  · simp [sourceRieszLongTransportKernel,hp]
  have hp' : p.2≠p.1 := Ne.symm hp
  simp only [sourceRieszLongTransportKernel,Prod.fst_swap,Prod.snd_swap,ite_eq_right hp,ite_eq_right hp']
  simpa only [neg_sub] using sourceRieszLongRange_iteratedFDeriv_neg s η n (p.1-p.2) (fun _=>v p.1-v p.2)

lemma measurable_sourceRieszLongTransportKernel_all_order (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    Measurable (sourceRieszLongTransportKernel n s η v) := by
  classical
  let d : Set (E×E) := {p |p.1=p.2}
  let f : E×E→ℝ := fun p=>iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (p.1-p.2) (fun _=>v p.1-v p.2)
  have hf : ContinuousOn f dᶜ := by
    intro p hp
    have hp' : p.1≠p.2 := hp
    have hz : p.1-p.2≠0 := sub_ne_zero.mpr hp'
    have hd : ContinuousAt (fun q : E×E=>iteratedFDeriv ℝ n (DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η) (q.1-q.2)) p :=
      (continuousAt_sourceRieszLongRange_iteratedFDeriv s η n hs hη hz).comp (f := fun q : E×E=>q.1-q.2)
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
lemma sourceRieszLongTransportKernel_all_order_bound (n : ℕ) (s η : ℝ)
    (hs : 0<s) (hη : 0<η) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (p : E×E) :
    |sourceRieszLongTransportKernel n s η v p| ≤
      (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*
        DGRHS.Gaussian.gaussianRieszEuclideanTruncation s η (p.1-p.2) := by
  unfold sourceRieszLongTransportKernel
  split_ifs with hp
  · simp only [abs_zero]
    exact mul_nonneg (by have h:=sourceRieszGaussianDerivativeConstant_pos n;positivity)
      (DGRHS.Gaussian.gaussianRieszEuclideanTruncation_nonneg s η hs hη _)
  · exact sourceRieszLongRange_all_order_transport_bound n s η hs hη hv hp

end DGRHS.Commutator
#check DGRHS.Commutator.continuousAt_sourceRieszLongRange_iteratedFDeriv
#print axioms DGRHS.Commutator.continuousAt_sourceRieszLongRange_iteratedFDeriv
#check DGRHS.Commutator.sourceRieszLongRange_iteratedFDeriv_neg
#print axioms DGRHS.Commutator.sourceRieszLongRange_iteratedFDeriv_neg
#check DGRHS.Commutator.sourceRieszLongTransportKernel_all_order_symmetric
#print axioms DGRHS.Commutator.sourceRieszLongTransportKernel_all_order_symmetric
#check DGRHS.Commutator.measurable_sourceRieszLongTransportKernel_all_order
#print axioms DGRHS.Commutator.measurable_sourceRieszLongTransportKernel_all_order
#check DGRHS.Commutator.sourceRieszLongTransportKernel
#print axioms DGRHS.Commutator.sourceRieszLongTransportKernel
#check DGRHS.Commutator.sourceRieszLongTransportKernel_all_order_bound
#print axioms DGRHS.Commutator.sourceRieszLongTransportKernel_all_order_bound
