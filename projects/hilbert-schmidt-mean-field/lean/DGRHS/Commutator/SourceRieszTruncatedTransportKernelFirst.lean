import DGRHS.Commutator.SourceRieszTruncatedTransportKernelBound
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Collision-zero first transport contraction of the actual short profile. -/
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal RealInnerProductSpace
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

def sourceRieszShortTransportKernel (n : ℕ) (s η : ℝ)
    (v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) : ℝ := by
  classical
  exact if p.1=p.2 then 0 else iteratedFDeriv ℝ n
    (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η) (p.1-p.2) (fun _=>v p.1-v p.2)

lemma sourceRieszShortRange_fderiv_formula (s η : ℝ) (hs : 0<s) (hη : 0<η)
    {z : EuclideanSpace ℝ ι} (hz : z≠0) :
    fderiv ℝ (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η) z =
      (-(DGRHS.Gaussian.gaussianRieszSourceCoefficient s /
        DGRHS.Gaussian.gaussianRieszSourceCoefficient (s+2))*
          DGRHS.Gaussian.gaussianRieszEuclideanShortRange (s+2) η z) • innerSL ℝ z := by
  have hF := (hasFDerivAt_sourceRieszShortRange s η hs hη hz).fderiv
  have hAE : (fun t : ℝ=>t^(-s-1) • sourceRieszGaussianScaleDerivative t z) =ᵐ[volume.restrict (Ioc 0 η)]
      (fun t=>-(t^(-(s+2)-1)*sourceRieszGaussianScale t z) • innerSL ℝ z) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have hp : t^(-s-1)/t^2=t^(-(s+2)-1) := by
      rw [←Real.rpow_two,←Real.rpow_sub ht.1]
      congr 1
      ring
    unfold sourceRieszGaussianScaleDerivative
    rw [smul_smul]
    congr 1
    rw [←hp]
    ring
  rw [hF,integral_congr_ae hAE,integral_smul_const,integral_neg,smul_smul]
  unfold DGRHS.Gaussian.gaussianRieszEuclideanShortRange
  simp only [sourceRieszGaussianScale]
  congr 1
  have hc : DGRHS.Gaussian.gaussianRieszSourceCoefficient (s+2)≠0 :=
    (DGRHS.Gaussian.gaussianRieszSourceCoefficient_pos (s+2) (by linarith)).ne'
  field_simp

lemma sourceRieszShortTransportKernel_first_bound (s η : ℝ) (hs : 0<s) (hη : 0<η)
    {K : ℝ≥0} {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
    |sourceRieszShortTransportKernel 1 s η v p| ≤
      (4*(2:ℝ)^s)*(K:ℝ)*DGRHS.Gaussian.gaussianRieszEuclideanShortRange s (2*η) (p.1-p.2) := by
  classical
  by_cases hp : p.1=p.2
  · simp only [sourceRieszShortTransportKernel,if_pos hp,abs_zero]
    exact mul_nonneg (by positivity) (DGRHS.Gaussian.gaussianRieszEuclideanShortRange_nonneg s (2*η) hs _)
  · simp only [sourceRieszShortTransportKernel,if_neg hp,iteratedFDeriv_one_apply]
    exact sourceRieszShortRange_fderiv_transport_bound s η hs hη hv hp

lemma measurable_sourceRieszShortTransportKernel_first (s η : ℝ) (hs : 0<s) (hη : 0<η)
    {K : ℝ≥0} {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v) :
    Measurable (sourceRieszShortTransportKernel 1 s η v) := by
  classical
  let E := EuclideanSpace ℝ ι
  let d : Set (E×E) := {p|p.1=p.2}
  let c : ℝ := -(DGRHS.Gaussian.gaussianRieszSourceCoefficient s /
    DGRHS.Gaussian.gaussianRieszSourceCoefficient (s+2))
  let f : E×E→ℝ := fun p=>c*DGRHS.Gaussian.gaussianRieszEuclideanShortRange (s+2) η (p.1-p.2)*⟪p.1-p.2,v p.1-v p.2⟫
  have hd : MeasurableSet d := (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hf : ContinuousOn f dᶜ := by
    intro p hp
    have hp' : p.1-p.2≠0 := sub_ne_zero.mpr hp
    have hS : ContinuousAt (fun q : E×E=>DGRHS.Gaussian.gaussianRieszEuclideanShortRange (s+2) η (q.1-q.2)) p :=
      ((hasFDerivAt_sourceRieszShortRange (s+2) η (by linarith) hη hp').continuousAt).comp
        (f:=fun q : E×E=>q.1-q.2) (continuous_fst.sub continuous_snd).continuousAt
    have hV : Continuous (fun q : E×E=>v q.1-v q.2) := (hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)
    apply ContinuousAt.continuousWithinAt
    dsimp [f]
    fun_prop
  have h0 : ContinuousOn (fun _ : E×E=>(0:ℝ)) d := continuousOn_const
  have hm := h0.measurable_piecewise hf hd
  convert hm using 1
  ext p
  by_cases hp : p.1=p.2
  · simp [sourceRieszShortTransportKernel,d,hp]
  · simp only [sourceRieszShortTransportKernel,if_neg hp,iteratedFDeriv_one_apply]
    rw [sourceRieszShortRange_fderiv_formula s η hs hη (sub_ne_zero.mpr hp)]
    simp [d,f,c,hp,smul_apply,smul_eq_mul,inner_sub_left]
end DGRHS.Commutator
#check DGRHS.Commutator.sourceRieszShortTransportKernel
#print axioms DGRHS.Commutator.sourceRieszShortTransportKernel
#check DGRHS.Commutator.sourceRieszShortRange_fderiv_formula
#print axioms DGRHS.Commutator.sourceRieszShortRange_fderiv_formula
#check DGRHS.Commutator.sourceRieszShortTransportKernel_first_bound
#print axioms DGRHS.Commutator.sourceRieszShortTransportKernel_first_bound
#check DGRHS.Commutator.measurable_sourceRieszShortTransportKernel_first
#print axioms DGRHS.Commutator.measurable_sourceRieszShortTransportKernel_first
