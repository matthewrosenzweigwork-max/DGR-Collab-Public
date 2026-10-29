import DGRHS.Commutator.SourceRieszTruncatedTransportKernelScale
import DGRHS.Gaussian.RieszGaussianTruncationComparison
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Proper dominated first differentiation of the actual short Riesz scale
integral away from zero; neighborhood domination is derived, not assumed. -/
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sourceRieszGaussianScaleDerivative_norm (t : ℝ) (z : E) :
    ‖sourceRieszGaussianScaleDerivative t z‖ =
      sourceRieszGaussianScale t z/t^2*‖z‖ := by
  simp only [sourceRieszGaussianScaleDerivative,norm_smul,Real.norm_eq_abs,abs_neg,
    abs_div,sourceRieszGaussianScale,abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (sq_nonneg t),innerSL_apply_norm]

lemma sourceRieszGaussianScaleDerivative_local_bound (s t : ℝ) (ht : 0<t)
    {z y : E} (hy : y∈ball z (‖z‖/2)) :
    ‖t^(-s-1) • sourceRieszGaussianScaleDerivative t y‖ ≤
      (3*‖z‖/2)*t^(-(s+2)-1)*Real.exp (-‖z‖^2/(8*t^2)) := by
  have hd : ‖y-z‖<‖z‖/2 := by simpa only [mem_ball,dist_eq_norm] using hy
  have h1 : ‖z‖≤‖y‖+‖y-z‖ := by
    calc
      _ = ‖y-(y-z)‖ := by congr 1;abel
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖y‖≤‖z‖+‖y-z‖ := by
    calc
      _ = ‖z+(y-z)‖ := by congr 1;abel
      _ ≤ _ := norm_add_le _ _
  have hlo : ‖z‖/2≤‖y‖ := by linarith
  have hhi : ‖y‖≤3*‖z‖/2 := by linarith
  have he : Real.exp (-‖y‖^2/(2*t^2)) ≤ Real.exp (-‖z‖^2/(8*t^2)) := by
    apply Real.exp_le_exp.mpr
    have heq : -‖z‖^2/(8*t^2) = -(‖z‖^2/4)/(2*t^2) := by ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right (by positivity : 0<2*t^2)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (show 0≤‖y‖+‖z‖/2 by positivity)]
  have hp : t^(-s-1)/t^2=t^(-(s+2)-1) := by
    rw [←Real.rpow_two,←Real.rpow_sub ht]
    congr 1
    ring
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg ht.le _),
    sourceRieszGaussianScaleDerivative_norm,sourceRieszGaussianScale]
  calc
    _ ≤ t^(-s-1)*(Real.exp (-‖z‖^2/(8*t^2))/t^2*(3*‖z‖/2)) := by
      gcongr
    _ = _ := by rw [←hp];ring

lemma sourceRieszGaussianScale_weight_continuousOn (s η : ℝ) (z : E) :
    ContinuousOn (fun t : ℝ=>t^(-s-1)*sourceRieszGaussianScale t z) (Ioc 0 η) := by
  intro t ht
  have ht0 : t≠0 := ht.1.ne'
  apply ContinuousAt.continuousWithinAt
  unfold sourceRieszGaussianScale
  have ht2 : t^2≠0 := pow_ne_zero 2 ht0
  fun_prop (disch := aesop)

lemma sourceRieszGaussianScale_derivative_weight_continuousOn (s η : ℝ) (z : E) :
    ContinuousOn (fun t : ℝ=>t^(-s-1) • sourceRieszGaussianScaleDerivative t z) (Ioc 0 η) := by
  intro t ht
  have ht0 : t≠0 := ht.1.ne'
  apply ContinuousAt.continuousWithinAt
  unfold sourceRieszGaussianScaleDerivative sourceRieszGaussianScale
  have ht2 : t^2≠0 := pow_ne_zero 2 ht0
  fun_prop (disch := aesop)

lemma hasFDerivAt_sourceRieszShortRange {ι : Type*} [Fintype ι]
    (s η : ℝ) (hs : 0<s) (hη : 0<η) {z : EuclideanSpace ℝ ι} (hz : z≠0) :
    HasFDerivAt (DGRHS.Gaussian.gaussianRieszEuclideanShortRange s η)
      (DGRHS.Gaussian.gaussianRieszSourceCoefficient s •
        ∫ t in Ioc 0 η,t^(-s-1) • sourceRieszGaussianScaleDerivative t z) z := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 η)
  have hb : Integrable (fun t : ℝ=>(3*‖z‖/2)*t^(-(s+2)-1)*Real.exp (-‖z‖^2/(8*t^2))) μ := by
    have hi := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale (s+2) (‖z‖^2/8)
      (by linarith) (by have h:=norm_pos_iff.mpr hz;positivity)).mono_set (s:=Ioc 0 η) Ioc_subset_Ioi_self
    convert hi.const_mul (3*‖z‖/2) using 1
    ext t
    have he : -‖z‖^2/(8*t^2) = -(‖z‖^2/8)/t^2 := by ring
    rw [he]
    ring
  have hi : Integrable (fun t : ℝ=>t^(-s-1)*sourceRieszGaussianScale t z) μ := by
    exact (DGRHS.Gaussian.integrableOn_gaussianRieszEuclidean_full_scale s hs z hz).mono_set Ioc_subset_Ioi_self
  have ht : ∀ᵐ t ∂μ,t∈Ioc 0 η := self_mem_ae_restrict measurableSet_Ioc
  have hf := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F:=fun y (t : ℝ)=>t^(-s-1)*sourceRieszGaussianScale t y)
    (F':=fun y (t : ℝ)=>t^(-s-1) • sourceRieszGaussianScaleDerivative t y)
    (bound:=fun t : ℝ=>(3*‖z‖/2)*t^(-(s+2)-1)*Real.exp (-‖z‖^2/(8*t^2)))
    (μ:=μ) (ball_mem_nhds z (by exact half_pos (norm_pos_iff.mpr hz)))
    (Filter.Eventually.of_forall (fun y=>(sourceRieszGaussianScale_weight_continuousOn s η y).aestronglyMeasurable measurableSet_Ioc))
    hi ((sourceRieszGaussianScale_derivative_weight_continuousOn s η z).aestronglyMeasurable measurableSet_Ioc)
    (ht.mono (fun t ht y hy=>sourceRieszGaussianScaleDerivative_local_bound s t ht.1 hy)) hb
    (ht.mono (fun t ht y _=>(hasFDerivAt_sourceRieszGaussianScale t ht.1.ne' y).const_mul (t^(-s-1))))
  exact hf.const_mul (DGRHS.Gaussian.gaussianRieszSourceCoefficient s)
end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszGaussianScaleDerivative_norm
#print axioms DGRHS.Commutator.sourceRieszGaussianScaleDerivative_norm
#check @DGRHS.Commutator.sourceRieszGaussianScaleDerivative_local_bound
#print axioms DGRHS.Commutator.sourceRieszGaussianScaleDerivative_local_bound
#check @DGRHS.Commutator.sourceRieszGaussianScale_weight_continuousOn
#print axioms DGRHS.Commutator.sourceRieszGaussianScale_weight_continuousOn
#check @DGRHS.Commutator.sourceRieszGaussianScale_derivative_weight_continuousOn
#print axioms DGRHS.Commutator.sourceRieszGaussianScale_derivative_weight_continuousOn
#check @DGRHS.Commutator.hasFDerivAt_sourceRieszShortRange
#print axioms DGRHS.Commutator.hasFDerivAt_sourceRieszShortRange
