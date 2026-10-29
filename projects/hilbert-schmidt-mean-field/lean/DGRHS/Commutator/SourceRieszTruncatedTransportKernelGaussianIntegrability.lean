import DGRHS.Commutator.SourceRieszTruncatedTransportKernelGaussianScaleBounds
import DGRHS.Commutator.SourceRieszTruncatedTransportKernelDerivative

/-! Proper all-order local scale-integral bounds, obtained from actual Gaussian
derivatives. The short profile itself is not differentiated in this module. -/
noncomputable section
open MeasureTheory Set Metric
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sourceRieszGaussian_iteratedFDeriv_scale_eq (n : ℕ) (t : ℝ) (ht : 0<t) (z : E) :
    iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z =
      (t⁻¹)^n • iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z) := by
  let g : E→L[ℝ] E := t⁻¹ • ContinuousLinearMap.id ℝ E
  have hg : ∀ y : E,g y=t⁻¹ • y := by intro y;rfl
  have he : sourceRieszGaussianScale t=(sourceRieszGaussianScale 1 ∘ g : E→ℝ) := by
    ext y
    simp only [Function.comp_apply,hg,sourceRieszGaussianScale,norm_smul,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
    congr 1
    field_simp
  rw [he,g.iteratedFDeriv_comp_right (contDiff_sourceRieszGaussianScale n 1) z le_rfl]
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hg,
    ContinuousMultilinearMap.smul_apply]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)).map_smul_univ (fun _=>t⁻¹) m

lemma sourceRieszGaussian_iteratedFDeriv_weight_continuousOn (n : ℕ) (s η : ℝ) (z : E) :
    ContinuousOn (fun t : ℝ=>t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z) (Ioc 0 η) := by
  have hD : Continuous (iteratedFDeriv ℝ n (sourceRieszGaussianScale 1 : E→ℝ)) :=
    (contDiff_sourceRieszGaussianScale n 1).continuous_iteratedFDeriv le_rfl
  apply ContinuousOn.congr (f:=fun t : ℝ=>t^(-s-1) • ((t⁻¹)^n • iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z))) _
    (fun t ht=>by rw [sourceRieszGaussian_iteratedFDeriv_scale_eq n t ht.1])
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have ht0 : t≠0 := ht.1.ne'
  have harg : ContinuousAt (fun u : ℝ=>u⁻¹ • z) t := by fun_prop (disch:=aesop)
  exact (by fun_prop (disch:=aesop) : ContinuousAt (fun u : ℝ=>u^(-s-1)) t).smul
    ((by fun_prop (disch:=aesop) : ContinuousAt (fun u : ℝ=>(u⁻¹)^n) t).smul (hD.continuousAt.comp harg))

lemma sourceRieszGaussian_iteratedFDeriv_local_scale_bound (n : ℕ) (s t : ℝ) (ht : 0<t)
    {z y : E} (hy : y∈ball z (‖z‖/2)) :
    ‖t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) y‖ ≤
      sourceRieszGaussianDerivativeConstant n*t^(-(s+n)-1)*Real.exp (-‖z‖^2/(32*t^2)) := by
  have hd : ‖y-z‖<‖z‖/2 := by simpa only [mem_ball,dist_eq_norm] using hy
  have h1 : ‖z‖≤‖y‖+‖y-z‖ := by
    calc
      _ = ‖y-(y-z)‖ := by congr 1;abel
      _ ≤ _ := norm_sub_le _ _
  have hlo : ‖z‖/2≤‖y‖ := by linarith
  have he : Real.exp (-‖y‖^2/(8*t^2))≤Real.exp (-‖z‖^2/(32*t^2)) := by
    apply Real.exp_le_exp.mpr
    have heq : -‖z‖^2/(32*t^2)=-(‖z‖^2/4)/(8*t^2) := by ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right (by positivity : 0<8*t^2)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (show 0≤‖y‖+‖z‖/2 by positivity)]
  have hp : t^(-s-1)*(t⁻¹)^n=t^(-(s+n)-1) := by
    rw [inv_pow,←Real.rpow_natCast,←Real.rpow_neg ht.le,←Real.rpow_add ht]
    congr 1
    ring
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  calc
    _ ≤ t^(-s-1)*((t⁻¹)^n*sourceRieszGaussianDerivativeConstant n*Real.exp (-‖y‖^2/(8*t^2))) := mul_le_mul_of_nonneg_left (sourceRieszGaussian_iteratedFDeriv_unweighted_bound n t ht y) (Real.rpow_nonneg ht.le _)
    _ ≤ t^(-s-1)*((t⁻¹)^n*sourceRieszGaussianDerivativeConstant n*Real.exp (-‖z‖^2/(32*t^2))) := by
      gcongr
      exact mul_nonneg (by positivity) (sourceRieszGaussianDerivativeConstant_pos n).le
    _ = _ := by rw [←hp];ring

lemma integrable_sourceRieszGaussian_all_order_local_majorant (n : ℕ) (s η : ℝ) (hs : 0<s)
    {z : E} (hz : z≠0) :
    Integrable (fun t : ℝ=>sourceRieszGaussianDerivativeConstant n*t^(-(s+n)-1)*Real.exp (-‖z‖^2/(32*t^2))) (volume.restrict (Ioc 0 η)) := by
  have hi := (DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale (s+n) (‖z‖^2/32)
    (by positivity) (by have h:=norm_pos_iff.mpr hz;positivity)).mono_set (s:=Ioc 0 η) Ioc_subset_Ioi_self
  convert hi.const_mul (sourceRieszGaussianDerivativeConstant n) using 1
  ext t
  have he : -‖z‖^2/(32*t^2)=-(‖z‖^2/32)/t^2 := by ring
  rw [he]
  ring

lemma integrable_sourceRieszGaussian_all_order_scale (n : ℕ) (s η : ℝ) (hs : 0<s)
    {z : E} (hz : z≠0) :
    Integrable (fun t : ℝ=>t^(-s-1) • iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z) (volume.restrict (Ioc 0 η)) := by
  have ht : ∀ᵐ t ∂(volume.restrict (Ioc 0 η)),t∈Ioc 0 η := self_mem_ae_restrict measurableSet_Ioc
  exact (integrable_sourceRieszGaussian_all_order_local_majorant n s η hs hz).mono'
    ((sourceRieszGaussian_iteratedFDeriv_weight_continuousOn n s η z).aestronglyMeasurable measurableSet_Ioc)
    (ht.mono (fun t ht=>sourceRieszGaussian_iteratedFDeriv_local_scale_bound n s t ht.1
      (by simpa only [mem_ball,dist_self] using half_pos (norm_pos_iff.mpr hz))))

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_scale_eq
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_scale_eq
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_weight_continuousOn
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_weight_continuousOn
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_local_scale_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_local_scale_bound
#check @DGRHS.Commutator.integrable_sourceRieszGaussian_all_order_local_majorant
#print axioms DGRHS.Commutator.integrable_sourceRieszGaussian_all_order_local_majorant
#check @DGRHS.Commutator.integrable_sourceRieszGaussian_all_order_scale
#print axioms DGRHS.Commutator.integrable_sourceRieszGaussian_all_order_scale
