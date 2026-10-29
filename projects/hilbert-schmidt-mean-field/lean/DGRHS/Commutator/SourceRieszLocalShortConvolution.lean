/- Compatibility port of SourceRieszTruncatedTransportKernelAllOrderConvolution.lean, immutable original SHA256 88155e8b5996d68d98f025d6c8a6c196352b3fa25bbca4d1ce113c98402d3301.
Only explicit local-instance declaration names / dependency module paths differ;
public mathematical declarations renamed by recorded map; proof bodies retained. Originals unchanged. -/
import DGRHS.Commutator.SourceRieszLocalShortMeasurable
import DGRHS.Gaussian.GaussianShortRangeConvolution

/-! Proper short transport section/pair integrals and quantitative centering
at the source eta^(d-s) scale. Every fixed derivative order is covered. -/
noncomputable section
open MeasureTheory Set Real
open scoped NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

def localCompatible_sourceRieszShortTransportAllOrderPotentialBound (n : ℕ) (s η K M : ℝ) : ℝ :=
  (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*K^n*M*(DGRHS.Gaussian.gaussianRieszSourceCoefficient s *
    (2*Real.pi)^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)-s)*(2:ℝ)^((Fintype.card ι : ℝ)-s))*η^((Fintype.card ι : ℝ)-s)

lemma localCompatible_integrable_sourceRieszShortTransportKernel_all_order_row (n : ℕ) (s η : ℝ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂volume,ρ x≤M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y=>sourceRieszShortTransportKernel n s η v (x,y)) (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by
  have hC := sourceRieszGaussianDerivativeConstant_pos n
  have hi := (DGRHS.Gaussian.integrable_gaussianRieszShortRange_convolution s (2*η) (by positivity)
    (by linarith) ρ M hρ x).const_mul ((sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n)
  apply hi.mono' ((localCompatible_measurable_sourceRieszShortTransportKernel_all_order s η n hs hv).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using sourceRieszShortTransportKernel_all_order_bound n s η hs hη hv (x,y)

lemma localCompatible_sourceRieszShortTransportKernel_all_order_row_bound (n : ℕ) (s η : ℝ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M) (x : EuclideanSpace ℝ ι) :
    (∫ y,|sourceRieszShortTransportKernel n s η v (x,y)| ∂DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) ≤
      localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) n s η K M := by
  have hC := sourceRieszGaussianDerivativeConstant_pos n
  have hi := localCompatible_integrable_sourceRieszShortTransportKernel_all_order_row n s η hs hη hd hv ρ M hρ x
  have hG := DGRHS.Gaussian.integrable_gaussianRieszShortRange_convolution s (2*η) (by positivity) (by linarith) ρ M hρ x
  have hAbs : Integrable (fun y=>|sourceRieszShortTransportKernel n s η v (x,y)|) (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by simpa only [Real.norm_eq_abs] using hi.norm
  calc
    _ ≤ (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*(∫ y,DGRHS.Gaussian.gaussianRieszEuclideanShortRange s (2*η) (x-y) ∂DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by
      rw [←integral_const_mul]
      exact integral_mono_ae hAbs (hG.const_mul _) (Filter.Eventually.of_forall (fun y=>sourceRieszShortTransportKernel_all_order_bound n s η hs hη hv (x,y)))
    _ ≤ (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*(M*(DGRHS.Gaussian.gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2)/((Fintype.card ι : ℝ)-s)*(2*η)^((Fintype.card ι : ℝ)-s))) :=
      mul_le_mul_of_nonneg_left (DGRHS.Gaussian.gaussianRieszShortRange_convolution_le s (2*η) hs (by positivity) (by linarith) ρ M hM hρ x) (by positivity)
    _ = _ := by unfold localCompatible_sourceRieszShortTransportAllOrderPotentialBound;rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hη.le];ring

lemma localCompatible_integrable_sourceRieszShortTransportKernel_all_order_pair (n : ℕ) (s η : ℝ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    Integrable (sourceRieszShortTransportKernel n s η v)
      ((DGRHS.Gaussian.gaussianRieszDensityMeasure ρ).prod (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) := by
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  have hm := (localCompatible_measurable_sourceRieszShortTransportKernel_all_order s η n hs hv).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun x=>localCompatible_integrable_sourceRieszShortTransportKernel_all_order_row n s η hs hη hd hv ρ M hρ x)
  · apply (integrable_const (localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) n s η K M)).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖∫ y,‖sourceRieszShortTransportKernel n s η v (x,y)‖ ∂μ‖≤_
    rw [Real.norm_of_nonneg (integral_nonneg (fun y=>norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using localCompatible_sourceRieszShortTransportKernel_all_order_row_bound n s η hs hη hd hv ρ M hM hρ x

lemma localCompatible_sourceRieszShortTransportKernel_all_order_centered_bound (n : ℕ) (s η : ℝ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
    |DGRHS.Gaussian.hoeffdingCentered (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v) p| ≤
      (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n*DGRHS.Gaussian.gaussianRieszEuclideanShortRange s (2*η) (p.1-p.2)+
        3*localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) n s η K M := by
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  let q := sourceRieszShortTransportKernel n s η v
  let B := localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) n s η K M
  have hPair := localCompatible_integrable_sourceRieszShortTransportKernel_all_order_pair n s η hs hη hd hv ρ M hM hρ
  have hR : ∀ x,|∫ y,q (x,y) ∂μ|≤B := by
    intro x
    calc
      _ ≤ ∫ y,|q (x,y)| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y=>q (x,y))
      _ ≤ _ := localCompatible_sourceRieszShortTransportKernel_all_order_row_bound n s η hs hη hd hv ρ M hM hρ x
  have hSwap : (fun x=>q (x,p.2))=(fun x=>q (p.2,x)) := by
    funext x
    exact localCompatible_sourceRieszShortTransportKernel_all_order_symmetric s η n v (p.2,x)
  have hMean : |∫ z,q z ∂μ.prod μ|≤B := by
    rw [integral_prod _ hPair]
    calc
      _ ≤ ∫ x,|∫ y,q (x,y) ∂μ| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>∫ y,q (x,y) ∂μ)
      _ ≤ ∫ _ : EuclideanSpace ℝ ι,B ∂μ := integral_mono_ae hPair.integral_prod_left.norm (integrable_const _) (Filter.Eventually.of_forall hR)
      _ = _ := by simp [μ]
  have h0 := sourceRieszShortTransportKernel_all_order_bound n s η hs hη hv p
  unfold DGRHS.Gaussian.hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change |q p-(∫ y,q (p.1,y) ∂μ)-(∫ x,q (x,p.2) ∂μ)+(∫ z,q z ∂μ.prod μ)|≤_
  rw [hSwap]
  have hsub (a b : ℝ) : |a-b|≤|a|+|b| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  calc
    _ ≤ |q p|+|∫ y,q (p.1,y) ∂μ|+|∫ x,q (p.2,x) ∂μ|+|∫ z,q z ∂μ.prod μ| := by
      calc
        _ ≤ |q p-(∫ y,q (p.1,y) ∂μ)-(∫ x,q (p.2,x) ∂μ)|+|∫ z,q z ∂μ.prod μ| := abs_add_le _ _
        _ ≤ (|q p-(∫ y,q (p.1,y) ∂μ)|+|∫ x,q (p.2,x) ∂μ|)+|∫ z,q z ∂μ.prod μ| := by gcongr;exact hsub _ _
        _ ≤ _ := by gcongr;exact hsub _ _
    _ ≤ _ := by have h1:=hR p.1;have h2:=hR p.2;linarith
end DGRHS.Commutator
#check DGRHS.Commutator.localCompatible_sourceRieszShortTransportAllOrderPotentialBound
#print axioms DGRHS.Commutator.localCompatible_sourceRieszShortTransportAllOrderPotentialBound
#check DGRHS.Commutator.localCompatible_integrable_sourceRieszShortTransportKernel_all_order_row
#print axioms DGRHS.Commutator.localCompatible_integrable_sourceRieszShortTransportKernel_all_order_row
#check DGRHS.Commutator.localCompatible_sourceRieszShortTransportKernel_all_order_row_bound
#print axioms DGRHS.Commutator.localCompatible_sourceRieszShortTransportKernel_all_order_row_bound
#check DGRHS.Commutator.localCompatible_integrable_sourceRieszShortTransportKernel_all_order_pair
#print axioms DGRHS.Commutator.localCompatible_integrable_sourceRieszShortTransportKernel_all_order_pair
#check DGRHS.Commutator.localCompatible_sourceRieszShortTransportKernel_all_order_centered_bound
#print axioms DGRHS.Commutator.localCompatible_sourceRieszShortTransportKernel_all_order_centered_bound
