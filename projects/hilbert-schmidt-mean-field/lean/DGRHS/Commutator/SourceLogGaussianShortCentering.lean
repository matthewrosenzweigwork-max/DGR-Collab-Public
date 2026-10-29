import DGRHS.Commutator.SourceLogGaussianShortKernel
import DGRHS.Gaussian.GaussianLogShortRangeSource

/-! Proper short transport section/pair integrals and quantitative centering
at the source eta^d scale. Every fixed derivative order is covered. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open scoped NNReal
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

def sourceLogGaussianShortTransportPotentialBound (n : ℕ) (η K M : ℝ) : ℝ :=
  sourceRieszGaussianDerivativeConstant n*K^n*M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*(2:ℝ)^(Fintype.card ι : ℝ))*η^(Fintype.card ι : ℝ)

lemma integrable_sourceLogGaussianShortTransportKernel_row (n : ℕ) (η : ℝ) (hη : 0<η)
    (hd : 0<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂volume,ρ x≤M) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y=>sourceLogGaussianShortTransportKernel n η v (x,y)) (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by
  have hC := sourceRieszGaussianDerivativeConstant_pos n
  have hi := (DGRHS.Gaussian.integrable_gaussianLogShortRange_convolution (2*η) (by positivity)
    hd ρ M hρ x).const_mul (sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n)
  apply hi.mono' ((measurable_sourceLogGaussianShortTransportKernel η n hη hv).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using sourceLogGaussianShortTransportKernel_bound n η hη hv (x,y)

lemma sourceLogGaussianShortTransportKernel_row_bound (n : ℕ) (η : ℝ) (hη : 0<η)
    (hd : 0<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M) (x : EuclideanSpace ℝ ι) :
    (∫ y,|sourceLogGaussianShortTransportKernel n η v (x,y)| ∂DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) ≤
      sourceLogGaussianShortTransportPotentialBound (ι:=ι) n η K M := by
  have hC := sourceRieszGaussianDerivativeConstant_pos n
  have hi := integrable_sourceLogGaussianShortTransportKernel_row n η hη hd hv ρ M hρ x
  have hG := DGRHS.Gaussian.integrable_gaussianLogShortRange_convolution (2*η) (by positivity) hd ρ M hρ x
  have hAbs : Integrable (fun y=>|sourceLogGaussianShortTransportKernel n η v (x,y)|) (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by simpa only [Real.norm_eq_abs] using hi.norm
  calc
    _ ≤ sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*(∫ y,DGRHS.Gaussian.gaussianLogShortRange (2*η) (x-y) ∂DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by
      rw [←integral_const_mul]
      exact integral_mono_ae hAbs (hG.const_mul _) (Filter.Eventually.of_forall (fun y=>sourceLogGaussianShortTransportKernel_bound n η hη hv (x,y)))
    _ ≤ sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*(M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)*(2*η)^(Fintype.card ι : ℝ))) :=
      mul_le_mul_of_nonneg_left (DGRHS.Gaussian.gaussianLogShortRange_convolution_le (2*η) (by positivity) hd ρ M hM hρ x) (by positivity)
    _ = _ := by unfold sourceLogGaussianShortTransportPotentialBound;rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hη.le];ring

lemma integrable_sourceLogGaussianShortTransportKernel_pair (n : ℕ) (η : ℝ) (hη : 0<η)
    (hd : 0<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    Integrable (sourceLogGaussianShortTransportKernel n η v)
      ((DGRHS.Gaussian.gaussianRieszDensityMeasure ρ).prod (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) := by
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  have hm := (measurable_sourceLogGaussianShortTransportKernel η n hη hv).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun x=>integrable_sourceLogGaussianShortTransportKernel_row n η hη hd hv ρ M hρ x)
  · apply (integrable_const (sourceLogGaussianShortTransportPotentialBound (ι:=ι) n η K M)).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    change ‖∫ y,‖sourceLogGaussianShortTransportKernel n η v (x,y)‖ ∂μ‖≤_
    rw [Real.norm_of_nonneg (integral_nonneg (fun y=>norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using sourceLogGaussianShortTransportKernel_row_bound n η hη hd hv ρ M hM hρ x

lemma sourceLogGaussianShortTransportKernel_centered_bound (n : ℕ) (η : ℝ) (hη : 0<η)
    (hd : 0<(Fintype.card ι : ℝ)) {K : ℝ≥0}
    {v : EuclideanSpace ℝ ι→EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
    |DGRHS.Gaussian.hoeffdingCentered (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) (sourceLogGaussianShortTransportKernel n η v) p| ≤
      sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*DGRHS.Gaussian.gaussianLogShortRange (2*η) (p.1-p.2)+
        3*sourceLogGaussianShortTransportPotentialBound (ι:=ι) n η K M := by
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  let q := sourceLogGaussianShortTransportKernel n η v
  let B := sourceLogGaussianShortTransportPotentialBound (ι:=ι) n η K M
  have hPair := integrable_sourceLogGaussianShortTransportKernel_pair n η hη hd hv ρ M hM hρ
  have hR : ∀ x,|∫ y,q (x,y) ∂μ|≤B := by
    intro x
    calc
      _ ≤ ∫ y,|q (x,y)| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y=>q (x,y))
      _ ≤ _ := sourceLogGaussianShortTransportKernel_row_bound n η hη hd hv ρ M hM hρ x
  have hSwap : (fun x=>q (x,p.2))=(fun x=>q (p.2,x)) := by
    funext x
    exact sourceLogGaussianShortTransportKernel_symmetric η n v (p.2,x)
  have hMean : |∫ z,q z ∂μ.prod μ|≤B := by
    rw [integral_prod _ hPair]
    calc
      _ ≤ ∫ x,|∫ y,q (x,y) ∂μ| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>∫ y,q (x,y) ∂μ)
      _ ≤ ∫ _ : EuclideanSpace ℝ ι,B ∂μ := integral_mono_ae hPair.integral_prod_left.norm (integrable_const _) (Filter.Eventually.of_forall hR)
      _ = _ := by simp [μ]
  have h0 := sourceLogGaussianShortTransportKernel_bound n η hη hv p
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
