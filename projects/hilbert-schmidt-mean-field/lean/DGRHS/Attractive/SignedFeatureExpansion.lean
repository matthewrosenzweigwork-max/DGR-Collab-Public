import DGRHS.Attractive.SignedFeatureRemainderMoments
import DGRHS.Gaussian.FeatureRateNormalization

/-! Actual integrated positive polynomial expansion. The elementary section
lemma takes only genuine section properness, derives properness of the Wick
factor, and integrates the checked pointwise residual identity. All section
inputs are to be discharged by actual joint moment properness before the
source factory endpoint; no Taylor or rate conclusion is a premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} [IsProbabilityMeasure μ]

lemma stronglyMeasurable_positiveQuadraticCoefficient (β : ℝ) (D : X → ℝ)
    (hD : StronglyMeasurable D) (g : X × Ω → ℝ) (hg : StronglyMeasurable g) :
    StronglyMeasurable (positiveQuadraticCoefficient μ β D g) := by
  have hm : StronglyMeasurable (positiveQuadraticIntegrand β D g) :=
    ((hg.pow 2).sub (hD.comp_measurable measurable_fst)).const_mul _
  exact hm.integral_prod_left'

lemma stronglyMeasurable_positiveCubicCoefficient (β : ℝ) (D : X → ℝ)
    (hD : StronglyMeasurable D) (g : X × Ω → ℝ) (hg : StronglyMeasurable g) :
    StronglyMeasurable (positiveCubicCoefficient μ β D g) := by
  have hm : StronglyMeasurable (positiveCubicIntegrand β D g) :=
    ((hg.pow 3).sub (((hD.comp_measurable measurable_fst).const_mul 3).mul hg)).const_mul _
  exact hm.integral_prod_left'

lemma stronglyMeasurable_positiveIntegratedWickRemainder (β : ℝ) (D : X → ℝ)
    (hD : StronglyMeasurable D) (g : X × Ω → ℝ) (hg : StronglyMeasurable g) (t : ℝ) :
    StronglyMeasurable (positiveIntegratedWickRemainder μ β D g t) := by
  have hm : StronglyMeasurable (fun p : X × Ω => positiveWickScalarRemainder β (D p.1) t (g p)) := by
    unfold positiveWickScalarRemainder
    fun_prop
  exact hm.integral_prod_left'

lemma stronglyMeasurable_positiveFeatureFactor {H : Type*} [NormedAddCommGroup H]
    (β : ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) (N : ℕ) :
    StronglyMeasurable (positiveFeatureFactor μ β k g N) := by
  have hm : StronglyMeasurable (positiveFeatureWick β k g N) := by
    unfold positiveFeatureWick
    exact Real.continuous_exp.comp_stronglyMeasurable ((hg.const_mul _).sub
      (((hk.comp_measurable measurable_fst).norm.pow 2).const_mul _))
  exact hm.integral_prod_left'

lemma positive_wick_integrated_expansion (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (t : ℝ) (ω : Ω)
    (hg1 : Integrable (fun x => g (x,ω)) μ) (hmean : (∫ x,g (x,ω) ∂μ)=0)
    (hB : Integrable (fun x => positiveQuadraticIntegrand β D g (x,ω)) μ)
    (hR : Integrable (fun x => positiveCubicIntegrand β D g (x,ω)) μ)
    (hE : Integrable (fun x => positiveWickScalarRemainder β (D x) t (g (x,ω))) μ) :
    Integrable (fun x => Real.exp (t*Real.sqrt β*g (x,ω)-t^2*β*D x/2)) μ ∧
    (∫ x,Real.exp (t*Real.sqrt β*g (x,ω)-t^2*β*D x/2) ∂μ)=
      1+t^2*positiveQuadraticCoefficient μ β D g ω+
        t^3*positiveCubicCoefficient μ β D g ω+positiveIntegratedWickRemainder μ β D g t ω := by
  have he : (fun x => Real.exp (t*Real.sqrt β*g (x,ω)-t^2*β*D x/2)) =
      fun x => 1+(t*Real.sqrt β)*g (x,ω)+t^2*positiveQuadraticIntegrand β D g (x,ω)+
        t^3*positiveCubicIntegrand β D g (x,ω)+positiveWickScalarRemainder β (D x) t (g (x,ω)) := by
    funext x
    unfold positiveQuadraticIntegrand positiveCubicIntegrand positiveWickScalarRemainder
    ring
  have h12 := (integrable_const (1:ℝ)).add (hg1.const_mul (t*Real.sqrt β))
  have h123 := h12.add (hB.const_mul (t^2))
  have h1234 := h123.add (hR.const_mul (t^3))
  have hi := h1234.add hE
  refine ⟨by rw [he]; exact hi,?_⟩
  have hs4 := integral_add h1234 hE
  have hs3 := integral_add h123 (hR.const_mul (t^3))
  have hs2 := integral_add h12 (hB.const_mul (t^2))
  have hs1 := integral_add (integrable_const (1:ℝ)) (hg1.const_mul (t*Real.sqrt β))
  simp only [Pi.add_apply] at hs4 hs3 hs2 hs1
  rw [he, hs4, hs3, hs2, hs1]
  simp only [integral_const_mul,hmean,mul_zero,add_zero]
  have hc : (∫ x,(1:ℝ) ∂μ)=1 := by simp
  rw [hc]
  rfl

def positiveFeatureNormalizedRemainder (μ : Measure X) (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (N:ℝ)^2*positiveIntegratedWickRemainder μ β D g (featureRateScale N) ω

lemma positiveFeatureNormalizedRemainder_div (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (N : ℕ) (hN : 1≤N) (ω : Ω) :
    positiveFeatureNormalizedRemainder μ β D g N ω/(N:ℝ)^2=
      positiveIntegratedWickRemainder μ β D g (featureRateScale N) ω := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by norm_num : 0<1) hN))
  unfold positiveFeatureNormalizedRemainder
  field_simp

variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma positiveWickScalarRemainder_integrable_of_wick (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (t : ℝ) (ω : Ω)
    (hg1 : Integrable (fun x => g (x,ω)) μ)
    (hB : Integrable (fun x => positiveQuadraticIntegrand β D g (x,ω)) μ)
    (hR : Integrable (fun x => positiveCubicIntegrand β D g (x,ω)) μ)
    (hWick : Integrable (fun x => Real.exp (t*Real.sqrt β*g (x,ω)-t^2*β*D x/2)) μ) :
    Integrable (fun x => positiveWickScalarRemainder β (D x) t (g (x,ω))) μ := by
  have hp := (((integrable_const (1:ℝ)).add (hg1.const_mul (t*Real.sqrt β))).add
    (hB.const_mul (t^2))).add (hR.const_mul (t^3))
  convert hWick.sub hp using 1
  funext x
  simp only [Pi.sub_apply, Pi.add_apply]
  unfold positiveWickScalarRemainder positiveQuadraticIntegrand positiveCubicIntegrand
  ring

lemma positiveFeatureWick_eq_scaled {H : Type*} [NormedAddCommGroup H]
    (β : ℝ) (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : X × (ℕ → ℝ)) :
    positiveFeatureWick β k g N p = Real.exp
      (featureRateScale N*Real.sqrt β*g p-featureRateScale N^2*β*‖k p.1‖^2/2) := by
  unfold positiveFeatureWick
  rw [featureRateScale_sq,featureRateScale_mul_sqrt]
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma ae_positiveFeatureFactor_expansion {H : Type*} [NormedAddCommGroup H]
    (β : ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hLaw : ∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω))
      (gaussianReal 0 (Real.toNNReal (‖k x‖^2))) IsonormalProcess.iidStdGaussian)
    (hg1 : ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,Integrable (fun x => g (x,ω)) μ)
    (hmean : ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,(∫ x,g (x,ω) ∂μ)=0)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (N : ℕ) (hN : 1≤N)
    (hWick : ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      Integrable (fun x => positiveFeatureWick β k g N (x,ω)) μ) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, positiveFeatureFactor μ β k g N ω =
      1+positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω/(N:ℝ)+
        positiveCubicCoefficient μ β (fun x => ‖k x‖^2) g ω/((N:ℝ)*Real.sqrt (N:ℝ))+
        positiveFeatureNormalizedRemainder μ β (fun x => ‖k x‖^2) g N ω/(N:ℝ)^2 := by
  let D : X → ℝ := fun x => ‖k x‖^2
  have hDm : StronglyMeasurable D := hk.norm.pow 2
  have hD : ∀ x,0≤D x := fun x => sq_nonneg _
  obtain ⟨hB4,_,_⟩ := positive_quadratic_fourth_moment β D hDm hD g hg hLaw a ha hM
  obtain ⟨hR4,_,_⟩ := positive_cubic_fourth_moment β D hDm hD g hg hLaw a ha hM
  have hBm : StronglyMeasurable (positiveQuadraticIntegrand β D g) := by
    unfold positiveQuadraticIntegrand
    exact ((hg.pow 2).sub (hDm.comp_measurable measurable_fst)).const_mul _
  have hRm : StronglyMeasurable (positiveCubicIntegrand β D g) := by
    unfold positiveCubicIntegrand
    exact ((hg.pow 3).sub (((hDm.comp_measurable measurable_fst).const_mul 3).mul hg)).const_mul _
  have hB1 := (integrable_lower_powers_of_fourth _ hBm.aestronglyMeasurable hB4).1
  have hR1 := (integrable_lower_powers_of_fourth _ hRm.aestronglyMeasurable hR4).1
  filter_upwards [hg1,hmean,hB1.prod_left_ae,hR1.prod_left_ae,hWick] with ω hi hz hB hR hω
  have hw : Integrable (fun x => Real.exp
      (featureRateScale N*Real.sqrt β*g (x,ω)-featureRateScale N^2*β*D x/2)) μ := by
    simpa only [positiveFeatureWick_eq_scaled] using hω
  have hE := positiveWickScalarRemainder_integrable_of_wick β D g (featureRateScale N) ω hi hB hR hw
  have he := (positive_wick_integrated_expansion β D g (featureRateScale N) ω hi hz hB hR hE).2
  unfold positiveFeatureFactor
  simp_rw [positiveFeatureWick_eq_scaled]
  rw [he,featureRateScale_sq,featureRateScale_cube,
    positiveFeatureNormalizedRemainder_div β D g N hN ω]
  simp only [div_eq_mul_inv]
  ring

lemma ae_positive_wick_integrated_expansion (β : ℝ) (hβ : 0≤β)
    (D : X → ℝ) (hDm : StronglyMeasurable D) (hD : ∀ x,0≤D x)
    (g : X × Ω → ℝ) (hg : StronglyMeasurable g)
    (hLaw : ∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω)) (gaussianReal 0 (Real.toNNReal (D x))) P)
    (hg1 : ∀ᵐ ω ∂P, Integrable (fun x => g (x,ω)) μ)
    (hmean : ∀ᵐ ω ∂P, (∫ x,g (x,ω) ∂μ)=0)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*D x)) μ)
    (t : ℝ) (ht : 0≤t) (hscale : 32*β*t^2≤a) :
    ∀ᵐ ω ∂P,
      Integrable (fun x => Real.exp (t*Real.sqrt β*g (x,ω)-t^2*β*D x/2)) μ ∧
      (∫ x,Real.exp (t*Real.sqrt β*g (x,ω)-t^2*β*D x/2) ∂μ)=
        1+t^2*positiveQuadraticCoefficient μ β D g ω+
          t^3*positiveCubicCoefficient μ β D g ω+positiveIntegratedWickRemainder μ β D g t ω := by
  obtain ⟨hB4,_,_⟩ := positive_quadratic_fourth_moment β D hDm hD g hg hLaw a ha hM
  obtain ⟨hR4,_,_⟩ := positive_cubic_fourth_moment β D hDm hD g hg hLaw a ha hM
  obtain ⟨hE4,_,_⟩ := positive_remainder_fourth_moment β hβ D hDm hD g hg hLaw a ha hM t ht hscale
  have hBm : StronglyMeasurable (positiveQuadraticIntegrand β D g) := by
    unfold positiveQuadraticIntegrand
    exact ((hg.pow 2).sub (hDm.comp_measurable measurable_fst)).const_mul _
  have hRm : StronglyMeasurable (positiveCubicIntegrand β D g) := by
    unfold positiveCubicIntegrand
    exact ((hg.pow 3).sub (((hDm.comp_measurable measurable_fst).const_mul 3).mul hg)).const_mul _
  have hEm : StronglyMeasurable (fun p : X × Ω => positiveWickScalarRemainder β (D p.1) t (g p)) := by
    unfold positiveWickScalarRemainder
    fun_prop
  have hB1 := (integrable_lower_powers_of_fourth _ hBm.aestronglyMeasurable hB4).1
  have hR1 := (integrable_lower_powers_of_fourth _ hRm.aestronglyMeasurable hR4).1
  have hE1 := (integrable_lower_powers_of_fourth _ hEm.aestronglyMeasurable hE4).1
  filter_upwards [hg1,hmean,hB1.prod_left_ae,hR1.prod_left_ae,hE1.prod_left_ae] with ω hω hzero hB hR hE
  exact positive_wick_integrated_expansion β D g t ω hω hzero hB hR hE

lemma positiveFeatureNormalizedRemainder_fourth_moment (β : ℝ) (hβ : 0≤β)
    (D : X → ℝ) (hDm : StronglyMeasurable D) (hD : ∀ x,0≤D x)
    (g : X × Ω → ℝ) (hg : StronglyMeasurable g)
    (hLaw : ∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω)) (gaussianReal 0 (Real.toNNReal (D x))) P)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*D x)) μ)
    (N : ℕ) (hN : 1≤N) (hscale : 32*β≤a*(N:ℝ)) :
    Integrable (fun ω => positiveFeatureNormalizedRemainder μ β D g N ω^4) P ∧
    (∫ ω,positiveFeatureNormalizedRemainder μ β D g N ω^4 ∂P) ≤
      β^8*(6912*gaussianDiagonalMomentConstant a 0 8+
        432*gaussianDiagonalMomentConstant a 4 4+27*gaussianDiagonalMomentConstant a 8 0)*
          (∫ x,Real.exp (a*D x) ∂μ) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hN)
  have hsc : 32*β*featureRateScale N^2≤a := by
    rw [featureRateScale_sq,←div_eq_mul_inv]
    exact (div_le_iff₀ hn).2 hscale
  obtain ⟨_,hi,hb⟩ := positive_remainder_fourth_moment β hβ D hDm hD g hg hLaw a ha hM
    (featureRateScale N) (featureRateScale_nonneg N) hsc
  have heq : (fun ω => positiveFeatureNormalizedRemainder μ β D g N ω^4)=
      fun ω => ((N:ℝ)^2)^4*positiveIntegratedWickRemainder μ β D g (featureRateScale N) ω^4 := by
    funext ω
    unfold positiveFeatureNormalizedRemainder
    rw [mul_pow]
  refine ⟨by rw [heq];exact hi.const_mul _,?_⟩
  rw [heq,integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0≤((N:ℝ)^2)^4)
  have hc : ((N:ℝ)^2)^4*featureRateScale N^16=1 := by
    calc
      _ = ((N:ℝ)^2*featureRateScale N^4)^4 := by ring
      _ = 1 := by rw [featureRateScale_fourth_cancel N hN];norm_num
  calc
    _ ≤ ((N:ℝ)^2)^4*(featureRateScale N^16*β^8*
        (6912*gaussianDiagonalMomentConstant a 0 8+
          432*gaussianDiagonalMomentConstant a 4 4+27*gaussianDiagonalMomentConstant a 8 0)*
            (∫ x,Real.exp (a*D x) ∂μ)) := hh
    _ = (((N:ℝ)^2)^4*featureRateScale N^16)*
        (β^8*(6912*gaussianDiagonalMomentConstant a 0 8+
          432*gaussianDiagonalMomentConstant a 4 4+27*gaussianDiagonalMomentConstant a 8 0)*
            (∫ x,Real.exp (a*D x) ∂μ)) := by ring
    _ = _ := by rw [hc,one_mul]


end DGRHS.Attractive
#check DGRHS.Attractive.positive_wick_integrated_expansion
#print axioms DGRHS.Attractive.positive_wick_integrated_expansion
#check DGRHS.Attractive.ae_positive_wick_integrated_expansion
#print axioms DGRHS.Attractive.ae_positive_wick_integrated_expansion
#check DGRHS.Attractive.positiveFeatureNormalizedRemainder_fourth_moment
#print axioms DGRHS.Attractive.positiveFeatureNormalizedRemainder_fourth_moment
#check DGRHS.Attractive.ae_positiveFeatureFactor_expansion
#print axioms DGRHS.Attractive.ae_positiveFeatureFactor_expansion

#check DGRHS.Attractive.stronglyMeasurable_positiveFeatureFactor
#print axioms DGRHS.Attractive.stronglyMeasurable_positiveFeatureFactor
#check DGRHS.Attractive.stronglyMeasurable_positiveQuadraticCoefficient
#print axioms DGRHS.Attractive.stronglyMeasurable_positiveQuadraticCoefficient
#check DGRHS.Attractive.stronglyMeasurable_positiveCubicCoefficient
#print axioms DGRHS.Attractive.stronglyMeasurable_positiveCubicCoefficient
#check DGRHS.Attractive.stronglyMeasurable_positiveIntegratedWickRemainder
#print axioms DGRHS.Attractive.stronglyMeasurable_positiveIntegratedWickRemainder
