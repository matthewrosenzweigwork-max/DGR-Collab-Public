import DGRHS.Attractive.SignedFeatureJointMoments
import DGRHS.Attractive.SignedFeatureSpatialMoments
import DGRHS.Attractive.SignedFeatureRemainderScalar

/-! Genuine quadratic/cubic fourth moments from the original diagonal
exponential parameter a. All product and spatial properness is derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

def positiveQuadraticIntegrand (β : ℝ) (D : X → ℝ) (g : X × Ω → ℝ) (p : X × Ω) : ℝ :=
  (β/2)*(g p^2-D p.1)

def positiveCubicIntegrand (β : ℝ) (D : X → ℝ) (g : X × Ω → ℝ) (p : X × Ω) : ℝ :=
  (β*Real.sqrt β/6)*(g p^3-3*D p.1*g p)

def positiveQuadraticCoefficient (μ : Measure X) (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (ω : Ω) : ℝ := ∫ x,positiveQuadraticIntegrand β D g (x,ω) ∂μ

def positiveCubicCoefficient (μ : Measure X) (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (ω : Ω) : ℝ := ∫ x,positiveCubicIntegrand β D g (x,ω) ∂μ

def gaussianDiagonalMomentConstant (a : ℝ) (l r : ℕ) : ℝ :=
  2*((2*r).factorial:ℝ)*Real.exp 1*((l+r).factorial:ℝ)/(a/2)^(l+r)

lemma fourth_difference_le (x y : ℝ) : (x-y)^4 ≤ 27*(x^4+y^4) := by
  simpa only [show (-y)^4=y^4 by ring, zero_pow (by decide : (4:ℕ)≠0),
    add_zero,sub_eq_add_neg] using fourth_sum_three_le x (-y) 0

lemma positiveQuadraticIntegrand_fourth_le (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (p : X × Ω) :
    positiveQuadraticIntegrand β D g p^4 ≤
      27*(β/2)^4*(|g p|^8+(D p.1)^4) := by
  have h := mul_le_mul_of_nonneg_left (fourth_difference_le (g p^2) (D p.1))
    (by positivity : 0 ≤ (β/2)^4)
  unfold positiveQuadraticIntegrand
  rw [mul_pow]
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [show |g p|^8=g p^8 by rw [show (8:ℕ)=2*4 by rfl,pow_mul,sq_abs]; ring]
      ring

lemma positiveCubicIntegrand_fourth_le (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (p : X × Ω) :
    positiveCubicIntegrand β D g p^4 ≤
      27*(β*Real.sqrt β/6)^4*(|g p|^12+81*(D p.1)^4*|g p|^4) := by
  have h := mul_le_mul_of_nonneg_left (fourth_difference_le (g p^3) (3*D p.1*g p))
    (by positivity : 0 ≤ (β*Real.sqrt β/6)^4)
  unfold positiveCubicIntegrand
  rw [mul_pow]
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [show |g p|^12=g p^12 by rw [show (12:ℕ)=2*6 by rfl,pow_mul,sq_abs]; ring,
        show |g p|^4=g p^4 by rw [show (4:ℕ)=2*2 by rfl,pow_mul,sq_abs]; ring]
      ring

lemma positive_quadratic_fourth_moment (β : ℝ)
    (D : X → ℝ) (hDm : StronglyMeasurable D) (hD : ∀ x,0≤D x)
    (g : X × Ω → ℝ) (hg : StronglyMeasurable g)
    (hLaw : ∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω)) (gaussianReal 0 (Real.toNNReal (D x))) P)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*D x)) μ) :
    Integrable (fun p => positiveQuadraticIntegrand β D g p^4) (μ.prod P) ∧
    Integrable (fun ω => positiveQuadraticCoefficient μ β D g ω^4) P ∧
    (∫ ω,positiveQuadraticCoefficient μ β D g ω^4 ∂P) ≤
      27*(β/2)^4*(gaussianDiagonalMomentConstant a 0 4+gaussianDiagonalMomentConstant a 4 0)*
        (∫ x,Real.exp (a*D x) ∂μ) := by
  obtain ⟨hi8,hb8⟩ := joint_gaussian_weighted_even_moment D hDm hD g hg hLaw a ha hM
    0 (le_refl 0) (by norm_num; positivity) 0 4
  obtain ⟨hiD,hbD⟩ := joint_gaussian_weighted_even_moment D hDm hD g hg hLaw a ha hM
    0 (le_refl 0) (by norm_num; positivity) 4 0
  simp only [Nat.reduceMul, Nat.add_zero, Nat.zero_add, zero_mul,Real.exp_zero,pow_zero,one_mul,mul_one] at hi8 hb8 hiD hbD
  have hm : StronglyMeasurable (positiveQuadraticIntegrand β D g) := by
    unfold positiveQuadraticIntegrand
    exact ((hg.pow 2).sub (hDm.comp_measurable measurable_fst)).const_mul _
  have hi4 : Integrable (fun p => positiveQuadraticIntegrand β D g p^4) (μ.prod P) := by
    apply ((hi8.add hiD).const_mul (27*(β/2)^4)).mono' (hm.pow 4).aestronglyMeasurable
    filter_upwards [] with p
    change ‖positiveQuadraticIntegrand β D g p^4‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact positiveQuadraticIntegrand_fourth_le β D g p
  obtain ⟨hiB,hbB⟩ := spatial_fourth_moment (positiveQuadraticIntegrand β D g) hm hi4
  refine ⟨hi4,hiB,?_⟩
  calc
    _ ≤ ∫ p,positiveQuadraticIntegrand β D g p^4 ∂μ.prod P := hbB
    _ ≤ ∫ p,27*(β/2)^4*(|g p|^8+(D p.1)^4) ∂μ.prod P :=
      integral_mono hi4 ((hi8.add hiD).const_mul _) (positiveQuadraticIntegrand_fourth_le β D g)
    _ = 27*(β/2)^4*((∫ p,|g p|^8 ∂μ.prod P)+(∫ p,(D p.1)^4 ∂μ.prod P)) := by
      rw [integral_const_mul,integral_add hi8 hiD]
    _ ≤ _ := by
      dsimp [gaussianDiagonalMomentConstant]
      have hh := mul_le_mul_of_nonneg_left (add_le_add hb8 hbD)
        (by positivity : 0≤27*(β/2)^4)
      convert hh using 1 <;> ring

lemma positive_cubic_fourth_moment (β : ℝ)
    (D : X → ℝ) (hDm : StronglyMeasurable D) (hD : ∀ x,0≤D x)
    (g : X × Ω → ℝ) (hg : StronglyMeasurable g)
    (hLaw : ∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω)) (gaussianReal 0 (Real.toNNReal (D x))) P)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*D x)) μ) :
    Integrable (fun p => positiveCubicIntegrand β D g p^4) (μ.prod P) ∧
    Integrable (fun ω => positiveCubicCoefficient μ β D g ω^4) P ∧
    (∫ ω,positiveCubicCoefficient μ β D g ω^4 ∂P) ≤
      27*(β*Real.sqrt β/6)^4*
        (gaussianDiagonalMomentConstant a 0 6+81*gaussianDiagonalMomentConstant a 4 2)*
        (∫ x,Real.exp (a*D x) ∂μ) := by
  obtain ⟨hi12,hb12⟩ := joint_gaussian_weighted_even_moment D hDm hD g hg hLaw a ha hM
    0 (le_refl 0) (by norm_num; positivity) 0 6
  obtain ⟨hiMix,hbMix⟩ := joint_gaussian_weighted_even_moment D hDm hD g hg hLaw a ha hM
    0 (le_refl 0) (by norm_num; positivity) 4 2
  simp only [Nat.reduceMul, Nat.add_zero, Nat.zero_add, zero_mul,Real.exp_zero,pow_zero,one_mul,mul_one] at hi12 hb12 hiMix hbMix
  have hm : StronglyMeasurable (positiveCubicIntegrand β D g) := by
    unfold positiveCubicIntegrand
    exact ((hg.pow 3).sub (((hDm.comp_measurable measurable_fst).const_mul 3).mul hg)).const_mul _
  have hi4 : Integrable (fun p => positiveCubicIntegrand β D g p^4) (μ.prod P) := by
    apply ((hi12.add (hiMix.const_mul 81)).const_mul (27*(β*Real.sqrt β/6)^4)).mono'
      (hm.pow 4).aestronglyMeasurable
    filter_upwards [] with p
    change ‖positiveCubicIntegrand β D g p^4‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    simpa only [Pi.add_apply, mul_assoc] using positiveCubicIntegrand_fourth_le β D g p
  obtain ⟨hiR,hbR⟩ := spatial_fourth_moment (positiveCubicIntegrand β D g) hm hi4
  refine ⟨hi4,hiR,?_⟩
  calc
    _ ≤ ∫ p,positiveCubicIntegrand β D g p^4 ∂μ.prod P := hbR
    _ ≤ ∫ p,27*(β*Real.sqrt β/6)^4*(|g p|^12+81*((D p.1)^4*|g p|^4)) ∂μ.prod P := by
      apply integral_mono hi4 ((hi12.add (hiMix.const_mul 81)).const_mul _)
      intro p
      simpa only [Pi.add_apply, mul_assoc] using positiveCubicIntegrand_fourth_le β D g p
    _ = 27*(β*Real.sqrt β/6)^4*((∫ p,|g p|^12 ∂μ.prod P)+
        81*(∫ p,(D p.1)^4*|g p|^4 ∂μ.prod P)) := by
      rw [integral_const_mul,integral_add hi12 (hiMix.const_mul 81),integral_const_mul]
    _ ≤ _ := by
      dsimp [gaussianDiagonalMomentConstant]
      have hh := mul_le_mul_of_nonneg_left
        (add_le_add hb12 (mul_le_mul_of_nonneg_left hbMix (by norm_num : (0:ℝ)≤81)))
        (by positivity : 0≤27*(β*Real.sqrt β/6)^4)
      convert hh using 1 <;> ring

end DGRHS.Attractive
#check DGRHS.Attractive.positive_quadratic_fourth_moment
#print axioms DGRHS.Attractive.positive_quadratic_fourth_moment
#check DGRHS.Attractive.positive_cubic_fourth_moment
#print axioms DGRHS.Attractive.positive_cubic_fourth_moment
