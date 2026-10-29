import DGRHS.Attractive.SignedFeatureCoefficients

/-! Actual jointly proper positive Wick remainder fourth moment. The only
restriction on the scale is the explicit eventual absorption condition; the
original diagonal exponential parameter remains independent of beta. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

def positiveIntegratedWickRemainder (μ : Measure X) (β : ℝ) (D : X → ℝ)
    (g : X × Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ x,positiveWickScalarRemainder β (D x) t (g (x,ω)) ∂μ

lemma positive_remainder_fourth_moment (β : ℝ) (hβ : 0≤β)
    (D : X → ℝ) (hDm : StronglyMeasurable D) (hD : ∀ x,0≤D x)
    (g : X × Ω → ℝ) (hg : StronglyMeasurable g)
    (hLaw : ∀ᵐ x ∂μ,HasLaw (fun ω => g (x,ω)) (gaussianReal 0 (Real.toNNReal (D x))) P)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*D x)) μ)
    (t : ℝ) (ht : 0≤t) (hscale : 32*β*t^2≤a) :
    Integrable (fun p => (positiveWickScalarRemainder β (D p.1) t (g p))^4) (μ.prod P) ∧
    Integrable (fun ω => positiveIntegratedWickRemainder μ β D g t ω^4) P ∧
    (∫ ω,positiveIntegratedWickRemainder μ β D g t ω^4 ∂P) ≤
      t^16*β^8*(6912*gaussianDiagonalMomentConstant a 0 8+
        432*gaussianDiagonalMomentConstant a 4 4+27*gaussianDiagonalMomentConstant a 8 0)*
          (∫ x,Real.exp (a*D x) ∂μ) := by
  let s := 4*t*Real.sqrt β
  have hs : 0≤s := by dsimp [s]; positivity
  have hsa : s^2≤a/2 := by
    dsimp [s]
    rw [mul_pow,mul_pow,Real.sq_sqrt hβ]
    nlinarith
  obtain ⟨hi16,hb16⟩ := joint_gaussian_weighted_even_moment D hDm hD g hg hLaw a ha hM s hs hsa 0 8
  obtain ⟨hiMix,hbMix⟩ := joint_gaussian_weighted_even_moment D hDm hD g hg hLaw a ha hM s hs hsa 4 4
  obtain ⟨hiD,hbD⟩ := joint_gaussian_weighted_even_moment D hDm hD g hg hLaw a ha hM s hs hsa 8 0
  simp only [Nat.reduceMul,pow_zero,one_mul,mul_one] at hi16 hb16 hiD hbD
  let F : X × Ω → ℝ := fun p => positiveWickScalarRemainder β (D p.1) t (g p)
  let Q : X × Ω → ℝ := fun p =>
    6912*(|g p|^16*Real.exp (s*|g p|))+
      432*(D p.1^4*|g p|^8*Real.exp (s*|g p|))+
      27*(D p.1^8*Real.exp (s*|g p|))
  have hQ : Integrable Q (μ.prod P) :=
    ((hi16.const_mul 6912).add (hiMix.const_mul 432)).add (hiD.const_mul 27)
  have hm : StronglyMeasurable F := by
    dsimp [F,positiveWickScalarRemainder]
    fun_prop
  have hb (p : X × Ω) : F p^4≤t^16*β^8*Q p := by
    have h := positiveWickScalarRemainder_fourth_le β (D p.1) t (g p) hβ (hD _) ht
    dsimp [F,Q,s]
    convert h using 1 <;> ring
  have hi4 : Integrable (fun p => F p^4) (μ.prod P) := by
    apply (hQ.const_mul (t^16*β^8)).mono' (hm.pow 4).aestronglyMeasurable
    filter_upwards [] with p
    change ‖F p^4‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hb p
  obtain ⟨hiE,hbE⟩ := spatial_fourth_moment F hm hi4
  refine ⟨hi4,hiE,?_⟩
  calc
    _ ≤ ∫ p,F p^4 ∂μ.prod P := hbE
    _ ≤ ∫ p,t^16*β^8*Q p ∂μ.prod P := integral_mono hi4 (hQ.const_mul _) hb
    _ = t^16*β^8*(6912*(∫ p,|g p|^16*Real.exp (s*|g p|) ∂μ.prod P)+
        432*(∫ p,D p.1^4*|g p|^8*Real.exp (s*|g p|) ∂μ.prod P)+
        27*(∫ p,D p.1^8*Real.exp (s*|g p|) ∂μ.prod P)) := by
      rw [integral_const_mul]
      dsimp [Q]
      rw [integral_add _ (hiD.const_mul 27),integral_add (hi16.const_mul 6912) (hiMix.const_mul 432)]
      · simp_rw [integral_const_mul]
      · exact (hi16.const_mul 6912).add (hiMix.const_mul 432)
    _ ≤ _ := by
      dsimp [gaussianDiagonalMomentConstant]
      have hh := mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hb16 (by norm_num : (0:ℝ)≤6912))
            (mul_le_mul_of_nonneg_left hbMix (by norm_num : (0:ℝ)≤432)))
          (mul_le_mul_of_nonneg_left hbD (by norm_num : (0:ℝ)≤27)))
        (by positivity : 0≤t^16*β^8)
      convert hh using 1 <;> ring

end DGRHS.Attractive
#check DGRHS.Attractive.positive_remainder_fourth_moment
#print axioms DGRHS.Attractive.positive_remainder_fourth_moment
