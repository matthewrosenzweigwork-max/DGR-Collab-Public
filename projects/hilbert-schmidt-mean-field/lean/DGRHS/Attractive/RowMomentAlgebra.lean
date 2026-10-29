/- Proper factorial-row algebra with explicit every-row quantifiers.
Coarse constants suffice for the source's possibly smaller quantitative threshold. -/
import DGRHS.Attractive.RowMoments
import DGRHS.Gaussian.HoeffdingLinearity
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω]

lemma nonneg_sum_pow_le (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (p : ℕ) :
    (a+b)^p ≤ 2^p*(a^p+b^p) := by
  rcases le_total a b with hab | hba
  · have h := pow_le_pow_left₀ (by positivity : 0≤a+b) (show a+b≤2*b by linarith) p
    rw [mul_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg ha p)) (by positivity))
  · have h := pow_le_pow_left₀ (by positivity : 0≤a+b) (show a+b≤2*a by linarith) p
    rw [mul_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hb p)) (by positivity))

lemma RowFactorialMoments.sub_scaled (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h k : Ω×Ω→ℝ) (hh : Measurable h) (hk : Measurable k) (C D t : ℝ)
    (hC : RowFactorialMoments μ h C) (hD : RowFactorialMoments μ k D) (ht : |t|≤1) :
    RowFactorialMoments μ (fun z => h z-t*k z) (4*(C+D)) := by
  have htn : 0≤|t| := abs_nonneg t
  have hpoint (p : ℕ) (x y : Ω) : |h (x,y)-t*k (x,y)|^p ≤
      2^p*(|h (x,y)|^p+|k (x,y)|^p) := by
    have ha : |h (x,y)-t*k (x,y)|≤|h (x,y)|+|k (x,y)| := by
      have hb : |h (x,y)-t*k (x,y)|≤|h (x,y)|+|t*k (x,y)| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (h (x,y)) (-(t*k (x,y)))
      apply hb.trans
      apply add_le_add_right _ _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans_eq (one_mul _)
    exact (pow_le_pow_left₀ (abs_nonneg _) ha p).trans
      (nonneg_sum_pow_le _ _ (abs_nonneg _) (abs_nonneg _) p)
  refine ⟨by linarith [hC.nonneg,hD.nonneg],?_,?_⟩
  · intro p hp y
    apply ((hC.proper p hp y).add (hD.proper p hp y)).const_mul (2^p) |>.mono'
      (by fun_prop)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs,abs_pow,abs_abs,Pi.add_apply] using hpoint p x y
  · intro p hp y
    have hb := integral_mono_ae (by
      apply ((hC.proper p hp y).add (hD.proper p hp y)).const_mul (2^p) |>.mono'
        (by fun_prop)
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_pow,abs_abs,Pi.add_apply] using hpoint p x y)
      (((hC.proper p hp y).add (hD.proper p hp y)).const_mul (2^p))
      (Filter.Eventually.of_forall fun x => hpoint p x y)
    rw [integral_const_mul] at hb
    change (∫ x,|h (x,y)-t*k (x,y)|^p ∂μ) ≤
      2^p*(∫ x,|h (x,y)|^p+|k (x,y)|^p ∂μ) at hb
    have ha := integral_add (hC.proper p hp y) (hD.proper p hp y)
    change (∫ x,|h (x,y)|^p+|k (x,y)|^p ∂μ) =
      (∫ x,|h (x,y)|^p ∂μ)+(∫ x,|k (x,y)|^p ∂μ) at ha
    rw [ha] at hb
    have hm := mul_le_mul_of_nonneg_left (add_le_add (hC.bound p hp y) (hD.bound p hp y))
      (by positivity : (0:ℝ)≤2^p)
    have hCp : C^p≤(C+D)^p := pow_le_pow_left₀ hC.nonneg (by linarith [hD.nonneg]) p
    have hDp : D^p≤(C+D)^p := pow_le_pow_left₀ hD.nonneg (by linarith [hC.nonneg]) p
    have h2 : (2:ℝ)≤2^p := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hp
    apply hb.trans (hm.trans _)
    calc
      2^p*(C^p*(p.factorial:ℝ)+D^p*(p.factorial:ℝ)) ≤
        2^p*(2*(C+D)^p*(p.factorial:ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by
            nlinarith [mul_le_mul_of_nonneg_right (add_le_add hCp hDp) (Nat.cast_nonneg (p.factorial))]) (by positivity)
      _ ≤ 2^p*(2^p*(C+D)^p*(p.factorial:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hx := mul_le_mul_of_nonneg_right h2
          (mul_nonneg (pow_nonneg (add_nonneg hC.nonneg hD.nonneg) p)
            (Nat.cast_nonneg (p.factorial)))
        simpa only [mul_assoc] using hx
      _ = (4*(C+D))^p*(p.factorial:ℝ) := by
        rw [show 4*(C+D)=2*(2*(C+D)) by ring]
        simp only [mul_pow]
        ring


end DGRHS.Attractive
#print axioms DGRHS.Attractive.nonneg_sum_pow_le
#check @DGRHS.Attractive.RowFactorialMoments.sub_scaled
#print axioms DGRHS.Attractive.RowFactorialMoments.sub_scaled
