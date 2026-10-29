import DGRHS.Attractive.SignedFeatureTaylor

/-! Scalar domination for the actual positive Wick remainder. The loose
integer coefficients make the Gaussian joint fourth moment transparent. -/
noncomputable section
namespace DGRHS.Attractive

def positiveWickScalarRemainder (β D t y : ℝ) : ℝ :=
  Real.exp (t*Real.sqrt β*y-t^2*β*D/2) -
    (1+t*Real.sqrt β*y+t^2*(β/2*(y^2-D))+
      t^3*(β*Real.sqrt β/6*(y^3-3*D*y)))

lemma abs_positiveWickScalarRemainder_le (β D t y : ℝ)
    (hβ : 0 ≤ β) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    |positiveWickScalarRemainder β D t y| ≤
      t^4*β^2*Real.exp (t*Real.sqrt β*|y|)*(4*y^4+2*D*y^2+D^2) := by
  have h := abs_positive_wick_cubic_remainder (t^2*β*D/2) (t*Real.sqrt β*y) (by positivity)
  rw [positive_wick_polynomial_coefficients β D t y hβ] at h
  have he : |t*Real.sqrt β*y|=t*Real.sqrt β*|y| := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg (Real.sqrt_nonneg β)]
  rw [he] at h
  have hs := Real.sq_sqrt hβ
  have h4 : (Real.sqrt β)^4=β^2 := by rw [show (4:ℕ)=2*2 by rfl, pow_mul, hs]
  change |positiveWickScalarRemainder β D t y| ≤ _ at h
  calc
    _ ≤ _ := h
    _ = t^4*β^2*Real.exp (t*Real.sqrt β*|y|)*(4*y^4+(3/2)*D*y^2+(1/2)*D^2) := by
      simp only [mul_pow, div_pow, hs, h4]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hD (sq_nonneg y), sq_nonneg D]

lemma fourth_sum_three_le (x y z : ℝ) :
    (x+y+z)^4 ≤ 27*(x^4+y^4+z^4) := by
  have h2 : (x+y+z)^2 ≤ 3*(x^2+y^2+z^2) := by
    nlinarith [sq_nonneg (x-y),sq_nonneg (x-z),sq_nonneg (y-z)]
  have h4 : (x^2+y^2+z^2)^2 ≤ 3*(x^4+y^4+z^4) := by
    nlinarith [sq_nonneg (x^2-y^2),sq_nonneg (x^2-z^2),sq_nonneg (y^2-z^2)]
  have hh := mul_self_le_mul_self (sq_nonneg (x+y+z)) h2
  nlinarith

lemma positiveWickScalarRemainder_fourth_le (β D t y : ℝ)
    (hβ : 0 ≤ β) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    (positiveWickScalarRemainder β D t y)^4 ≤
      t^16*β^8*Real.exp (4*t*Real.sqrt β*|y|)*
        (6912*|y|^16+432*D^4*|y|^8+27*D^8) := by
  have h := abs_positiveWickScalarRemainder_le β D t y hβ hD ht
  have hp := pow_le_pow_left₀ (abs_nonneg _) h 4
  have he : (Real.exp (t*Real.sqrt β*|y|))^4=Real.exp (4*t*Real.sqrt β*|y|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hh := fourth_sum_three_le (4*y^4) (2*D*y^2) (D^2)
  have heq : 27*((4*y^4)^4+(2*D*y^2)^4+(D^2)^4)=
      6912*|y|^16+432*D^4*|y|^8+27*D^8 := by
    rw [show |y|^16=y^16 by rw [show (16:ℕ)=2*8 by rfl,pow_mul,sq_abs]; ring,
      show |y|^8=y^8 by rw [show (8:ℕ)=2*4 by rfl,pow_mul,sq_abs]; ring]
    ring
  rw [heq] at hh
  rw [show |positiveWickScalarRemainder β D t y|^4=(positiveWickScalarRemainder β D t y)^4 by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,sq_abs]; ring,
    mul_pow,mul_pow,mul_pow,he,← pow_mul,← pow_mul] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hh (by positivity))

end DGRHS.Attractive
#check DGRHS.Attractive.positiveWickScalarRemainder_fourth_le
#print axioms DGRHS.Attractive.positiveWickScalarRemainder_fourth_le
