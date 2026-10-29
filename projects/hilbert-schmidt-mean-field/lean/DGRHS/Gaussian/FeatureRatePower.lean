import DGRHS.Gaussian.FeatureRateNormalization
import DGRHS.Gaussian.PowerApproximation
noncomputable section
namespace DGRHS.Gaussian

lemma feature_rate_norm_power_sub (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1 : ℝ) * r ^ n * ‖a - b‖ :=
  norm_power_difference a b r hr ha hb n

lemma feature_rate_norm_power_sub_of_bound (a b : ℂ) (r A : ℝ)
    (hr : 1 ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r)
    (N : ℕ) (hN : 1 ≤ N) (hA : r ^ N ≤ A) :
    ‖a ^ N - b ^ N‖ ≤ (N : ℝ) * A * ‖a - b‖ :=
  norm_power_difference_of_bound a b r A hr ha hb N hN hA

lemma feature_rate_norm_increment_remainder (a u : ℂ) (δ : ℝ)
    (hu : ‖u‖ ≤ 1) (hδ : ‖a - (1 + u)‖ ≤ δ) :
    ‖a - Complex.exp u‖ ≤ δ + ‖u‖ ^ 2 :=
  norm_exp_increment_difference a u δ hu hδ

lemma feature_rate_norm_increment_le (B R : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖((B / (N : ℝ) : ℝ) : ℂ) + Complex.I * (R / ((N : ℝ) * Real.sqrt (N : ℝ)) : ℝ)‖ ≤
      (|B| + |R|) / (N : ℝ) := by
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN1
  have hs : 0 < Real.sqrt (N : ℝ) := by linarith
  calc
    _ ≤ |B / (N : ℝ)| + |R / ((N : ℝ) * Real.sqrt (N : ℝ))| := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul] using norm_add_le
        (((B / (N : ℝ) : ℝ) : ℂ)) (Complex.I * (R / ((N : ℝ) * Real.sqrt (N : ℝ)) : ℝ))
    _ = |B| / (N : ℝ) + |R| / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
      rw [abs_div, abs_div, abs_of_pos hNp, abs_of_pos (mul_pos hNp hs)]
    _ ≤ |B| / (N : ℝ) + |R| / (N : ℝ) := by
      apply add_le_add (le_refl _)
      exact div_le_div_of_nonneg_left (abs_nonneg _) hNp (by nlinarith)
    _ = _ := by ring

lemma feature_rate_norm_power_exp_bound (a E : ℂ) (B R r A : ℝ)
    (hr : 1 ≤ r) (ha : ‖a‖ ≤ r)
    (N : ℕ) (hN : 1 ≤ N) (hA : r ^ N ≤ A)
    (he : Real.exp (B / (N : ℝ)) ≤ r) (hB : Real.exp B ≤ A)
    (hExpansion : a = 1 + (B / (N : ℝ) : ℝ) +
      Complex.I * (R / ((N : ℝ) * Real.sqrt (N : ℝ)) : ℝ) + E / ((N : ℝ) ^ 2 : ℝ)) :
    ‖a ^ N - Complex.exp ((B : ℂ) + Complex.I * (R / Real.sqrt (N : ℝ) : ℝ))‖ ≤
      A / (N : ℝ) * (‖E‖ + 3 * (|B| + |R|) ^ 2) := by
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNp
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hA0 : 0 ≤ A := (Real.exp_pos B).le.trans hB
  let u : ℂ := (B / (N : ℝ) : ℝ) + Complex.I * (R / ((N : ℝ) * Real.sqrt (N : ℝ)) : ℝ)
  let Y : ℝ := |B| + |R|
  have hY0 : 0 ≤ Y := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have huY : ‖u‖ ≤ Y / (N : ℝ) := feature_rate_norm_increment_le B R N hN
  have huExp : ‖Complex.exp u‖ ≤ r := by
    rw [Complex.norm_exp]
    simpa only [u, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using he
  have hExp : Complex.exp ((N : ℂ) * u) =
      Complex.exp ((B : ℂ) + Complex.I * (R / Real.sqrt (N : ℝ) : ℝ)) := by
    congr 1
    dsimp [u]
    push_cast
    field_simp
    <;> ring
  have hδ : ‖a - (1 + u)‖ = ‖E‖ / (N : ℝ) ^ 2 := by
    have hd : a - (1 + u) = E / ((N : ℝ) ^ 2 : ℝ) := by rw [hExpansion]; dsimp [u]; ring
    rw [hd, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hu : ‖u‖ ≤ 1
  · have hp := feature_rate_norm_power_sub_of_bound a (Complex.exp u) r A hr ha huExp N hN hA
    rw [← Complex.exp_nat_mul, hExp] at hp
    have hi := feature_rate_norm_increment_remainder a u (‖E‖ / (N : ℝ) ^ 2) hu hδ.le
    have hu2 : ‖u‖ ^ 2 ≤ (Y / (N : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) huY 2
    calc
      _ ≤ (N : ℝ) * A * (‖E‖ / (N : ℝ) ^ 2 + ‖u‖ ^ 2) :=
        hp.trans (mul_le_mul_of_nonneg_left hi (mul_nonneg hNp.le hA0))
      _ ≤ (N : ℝ) * A * (‖E‖ / (N : ℝ) ^ 2 + (Y / (N : ℝ)) ^ 2) := by gcongr
      _ = A / (N : ℝ) * (‖E‖ + Y ^ 2) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hA0 hNp.le)
        dsimp [Y]
        nlinarith [sq_nonneg (|B| + |R|)]
  · have hY : (N : ℝ) < Y := by
      have hh : 1 < Y / (N : ℝ) := (lt_of_not_ge hu).trans_le huY
      simpa only [one_mul] using (lt_div_iff₀ hNp).mp hh
    have hY1 : 1 ≤ Y := hN1.trans hY.le
    have hYs : (N : ℝ) ≤ Y ^ 2 := by nlinarith [sq_nonneg (Y - 1)]
    have hc : ‖a ^ N - Complex.exp ((B : ℂ) + Complex.I * (R / Real.sqrt (N : ℝ) : ℝ))‖ ≤ 2 * A := by
      apply (norm_sub_le _ _).trans
      have hap : ‖a ^ N‖ ≤ A := by
        rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) ha N).trans hA
      have hep : ‖Complex.exp ((B : ℂ) + Complex.I * (R / Real.sqrt (N : ℝ) : ℝ))‖ ≤ A := by
        rw [Complex.norm_exp]
        simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hB
      linarith
    calc
      _ ≤ 2 * A := hc
      _ = A / (N : ℝ) * (2 * (N : ℝ)) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hA0 hNp.le)
        dsimp [Y] at hYs ⊢
        nlinarith [norm_nonneg E]

lemma feature_rate_norm_power_centered_bound (a E : ℂ) (B R r A : ℝ)
    (hr : 1 ≤ r) (ha : ‖a‖ ≤ r)
    (N : ℕ) (hN : 1 ≤ N) (hA : r ^ N ≤ A)
    (he : Real.exp (B / (N : ℝ)) ≤ r) (hB : Real.exp B ≤ A)
    (hExpansion : a = 1 + (B / (N : ℝ) : ℝ) +
      Complex.I * (R / ((N : ℝ) * Real.sqrt (N : ℝ)) : ℝ) + E / ((N : ℝ) ^ 2 : ℝ)) :
    ‖a ^ N - (Real.exp B : ℝ) - Complex.I * (Real.exp B * R / Real.sqrt (N : ℝ) : ℝ)‖ ≤
      A / (N : ℝ) * (‖E‖ + 6 * B ^ 2 + 9 * R ^ 2) := by
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hA0 : 0 ≤ A := (Real.exp_pos B).le.trans hB
  have hy : (|B| + |R|) ^ 2 ≤ 2 * B ^ 2 + 2 * R ^ 2 := by nlinarith [sq_nonneg (|B| - |R|), sq_abs B, sq_abs R]
  have hi := feature_rate_norm_power_exp_bound a E B R r A hr ha N hN hA he hB hExpansion
  have hc : ‖Complex.exp (Complex.I * (R / Real.sqrt (N : ℝ) : ℝ)) - 1 -
      Complex.I * (R / Real.sqrt (N : ℝ) : ℝ)‖ ≤ 3 * R ^ 2 / (N : ℝ) := by
    have hh := norm_exp_linear_remainder_unit_modulus (Complex.I * (R / Real.sqrt (N : ℝ) : ℝ))
      (Complex.norm_exp_I_mul_ofReal _)
    simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, div_pow, Real.sq_sqrt hNp.le, mul_div_assoc] using hh
  have hEq : a ^ N - (Real.exp B : ℝ) - Complex.I * (Real.exp B * R / Real.sqrt (N : ℝ) : ℝ) =
      (a ^ N - Complex.exp ((B : ℂ) + Complex.I * (R / Real.sqrt (N : ℝ) : ℝ))) +
      (Real.exp B : ℝ) * (Complex.exp (Complex.I * (R / Real.sqrt (N : ℝ) : ℝ)) - 1 -
        Complex.I * (R / Real.sqrt (N : ℝ) : ℝ)) := by
    rw [Complex.exp_add, Complex.ofReal_exp]
    push_cast
    ring
  rw [hEq]
  apply (norm_add_le _ _).trans
  have hPhase : ‖(Real.exp B : ℝ) * (Complex.exp (Complex.I * (R / Real.sqrt (N : ℝ) : ℝ)) - 1 -
      Complex.I * (R / Real.sqrt (N : ℝ) : ℝ))‖ ≤ A / (N : ℝ) * (3 * R ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos B)]
    calc
      _ ≤ Real.exp B * (3 * R ^ 2 / (N : ℝ)) := mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ ≤ A * (3 * R ^ 2 / (N : ℝ)) := mul_le_mul_of_nonneg_right hB (by positivity)
      _ = _ := by ring
  have hsumb := add_le_add hi hPhase
  apply hsumb.trans
  have hys := mul_le_mul_of_nonneg_left hy (show 0 ≤ A / (N : ℝ) * 3 by positivity)
  nlinarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.feature_rate_norm_power_sub
#print axioms DGRHS.Gaussian.feature_rate_norm_power_sub

#check DGRHS.Gaussian.feature_rate_norm_power_sub_of_bound
#print axioms DGRHS.Gaussian.feature_rate_norm_power_sub_of_bound

#check DGRHS.Gaussian.feature_rate_norm_increment_remainder
#print axioms DGRHS.Gaussian.feature_rate_norm_increment_remainder

#check DGRHS.Gaussian.feature_rate_norm_increment_le
#print axioms DGRHS.Gaussian.feature_rate_norm_increment_le

#check DGRHS.Gaussian.feature_rate_norm_power_exp_bound
#print axioms DGRHS.Gaussian.feature_rate_norm_power_exp_bound

#check DGRHS.Gaussian.feature_rate_norm_power_centered_bound
#print axioms DGRHS.Gaussian.feature_rate_norm_power_centered_bound

#check DGRHS.Gaussian.norm_power_difference
#print axioms DGRHS.Gaussian.norm_power_difference

#check DGRHS.Gaussian.norm_power_difference_of_bound
#print axioms DGRHS.Gaussian.norm_power_difference_of_bound

#check DGRHS.Gaussian.norm_exp_increment_difference
#print axioms DGRHS.Gaussian.norm_exp_increment_difference

#check DGRHS.Gaussian.norm_imaginary_exp_remainder
#print axioms DGRHS.Gaussian.norm_imaginary_exp_remainder

#check DGRHS.Gaussian.norm_power_exp_difference
#print axioms DGRHS.Gaussian.norm_power_exp_difference
