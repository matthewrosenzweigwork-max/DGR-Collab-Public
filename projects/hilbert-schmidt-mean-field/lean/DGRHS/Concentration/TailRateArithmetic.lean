import DGRHS.Concentration.FourScaleTail

noncomputable section
namespace DGRHS.Concentration

/-- The four-regime source rate, with real division. Positive scales have the
usual source interpretation; the parameter tail separately covers zero scales. -/
def glzTailRate (t A B C D : ℝ) : ℝ :=
  min ((t/C)^2) (min (t/D) (min ((t/B)^(2/3 : ℝ)) ((t/A)^(1/2 : ℝ))))

lemma glzTailRate_nonneg (t A B C D : ℝ) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D) :
    0 ≤ glzTailRate t A B C D := by unfold glzTailRate; positivity

lemma glz_rate_threshold (u a A B C D : ℝ) (hu : 0 ≤ u) (ha : 0 ≤ a)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hRate : u ≤ glzTailRate a A B C D) : glzRealScale u A B C D ≤ 4*a := by
  have h1 : u ≤ (a/C)^2 := hRate.trans (min_le_left _ _)
  have hrest := hRate.trans (min_le_right _ _)
  have h2 : u ≤ a/D := hrest.trans (min_le_left _ _)
  have hlast := hrest.trans (min_le_right _ _)
  have h3 : u ≤ (a/B)^(2/3 : ℝ) := hlast.trans (min_le_left _ _)
  have h4 : u ≤ (a/A)^(1/2 : ℝ) := hlast.trans (min_le_right _ _)
  have hsC : Real.sqrt u ≤ a/C := by
    nlinarith [Real.sq_sqrt hu,Real.sqrt_nonneg u,div_nonneg ha hC.le]
  have hCterm : Real.sqrt u*C ≤ a := by
    have hh := mul_le_mul_of_nonneg_right hsC hC.le
    rwa [div_mul_cancel₀ _ hC.ne'] at hh
  have hDterm : u*D ≤ a := by
    have hh := mul_le_mul_of_nonneg_right h2 hD.le
    rwa [div_mul_cancel₀ _ hD.ne'] at hh
  have hBpow : u^3 ≤ (a/B)^2 := by
    have hh := pow_le_pow_left₀ hu h3 3
    have he : ((a/B)^(2/3 : ℝ))^3 = (a/B)^2 := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (div_nonneg ha hB.le)]
      norm_num
    rwa [he] at hh
  have hBsq : (u*Real.sqrt u)^2 = u^3 := by
    rw [mul_pow,Real.sq_sqrt hu]
    ring
  have hsB : u*Real.sqrt u ≤ a/B := by
    nlinarith [hBsq,mul_nonneg hu (Real.sqrt_nonneg u),div_nonneg ha hB.le]
  have hBterm : u*Real.sqrt u*B ≤ a := by
    have hh := mul_le_mul_of_nonneg_right hsB hB.le
    rwa [div_mul_cancel₀ _ hB.ne'] at hh
  have hApow : u^2 ≤ a/A := by
    have hh := pow_le_pow_left₀ hu h4 2
    have he : ((a/A)^(1/2 : ℝ))^2 = a/A := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (div_nonneg ha hA.le)]
      norm_num
    rwa [he] at hh
  have hAterm : u^2*A ≤ a := by
    have hh := mul_le_mul_of_nonneg_right hApow hA.le
    rwa [div_mul_cancel₀ _ hA.ne'] at hh
  unfold glzRealScale
  linarith

lemma glz_rate_scaled_lower (t A B C D b : ℝ) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 1 ≤ b) :
    glzTailRate t A B C D/b^2 ≤ glzTailRate (t/b) A B C D := by
  have hb0 : 0 < b := by linarith
  have hbb : b ≤ b^2 := by nlinarith
  have hden (x : ℝ) (hx : 0 ≤ x) (r : ℝ) (hr : r ≤ 2) :
      x^r/b^2 ≤ (x/b)^r := by
    rw [Real.div_rpow hx hb0.le]
    have he : b^r ≤ b^2 := by
      calc
        b^r ≤ b^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hr
        _ = b^2 := by norm_num
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) (Real.rpow_pos_of_pos hb0 _) he
  have hdiv (a : ℝ) : (t/b)/a = (t/a)/b := by ring
  unfold glzTailRate
  rw [hdiv C,hdiv D,hdiv B,hdiv A]
  simp only [div_pow]
  apply le_min
  · exact div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg b)
  · apply le_min
    · exact (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (sq_nonneg b)).trans
        (div_le_div_of_nonneg_left (div_nonneg ht hD) hb0 hbb)
    · apply le_min
      · exact (div_le_div_of_nonneg_right ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) (sq_nonneg b)).trans
          (hden (t/B) (div_nonneg ht hB) (2/3) (by norm_num))
      · exact (div_le_div_of_nonneg_right ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (sq_nonneg b)).trans
          (hden (t/A) (div_nonneg ht hA) (1/2) (by norm_num))

#print axioms DGRHS.Concentration.glz_rate_threshold
#print axioms DGRHS.Concentration.glz_rate_scaled_lower
end DGRHS.Concentration
