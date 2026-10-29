import DGRHS.Concentration.IidOffDiagonal

noncomputable section
open scoped ENNReal
namespace DGRHS.Concentration

/-- For positive t, division by a zero source scale contributes infinite rate. -/
def glzRateTerm (t s p : ℝ) : ℝ≥0∞ :=
  if s = 0 then ∞ else ENNReal.ofReal ((t/s)^p)

def glzExtendedRate (t A B C D : ℝ) : ℝ≥0∞ :=
  min (glzRateTerm t C 2) (min (glzRateTerm t D 1)
    (min (glzRateTerm t B (2/3)) (glzRateTerm t A (1/2))))

lemma glzRateTerm_top_iff (t s p : ℝ) : glzRateTerm t s p = ∞ ↔ s = 0 := by
  by_cases hs : s = 0 <;> simp [glzRateTerm,hs]

lemma glzExtendedRate_top_iff (t A B C D : ℝ) :
    glzExtendedRate t A B C D = ∞ ↔ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  constructor
  · intro hh
    have he := congrArg (fun x : ℝ≥0∞ ↦ x) hh
    have hC : glzRateTerm t C 2 = ∞ := top_unique (by rw [← he]; exact min_le_left _ _)
    have hrest : ∞ ≤ min (glzRateTerm t D 1)
        (min (glzRateTerm t B (2/3)) (glzRateTerm t A (1/2))) := by
      rw [← he]
      exact min_le_right _ _
    have hD : glzRateTerm t D 1 = ∞ := top_unique (hrest.trans (min_le_left _ _))
    have hB : glzRateTerm t B (2/3) = ∞ :=
      top_unique (hrest.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hA : glzRateTerm t A (1/2) = ∞ :=
      top_unique (hrest.trans ((min_le_right _ _).trans (min_le_right _ _)))
    exact ⟨(glzRateTerm_top_iff _ _ _).mp hA,(glzRateTerm_top_iff _ _ _).mp hB,
      (glzRateTerm_top_iff _ _ _).mp hC,(glzRateTerm_top_iff _ _ _).mp hD⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    simp [glzExtendedRate,glzRateTerm]

lemma glzRateTerm_real_le {t s p r : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (h : ENNReal.ofReal r ≤ glzRateTerm t s p) :
    s = 0 ∨ r ≤ (t/s)^p := by
  by_cases hz : s = 0
  · exact Or.inl hz
  · right
    simp only [glzRateTerm,ite_eq_right hz] at h
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    have hr : r ≤ (ENNReal.ofReal r).toReal := by
      by_cases hr0 : 0 ≤ r
      · simp only [ENNReal.toReal_ofReal hr0,le_refl]
      · exact (le_of_not_ge hr0).trans ENNReal.toReal_nonneg
    exact hr.trans (by simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (div_nonneg ht hs) _)] using hh)

lemma glzExtendedRate_real_controls (t A B C D : ℝ) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (C = 0 ∨ (glzExtendedRate t A B C D).toReal ≤ (t/C)^2) ∧
    (D = 0 ∨ (glzExtendedRate t A B C D).toReal ≤ t/D) ∧
    (B = 0 ∨ (glzExtendedRate t A B C D).toReal ≤ (t/B)^(2/3 : ℝ)) ∧
    (A = 0 ∨ (glzExtendedRate t A B C D).toReal ≤ (t/A)^(1/2 : ℝ)) := by
  have h0 := ENNReal.ofReal_toReal_le (a := glzExtendedRate t A B C D)
  have hc := glzRateTerm_real_le ht hC (h0.trans (min_le_left _ _))
  have hrest := h0.trans (min_le_right _ _)
  have hd := glzRateTerm_real_le ht hD (hrest.trans (min_le_left _ _))
  have hb := glzRateTerm_real_le ht hB (hrest.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ha := glzRateTerm_real_le ht hA (hrest.trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨by simpa using hc,by simpa using hd,hb,ha⟩

/-- The four scalar rate implications, with each zero scale handled before division. -/
lemma glz_zero_scale_rate_threshold (u a A B C D : ℝ) (hu : 0 ≤ u) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h1 : C = 0 ∨ u ≤ (a/C)^2) (h2 : D = 0 ∨ u ≤ a/D)
    (h3 : B = 0 ∨ u ≤ (a/B)^(2/3 : ℝ))
    (h4 : A = 0 ∨ u ≤ (a/A)^(1/2 : ℝ)) : glzRealScale u A B C D ≤ 4*a := by
  have hCterm : Real.sqrt u*C ≤ a := by
    rcases h1 with rfl | h1
    · simpa using ha
    · by_cases hz : C = 0
      · simp [hz,ha]
      · have hsC : Real.sqrt u ≤ a/C := by
          nlinarith [Real.sq_sqrt hu,Real.sqrt_nonneg u,div_nonneg ha hC]
        have hh := mul_le_mul_of_nonneg_right hsC hC
        rwa [div_mul_cancel₀ _ hz] at hh
  have hDterm : u*D ≤ a := by
    rcases h2 with rfl | h2
    · simpa using ha
    · by_cases hz : D = 0
      · simp [hz,ha]
      · have hh := mul_le_mul_of_nonneg_right h2 hD
        rwa [div_mul_cancel₀ _ hz] at hh
  have hBterm : u*Real.sqrt u*B ≤ a := by
    rcases h3 with rfl | h3
    · simpa using ha
    · by_cases hz : B = 0
      · simp [hz,ha]
      · have hBpow : u^3 ≤ (a/B)^2 := by
          have hh := pow_le_pow_left₀ hu h3 3
          have he : ((a/B)^(2/3 : ℝ))^3 = (a/B)^2 := by
            rw [← Real.rpow_natCast,← Real.rpow_mul (div_nonneg ha hB)]
            norm_num
          rwa [he] at hh
        have hBsq : (u*Real.sqrt u)^2 = u^3 := by rw [mul_pow,Real.sq_sqrt hu]; ring
        have hsB : u*Real.sqrt u ≤ a/B := by
          nlinarith [hBsq,mul_nonneg hu (Real.sqrt_nonneg u),div_nonneg ha hB]
        have hh := mul_le_mul_of_nonneg_right hsB hB
        rwa [div_mul_cancel₀ _ hz] at hh
  have hAterm : u^2*A ≤ a := by
    rcases h4 with rfl | h4
    · simpa using ha
    · by_cases hz : A = 0
      · simp [hz,ha]
      · have hApow : u^2 ≤ a/A := by
          have hh := pow_le_pow_left₀ hu h4 2
          have he : ((a/A)^(1/2 : ℝ))^2 = a/A := by
            rw [← Real.rpow_natCast,← Real.rpow_mul (div_nonneg ha hA)]
            norm_num
          rwa [he] at hh
        have hh := mul_le_mul_of_nonneg_right hApow hA
        rwa [div_mul_cancel₀ _ hz] at hh
  unfold glzRealScale
  linarith

lemma glz_extended_rate_scaled_threshold (t A B C D b : ℝ) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 1 ≤ b) :
    glzRealScale ((glzExtendedRate t A B C D).toReal/b^2) A B C D ≤ 4*(t/b) := by
  let r := (glzExtendedRate t A B C D).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hb0 : 0 < b := by linarith
  have hbb : b ≤ b^2 := by nlinarith
  have hden (x : ℝ) (hx : 0 ≤ x) (p : ℝ) (hp : p ≤ 2) :
      x^p/b^2 ≤ (x/b)^p := by
    rw [Real.div_rpow hx hb0.le]
    have he : b^p ≤ b^2 := by
      calc
        b^p ≤ b^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb hp
        _ = b^2 := by norm_num
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) (Real.rpow_pos_of_pos hb0 _) he
  have hdiv (s : ℝ) : (t/b)/s = (t/s)/b := by ring
  obtain ⟨hc,hd,hBnd,hAnd⟩ := glzExtendedRate_real_controls t A B C D ht hA hB hC hD
  apply glz_zero_scale_rate_threshold (r/b^2) (t/b) A B C D
    (div_nonneg hr (sq_nonneg _)) (div_nonneg ht hb0.le) hA hB hC hD
  · rcases hc with hz | hc
    · exact Or.inl hz
    · right
      rw [hdiv C,div_pow]
      exact div_le_div_of_nonneg_right hc (sq_nonneg _)
  · rcases hd with hz | hd
    · exact Or.inl hz
    · right
      rw [hdiv D]
      exact (div_le_div_of_nonneg_right hd (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left (div_nonneg ht hD) hb0 hbb)
  · rcases hBnd with hz | hBnd
    · exact Or.inl hz
    · right
      rw [hdiv B]
      exact (div_le_div_of_nonneg_right hBnd (sq_nonneg _)).trans
        (hden (t/B) (div_nonneg ht hB) (2/3) (by norm_num))
  · rcases hAnd with hz | hAnd
    · exact Or.inl hz
    · right
      rw [hdiv A]
      exact (div_le_div_of_nonneg_right hAnd (sq_nonneg _)).trans
        (hden (t/A) (div_nonneg ht hA) (1/2) (by norm_num))

#print axioms DGRHS.Concentration.glzExtendedRate_top_iff
#print axioms DGRHS.Concentration.glz_zero_scale_rate_threshold
#print axioms DGRHS.Concentration.glz_extended_rate_scaled_threshold
end DGRHS.Concentration
