import DGRHS.Concentration.MasterBounded

noncomputable section
open scoped ENNReal
namespace DGRHS.Concentration

lemma glzRateTerm_lower_of_product {t s p x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x)
    (hp : 0 ≤ p) (hProd : x*s ≤ t) :
    ENNReal.ofReal (x^p) ≤ glzRateTerm t s p := by
  by_cases hz : s = 0
  · simp only [glzRateTerm,ite_eq_left hz,le_top]
  · have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    simp only [glzRateTerm,ite_eq_right hz]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx ((le_div_iff₀ hs0).mpr hProd) hp)

lemma glzExtendedRate_lower_of_thresholds {v t A B C D : ℝ}
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : Real.sqrt v*C ≤ t) (hd : v*D ≤ t)
    (hb : (v*Real.sqrt v)*B ≤ t) (ha : v^2*A ≤ t) :
    ENNReal.ofReal v ≤ glzExtendedRate t A B C D := by
  have hc' := glzRateTerm_lower_of_product hC (Real.sqrt_nonneg v) (by norm_num : (0 : ℝ) ≤ 2) hc
  have hd' := glzRateTerm_lower_of_product hD hv (by norm_num : (0 : ℝ) ≤ 1) hd
  have hb' := glzRateTerm_lower_of_product hB (mul_nonneg hv (Real.sqrt_nonneg v)) (by norm_num : (0 : ℝ) ≤ 2/3) hb
  have ha' := glzRateTerm_lower_of_product hA (sq_nonneg v) (by norm_num : (0 : ℝ) ≤ 1/2) ha
  have hbp : (v*Real.sqrt v)^(2/3 : ℝ) = v := by
    have he : v*Real.sqrt v = v^(3/2 : ℝ) := by
      by_cases hz : v = 0
      · simp [hz]
      · have hv0 : 0 < v := lt_of_le_of_ne hv (Ne.symm hz)
        rw [Real.sqrt_eq_rpow]
        calc
          _ = v^(1 : ℝ)*v^(1/2 : ℝ) := by rw [Real.rpow_one]
          _ = v^(1+1/2 : ℝ) := (Real.rpow_add hv0 _ _).symm
          _ = _ := by norm_num
    rw [he,← Real.rpow_mul hv]
    norm_num
  have hap : (v^2)^(1/2 : ℝ) = v := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hv]
    norm_num
  apply le_min
  · have he : (Real.sqrt v)^(2 : ℝ) = v := by
      calc
        _ = (Real.sqrt v)^(2 : ℕ) := Real.rpow_natCast _ 2
        _ = v := Real.sq_sqrt hv
    rwa [he] at hc' 
  · apply le_min
    · simpa only [Real.rpow_one] using hd'
    · exact le_min (by simpa only [hbp] using hb') (by simpa only [hap] using ha')

/-- The four-rate arithmetic in the source master proposition, with zero scales
represented by infinite rates before any division. -/
theorem master_rate_lower {n u L a A B C D : ℝ}
    (hn : 0 ≤ n) (hu : 1 ≤ u) (hL : 0 < L) (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAb : A ≤ a) (hBs : B^2 ≤ n/L) (hCs : C^2 ≤ n^2/L) (hDb : D ≤ n/L)
    (hGrowth : 2*L^2*u*(1+a) ≤ n) :
    ENNReal.ofReal (2*L*u) ≤ glzExtendedRate (2*n*u) A B C D := by
  have hu0 : 0 ≤ u := by linarith
  have hv : 0 ≤ 2*L*u := by positivity
  have ht : 0 ≤ 2*n*u := by positivity
  have hSmall : 2*L^2*u ≤ n := by
    calc
      _ ≤ 2*L^2*u*(1+a) := le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ n := hGrowth
  have hSmalla : 2*L^2*u*a ≤ n := by
    calc
      _ ≤ 2*L^2*u*(1+a) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ n := hGrowth
  apply glzExtendedRate_lower_of_thresholds hv hA hB hC hD
  · have hs : (Real.sqrt (2*L*u)*C)^2 ≤ (2*n*u)^2 := by
      rw [mul_pow,Real.sq_sqrt hv]
      calc
        _ ≤ (2*L*u)*(n^2/L) := mul_le_mul_of_nonneg_left hCs hv
        _ = 2*n^2*u := by field_simp
        _ ≤ (2*n*u)^2 := by
          have hh : u ≤ 2*u^2 := by nlinarith
          have he := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*n^2 by positivity)
          nlinarith only [he]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (2*L*u)) hC]
  · calc
      _ ≤ (2*L*u)*(n/L) := mul_le_mul_of_nonneg_left hDb hv
      _ = 2*n*u := by field_simp
  · have he : ((2*L*u)*Real.sqrt (2*L*u)*B)^2 = (2*L*u)^3*B^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hv]
      ring
    have hs : ((2*L*u)*Real.sqrt (2*L*u)*B)^2 ≤ (2*n*u)^2 := by
      rw [he]
      calc
        _ ≤ (2*L*u)^3*(n/L) := mul_le_mul_of_nonneg_left hBs (by positivity)
        _ = 8*L^2*u^3*n := by field_simp;ring
        _ ≤ (2*n*u)^2 := by
          have hh := mul_le_mul_of_nonneg_right hSmall (show 0 ≤ 4*n*u^2 by positivity)
          nlinarith only [hh]
    nlinarith [mul_nonneg (mul_nonneg hv (Real.sqrt_nonneg (2*L*u))) hB]
  · calc
      _ ≤ (2*L*u)^2*a := mul_le_mul_of_nonneg_left hAb (sq_nonneg _)
      _ ≤ 2*n*u := by
        have hh := mul_le_mul_of_nonneg_right hSmalla (show 0 ≤ 2*u by positivity)
        nlinarith only [hh]

#print axioms DGRHS.Concentration.master_rate_lower
#check @DGRHS.Concentration.master_rate_lower
end DGRHS.Concentration
