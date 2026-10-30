import DGPS.Examples.PolynomialSpeciesActualUniformCapture

noncomputable section
open NormedSpace
open DGPS.Frontier.STR029
namespace DGPS.Examples.PolynomialSpecies

theorem polynomial_scaled_parameters_norm_bound
    (h A B α σ M : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hM : 1 ≤ M)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hα : |α| ≤ M) (hσ : |σ| ≤ M) :
    ‖polynomialScaledParameters (h, (A, B, α, σ))‖ ≤ M * h := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have h2 : h ^ 2 ≤ h := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hh1)]
  have h4 : h ^ 4 ≤ h := by
    have hm := mul_le_mul h2 h2 (sq_nonneg h) hh
    nlinarith only [hm, h2]
  have hAh : |h * A| ≤ M * h := by
    rw [abs_mul, abs_of_nonneg hh]
    nlinarith only [mul_le_mul_of_nonneg_left hA hh]
  have hBh : |h * B| ≤ M * h := by
    rw [abs_mul, abs_of_nonneg hh]
    nlinarith only [mul_le_mul_of_nonneg_left hB hh]
  have hσh : |h ^ 4 * σ| ≤ M * h := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hh 4)]
    exact (mul_le_mul_of_nonneg_left hσ (pow_nonneg hh 4)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left h4 hM0])
  have hαh : |h ^ 2 * α| ≤ M * h := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
    exact (mul_le_mul_of_nonneg_left hα (sq_nonneg h)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left h2 hM0])
  have hhh : |h| ≤ M * h := by
    rw [abs_of_nonneg hh]
    nlinarith only [mul_le_mul_of_nonneg_right hM hh]
  simp only [polynomialScaledParameters, Prod.norm_def, Real.norm_eq_abs]
  exact max_le hAh (max_le hBh (max_le (max_le hhh hσh) hαh))

theorem polynomial_near_base_sine_ne_zero (A B α : ℝ) (j : Fin 2)
    (hnear : dist ((A, B), α) (polynomialQuarticCriticalBase j) <
      Real.sqrt ((1 + Real.sqrt 2) / 4) / 2) : B ≠ 0 := by
  have hs : 0 < Real.sqrt ((1 + Real.sqrt 2) / 4) := by positivity
  intro hB
  have hb : |B - (polynomialQuarticCriticalBase j).1.2| <
      Real.sqrt ((1 + Real.sqrt 2) / 4) / 2 := by
    change max (max |A - (polynomialQuarticCriticalBase j).1.1|
      |B - (polynomialQuarticCriticalBase j).1.2|)
      |α - (polynomialQuarticCriticalBase j).2| < _ at hnear
    exact (max_lt_iff.mp (max_lt_iff.mp hnear).1).2
  by_cases hj : j = 0
  · simp only [polynomialQuarticCriticalBase, if_pos hj, hB, zero_sub, abs_neg,
      abs_of_pos hs] at hb
    linarith
  · simp only [polynomialQuarticCriticalBase, if_neg hj, hB, zero_sub, neg_neg,
      abs_of_pos hs] at hb
    linarith

end DGPS.Examples.PolynomialSpecies
