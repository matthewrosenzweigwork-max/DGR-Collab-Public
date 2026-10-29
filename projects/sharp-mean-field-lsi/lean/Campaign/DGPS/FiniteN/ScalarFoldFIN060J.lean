import DGPS.FiniteN.ScalarFoldFIN060I

/-!
# FIN060 (part J): the particle Poincare and LSI power bounds for the scalar fold model
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS DGPS.Models DGPS.Particle

/-- Particle Poincare rate `>= c' N^(-1/3)` for every `N >= 1`. -/
theorem poincare_lower_FIN060 {κ : ℝ} (hκ : 2 < κ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c' * (N : ℝ) ^ (-(1 / 3 : ℝ))) ≤
        particlePoincareRate (scalarCosine κ (scalarFoldField κ)) N := by
  obtain ⟨P0, hP0, N₀, hP⟩ := poincare_inverse_FIN060 hκ
  refine all_N_FIN060 (by norm_num) (fun N => particlePoincareRate
    (scalarCosine κ (scalarFoldField κ)) N) (fun N => ?_) (c := 1 / P0) (N₀ := N₀)
    (by positivity) (fun N hN => ?_)
  · obtain ⟨r, hr, h⟩ := DGPS.FiniteN.PositiveRate.particlePoincare_pos_aux
      (scalarCosine κ (scalarFoldField κ)) N
    exact ⟨r, hr, (le_particlePoincareRate_iff_forall _ N r).2 fun f _ => h f⟩
  · rw [le_particlePoincareRate_iff_forall]
    intro f hf
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have hpos : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hinv : 1 / P0 * (N : ℝ) ^ (-(1 / 3 : ℝ)) = (P0 * (N : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (by linarith), mul_inv, one_div]
    rw [hinv, inv_mul_le_iff₀ (by positivity)]
    exact hP N hN f

/-- Particle unrestricted LSI rate `>= c'' N^(-4/3)` for every `N >= 1`. -/
theorem lsi_lower_FIN060 {κ : ℝ} (hκ : 2 < κ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c' * (N : ℝ) ^ (-(4 / 3 : ℝ))) ≤
        particleRateAll (scalarCosine κ (scalarFoldField κ)) N := by
  obtain ⟨P0, hP0, N₀, hP⟩ := poincare_inverse_FIN060 hκ
  have hκ0 : 0 < κ := by linarith
  set h := scalarFoldField κ with hh
  set a : ℝ := 2 / (4 * Real.pi ^ 2) with ha
  have ha0 : 0 < a := by positivity
  set M0 : ℝ := a + (|h| + κ + 2) * P0 with hM0
  have hM0pos : 0 < M0 := by positivity
  refine all_N_FIN060 (by norm_num) (fun N => particleRateAll (scalarCosine κ h) N)
    (fun N => ?_) (c := 2 / M0) (N₀ := N₀) (by positivity) (fun N hN => ?_)
  · exact DGPS.FiniteN.PositiveRate.particleRateAll_pos_aux _ N
  · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have hu : 1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have hupos : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := by linarith
    have hP4 : (N : ℝ) ^ (4 / 3 : ℝ) = N * (N : ℝ) ^ (1 / 3 : ℝ) := by
      rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    have hb : 0 ≤ (|h| + κ) * (N : ℝ) := by positivity
    have hmain := lsi_of_poincare_defect_FIN060 (scalarCosine κ h) N
      (P := P0 * (N : ℝ) ^ (1 / 3 : ℝ)) (a := a) (b := (|h| + κ) * (N : ℝ))
      (by positivity) ha0.le hb (fun f => hP N hN f) (entropy_defect_FIN060 h hκ0.le N)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
    have hden : a + ((|h| + κ) * (N : ℝ) + 2) * (P0 * (N : ℝ) ^ (1 / 3 : ℝ)) ≤
        M0 * (N : ℝ) ^ (4 / 3 : ℝ) := by
      rw [hP4, hM0]
      set u : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
      set n : ℝ := (N : ℝ)
      have h1 : 1 ≤ n * u := by nlinarith
      have h2 : u ≤ n * u := by nlinarith
      have hab : 0 ≤ |h| + κ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 ha0.le, mul_le_mul_of_nonneg_left h2 hP0.le,
        mul_nonneg hab hP0.le, mul_nonneg (mul_nonneg hab hP0.le) (show 0 ≤ n * u by positivity)]
    have hpos : 0 < a + ((|h| + κ) * (N : ℝ) + 2) * (P0 * (N : ℝ) ^ (1 / 3 : ℝ)) := by positivity
    have hnp : (N : ℝ) ^ (-(4 / 3 : ℝ)) = ((N : ℝ) ^ (4 / 3 : ℝ))⁻¹ :=
      Real.rpow_neg (by linarith) _
    rw [hnp, ← div_eq_mul_inv, div_div]
    exact div_le_div_of_nonneg_left (by norm_num) hpos hden

end DGPS.FiniteN.ScalarFoldFIN060
