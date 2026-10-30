import DGPS.Frontier.FIN068.Close

/-! Actual quartic saddle weights on the anisotropically scaled rare rectangle.
This is the local potential input to FIN071; no rare-event mass estimate is assumed. -/

open DGPS.Models DGPS.Frontier.FIN068 DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

/-- On the original-coordinate rectangle of widths `s^2` and `s`, the actual
potential differs from its remote saddle value by at most a fixed multiple of `s^4`.
The radius and constant are chosen before the scale and the point. -/
theorem quartic_rare_rectangle_potential :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ s u y : ℝ,
      0 ≤ s → s ≤ δ → |u| ≤ s ^ 2 → |y| ≤ s →
      |quarticPsi_FIN066 !₂[-4 + u, y] - quarticPsi_FIN066 !₂[-4, 0]| ≤ C * s ^ 4 := by
  obtain ⟨δ, M, hδ, hδ1, hM, hTaylor⟩ := weighted_expansion_FIN068CLOSE
  have hA := exact_negative_reduced_quartic_coefficient.1.2.1
  have hD := exact_negative_reduced_quartic_coefficient.1.2.2.1
  let C := quarticA_FIN06803 / 2 + quarticD_FIN06803 / 32 +
    quarticD_FIN06803 / 512 + 8 * M
  refine ⟨δ, C, hδ, hδ1.le, by dsimp [C]; positivity, fun s u y hs hsδ hu hy => ?_⟩
  have hs1 : s ≤ 1 := hsδ.trans hδ1.le
  have hs2 : s ^ 2 ≤ s := by nlinarith
  have hy2 : y ^ 2 ≤ s ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hu2 : u ^ 2 ≤ s ^ 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
    simpa only [sq_abs, ← pow_mul] using h
  have hy4 : y ^ 4 ≤ s ^ 4 := by
    have h := pow_le_pow_left₀ (sq_nonneg y) hy2 2
    simpa only [← pow_mul] using h
  have huy : |u| * y ^ 2 ≤ s ^ 4 := by
    calc
      _ ≤ s ^ 2 * s ^ 2 := mul_le_mul hu hy2 (sq_nonneg y) (sq_nonneg s)
      _ = _ := by ring
  have hsum : (|u| + y ^ 2) ^ 3 ≤ 8 * s ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ |u| + y ^ 2)
      (show |u| + y ^ 2 ≤ 2 * s ^ 2 by linarith) 3
    have hs21 : s ^ 2 ≤ 1 := hs2.trans hs1
    have hmul := mul_le_mul_of_nonneg_left hs21 (by positivity : 0 ≤ 8 * s ^ 4)
    nlinarith only [h, hmul]
  have hrem := (hTaylor u y (hu.trans (hs2.trans hsδ))
    (hy2.trans (hs2.trans hsδ))).trans (mul_le_mul_of_nonneg_left hsum hM)
  have hp1 : |quarticA_FIN06803 * u ^ 2 / 2| ≤ quarticA_FIN06803 / 2 * s ^ 4 := by
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_nonneg (sq_nonneg u)]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hu2 hA.le]
  have hp2 : |quarticD_FIN06803 * u * y ^ 2 / 32| ≤ quarticD_FIN06803 / 32 * s ^ 4 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hD, abs_of_nonneg (sq_nonneg y)]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left huy hD.le]
  have hp3 : |quarticD_FIN06803 * y ^ 4 / 512| ≤ quarticD_FIN06803 / 512 * s ^ 4 := by
    rw [abs_div, abs_mul, abs_of_pos hD, abs_of_nonneg (by positivity : 0 ≤ y ^ 4)]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hy4 hD.le]
  have hp := (abs_add_le (quarticA_FIN06803 * u ^ 2 / 2 - quarticD_FIN06803 * u * y ^ 2 / 32)
    (quarticD_FIN06803 * y ^ 4 / 512)).trans
      (add_le_add ((abs_sub _ _).trans (add_le_add hp1 hp2)) hp3)
  have ht := abs_add_le (quarticPsi_FIN066 !₂[-4 + u, y] - quarticPsi_FIN066 !₂[-4, 0] -
      (quarticA_FIN06803 * u ^ 2 / 2 - quarticD_FIN06803 * u * y ^ 2 / 32 +
        quarticD_FIN06803 * y ^ 4 / 512))
    (quarticA_FIN06803 * u ^ 2 / 2 - quarticD_FIN06803 * u * y ^ 2 / 32 +
      quarticD_FIN06803 * y ^ 4 / 512)
  rw [sub_add_cancel] at ht
  dsimp only [C]
  nlinarith only [ht, hp, hrem]

/-- The genuine Gibbs weight on a rare rectangle is comparable to its saddle
weight by constants independent of particle number whenever `N*s^4 ≤ 1`. -/
theorem quartic_rare_rectangle_weight :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ N s u y : ℝ,
      0 ≤ N → 0 ≤ s → s ≤ δ → N * s ^ 4 ≤ 1 → |u| ≤ s ^ 2 → |y| ≤ s →
      Real.exp (-C) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) ≤
        Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + u, y])) ∧
      Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + u, y])) ≤
        Real.exp C * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hpot⟩ := quartic_rare_rectangle_potential
  refine ⟨δ, C, hδ, hδ1, hC, fun N s u y hN hs hsδ hscale hu hy => ?_⟩
  have hb := abs_le.mp (hpot s u y hs hsδ hu hy)
  have hlo := mul_le_mul_of_nonneg_left hb.1 hN
  have hhi := mul_le_mul_of_nonneg_left hb.2 hN
  have hc := mul_le_mul_of_nonneg_left hscale hC.le
  constructor
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hhi, hc]
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hlo, hc]

end DGPS.FiniteN
