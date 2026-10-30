import DGPS.Frontier.STR029.T46

/-! The additional exact Haar moments for the ACTUAL scaled reference base
cos(t). Generic p/q profiles and the existing Wallis moment evaluator are reused;
the cos(3t) base profile of the older example is never identified with this one. -/

noncomputable section
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

theorem polynomial_scaled_cos_pbq_moment (A B C D : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t * Real.cos t * qFun_STR02945 C D 0 0 t) =
      (A * C + B * D) / 4 := by
  have he : ∀ t : ℝ, pFun_STR02945 A B t * Real.cos t * qFun_STR02945 C D 0 0 t =
      0 * Real.cos t ^ 0 + (-A * C + 2 * B * D) * Real.cos t ^ 2 +
      (2 * A * C - 2 * B * D) * Real.cos t ^ 4 + 0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 +
      (-B * C) * (Real.cos t ^ 1 * Real.sin t) +
      (2 * A * D + 2 * B * C) * (Real.cos t ^ 3 * Real.sin t) +
      0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946, q_cs_STR02946]
    linear_combination (2 * B * D * Real.cos t ^ 2) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 he, mean9_STR02946]
  ring

theorem polynomial_scaled_cos_p2b2_moment (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2 * Real.cos t ^ 2) =
      (3 * A ^ 2 + B ^ 2) / 8 := by
  have he : ∀ t : ℝ, pFun_STR02945 A B t ^ 2 * Real.cos t ^ 2 =
      0 * Real.cos t ^ 0 + B ^ 2 * Real.cos t ^ 2 +
      (A ^ 2 - B ^ 2) * Real.cos t ^ 4 + 0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 +
      0 * (Real.cos t ^ 1 * Real.sin t) +
      (2 * A * B) * (Real.cos t ^ 3 * Real.sin t) +
      0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946]
    linear_combination (B ^ 2 * Real.cos t ^ 2) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 he, mean9_STR02946]
  ring

theorem polynomial_scaled_cos_p3b_moment (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 3 * Real.cos t) =
      3 * A * (A ^ 2 + B ^ 2) / 8 := by
  have he : ∀ t : ℝ, pFun_STR02945 A B t ^ 3 * Real.cos t =
      0 * Real.cos t ^ 0 + (3 * A * B ^ 2) * Real.cos t ^ 2 +
      (A ^ 3 - 3 * A * B ^ 2) * Real.cos t ^ 4 + 0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 +
      B ^ 3 * (Real.cos t ^ 1 * Real.sin t) +
      (3 * A ^ 2 * B - B ^ 3) * (Real.cos t ^ 3 * Real.sin t) +
      0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946]
    linear_combination (3 * A * B ^ 2 * Real.cos t ^ 2 + B ^ 3 * Real.cos t * Real.sin t) *
      Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 he, mean9_STR02946]
  ring

end DGPS.Examples.PolynomialSpecies
