import Mathlib

/-!
# Proposition 3.1: the pointwise algebra of the dissipation decomposition
-/

namespace SharpLSI.FL

open Finset

theorem diss_algebra {q d : ℕ} (θ s : Fin q → ℝ) (g : Fin q → Fin d → ℝ) (f G : Fin d → ℝ)
    {r : ℝ} (hr : 0 < r) (hs2 : ∑ a, θ a * s a ^ 2 = r ^ 2)
    (hsg : ∀ k, ∑ a, θ a * (s a * g a k) = r * G k) :
    ∑ a, θ a * ∑ k, (2 * g a k + s a * f k) ^ 2 =
      ∑ k, (2 * G k + r * f k) ^ 2 +
        ∑ a, θ a * ∑ k, (2 * g a k - s a * (2 * G k / r)) ^ 2 := by
  have key : ∀ k, ∑ a, θ a * (2 * g a k + s a * f k) ^ 2 =
      (2 * G k + r * f k) ^ 2 + ∑ a, θ a * (2 * g a k - s a * (2 * G k / r)) ^ 2 := by
    intro k
    have e1 : ∀ a, θ a * (2 * g a k + s a * f k) ^ 2 - θ a * (2 * g a k - s a * (2 * G k / r)) ^ 2 =
        (f k + 2 * G k / r) * (4 * (θ a * (s a * g a k)) + (f k - 2 * G k / r) * (θ a * s a ^ 2)) := by
      intro a; ring
    have e2 : ∑ a, (θ a * (2 * g a k + s a * f k) ^ 2 -
        θ a * (2 * g a k - s a * (2 * G k / r)) ^ 2) =
        (f k + 2 * G k / r) * (4 * (r * G k) + (f k - 2 * G k / r) * r ^ 2) := by
      simp_rw [e1]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsg k, hs2]
    rw [Finset.sum_sub_distrib] at e2
    have e3 : (f k + 2 * G k / r) * (4 * (r * G k) + (f k - 2 * G k / r) * r ^ 2) =
        (2 * G k + r * f k) ^ 2 := by
      field_simp
      ring
    linarith
  calc ∑ a, θ a * ∑ k, (2 * g a k + s a * f k) ^ 2
      = ∑ k, ∑ a, θ a * (2 * g a k + s a * f k) ^ 2 := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ = ∑ k, ((2 * G k + r * f k) ^ 2 + ∑ a, θ a * (2 * g a k - s a * (2 * G k / r)) ^ 2) :=
        Finset.sum_congr rfl fun k _ => key k
    _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

end SharpLSI.FL
