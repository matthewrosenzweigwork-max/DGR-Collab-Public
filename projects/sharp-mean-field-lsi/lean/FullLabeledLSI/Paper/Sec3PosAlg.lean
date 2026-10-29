import Mathlib

/-!
# Proposition 3.4: the `ℝ≥0∞` algebra of the final quotient bound
-/

open scoped ENNReal

namespace SharpLSI.FL

theorem final_quotient_ineq {r a g S D Y : ℝ≥0∞} (hr0 : r ≠ 0) (hrt : r ≠ ⊤) (ha0 : a ≠ 0)
    (hDt : D ≠ ⊤) (hYt : Y ≠ ⊤) (hG : 0 < g + S) (h1 : 2 * r * g ≤ D) (h2 : a * S ≤ D * Y) :
    (r⁻¹ + 2 * a⁻¹ * Y)⁻¹ ≤ D / (2 * (g + S)) := by
  set K := r⁻¹ + 2 * a⁻¹ * Y with hK
  have hstep1 : 2 * g ≤ r⁻¹ * D := by
    rw [← ENNReal.mul_le_iff_le_inv hr0 hrt]
    calc r * (2 * g) = 2 * r * g := by ring
      _ ≤ D := h1
  have hstep2 : S ≤ a⁻¹ * (D * Y) := by
    by_cases hat : a = ⊤
    · have hS : S = 0 := by
        by_contra hS
        have : a * S = ⊤ := by rw [hat]; exact ENNReal.top_mul hS
        rw [this] at h2
        exact (ENNReal.mul_ne_top hDt hYt) (top_le_iff.1 h2)
      rw [hS]; exact zero_le
    · exact (ENNReal.mul_le_iff_le_inv ha0 hat).1 h2
  have hstep3 : 2 * (g + S) ≤ D * K := by
    calc 2 * (g + S) = 2 * g + 2 * S := by ring
      _ ≤ r⁻¹ * D + 2 * (a⁻¹ * (D * Y)) := add_le_add hstep1 (by gcongr)
      _ = D * K := by rw [hK]; ring
  by_cases hKt : K = ⊤
  · rw [hKt]; simp
  have hK0 : K ≠ 0 := by
    intro h
    have : r⁻¹ = 0 := by
      rw [hK] at h
      exact le_antisymm (h ▸ le_self_add) zero_le
    exact ENNReal.inv_ne_zero.2 hrt this
  have h2G : 2 * (g + S) ≠ 0 := by
    intro h
    have : g + S = 0 := by
      rcases mul_eq_zero.1 h with h | h
      · norm_num at h
      · exact h
    exact absurd this hG.ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl h2G) (Or.inr hDt)]
  calc K⁻¹ * (2 * (g + S)) ≤ K⁻¹ * (D * K) := by gcongr
    _ = D := by
        rw [mul_comm D K, ← mul_assoc, ENNReal.inv_mul_cancel hK0 hKt, one_mul]

end SharpLSI.FL
