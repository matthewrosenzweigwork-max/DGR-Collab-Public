import Mathlib

/-!
# Resolvent iteration: exponent bookkeeping (LIP010c, partial)

Only the exponent ladder arithmetic for the resolvent iteration is proved here.
-/

namespace DGPS.Lipschitz

/-- Ladder exponents `p_k = 2d/(d-k)` for `d ≥ 2`, `k < d`. -/
noncomputable def ladderExponent (d k : ℕ) : ℝ := 2 * d / (d - k)

/-- Each ladder step gains strictly less than `1/d` in the Lebesgue exponent. -/
theorem ladderExponent_gap (d k : ℕ) (hk : k + 1 < d) :
    1 / ladderExponent d k - 1 / ladderExponent d (k + 1) < 1 / d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h1 : (0 : ℝ) < d - k := by
    have : (k : ℝ) < d := by exact_mod_cast (by omega : k < d)
    linarith
  have h2 : (0 : ℝ) < d - (k + 1 : ℕ) := by
    have : ((k + 1 : ℕ) : ℝ) < d := by exact_mod_cast hk
    linarith
  unfold ladderExponent
  have e : 1 / (2 * (d : ℝ) / (d - k)) - 1 / (2 * d / (d - ((k + 1 : ℕ) : ℝ)))
      = 1 / (2 * d) := by
    push_cast at *
    field_simp
    ring
  rw [e]
  apply one_div_lt_one_div_of_lt hd
  linarith

/-- The ladder starts at `p_0 = 2`. -/
theorem ladderExponent_zero (d : ℕ) (hd : 0 < d) : ladderExponent d 0 = 2 := by
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold ladderExponent
  simp
  field_simp

/-- The ladder exceeds `d` at the last step `k = d-1`: `p_{d-1} = 2d > d`. -/
theorem ladderExponent_last (d : ℕ) (hd : 0 < d) :
    ladderExponent d (d - 1) = 2 * d := by
  unfold ladderExponent
  have : ((d - 1 : ℕ) : ℝ) = d - 1 := by
    rw [Nat.cast_sub hd]; simp
  rw [this]; simp

end DGPS.Lipschitz
