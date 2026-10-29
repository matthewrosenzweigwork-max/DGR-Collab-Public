import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum.NatFactorial

noncomputable section
open Finset

namespace DGRHS.Concentration

lemma power_le_second_add_high (x : ℝ) (hx : 0 ≤ x) (m r : ℕ)
    (hr : 2 ≤ r) (hrm : r ≤ m) : x ^ r ≤ x ^ 2 + x ^ m := by
  by_cases hsmall : x ≤ 1
  · have hpow : x ^ r ≤ x ^ 2 := pow_le_pow_of_le_one hx hsmall hr
    have hhigh : 0 ≤ x ^ m := pow_nonneg hx m
    linarith
  · have hlarge : 1 ≤ x := by linarith
    have hpow : x ^ r ≤ x ^ m := pow_le_pow_right₀ hlarge hrm
    have hlow : 0 ≤ x ^ 2 := sq_nonneg x
    linarith

lemma factorial_lower_shift (q : ℕ) : 2 * 3 ^ q ≤ (q + 2).factorial := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    rw [show q + 1 + 2 = (q + 2) + 1 by omega, Nat.factorial_succ, pow_succ]
    calc
      2 * (3 ^ q * 3) = (2 * 3 ^ q) * 3 := by ring
      _ ≤ (q + 2).factorial * 3 := Nat.mul_le_mul_right 3 ih
      _ ≤ (q + 2).factorial * (q + 3) := Nat.mul_le_mul_left _ (by omega)
      _ = (q + 2 + 1) * (q + 2).factorial := by ring

lemma reciprocal_factorial_shift_le (q : ℕ) :
    1 / ((q + 2).factorial : ℝ) ≤ (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ q := by
  have hfact : (2 : ℝ) * 3 ^ q ≤ ((q + 2).factorial : ℝ) := by
    exact_mod_cast factorial_lower_shift q
  have hpos : 0 < (2 : ℝ) * 3 ^ q := by positivity
  calc
    1 / ((q + 2).factorial : ℝ) ≤ 1 / ((2 : ℝ) * 3 ^ q) :=
      one_div_le_one_div_of_le hpos hfact
    _ = (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ q := by rw [div_pow]; ring

lemma reciprocal_factorial_sum_strong (n : ℕ) :
    (∑ q ∈ Finset.range n, 1 / ((q + 2).factorial : ℝ)) ≤
      (3 / 4 : ℝ) * (1 - (1 / 3 : ℝ) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hnew := reciprocal_factorial_shift_le n
    nlinarith

lemma reciprocal_factorial_sum_le (n : ℕ) :
    (∑ q ∈ Finset.range n, 1 / ((q + 2).factorial : ℝ)) ≤ (3 / 4 : ℝ) := by
  have h := reciprocal_factorial_sum_strong n
  have hp : 0 ≤ (1 / 3 : ℝ) ^ n := by positivity
  nlinarith

lemma normalized_polynomial_exponent_bound (m : ℕ) (hm : 3 ≤ m) :
    (3 / 4 : ℝ) * ((m : ℝ) + 1) ≤ m := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

lemma normalized_factorial_sum_bound (m : ℕ) (hm : 2 ≤ m) :
    ((m : ℝ) + 1) * (∑ q ∈ Finset.range (m - 1), 1 / ((q + 2).factorial : ℝ)) ≤ m := by
  by_cases hm2 : m = 2
  · subst m
    norm_num
  · have hm3 : 3 ≤ m := by omega
    have hs := reciprocal_factorial_sum_le (m - 1)
    calc
      ((m : ℝ) + 1) * (∑ q ∈ Finset.range (m - 1), 1 / ((q + 2).factorial : ℝ)) ≤
          ((m : ℝ) + 1) * (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ m := by simpa only [mul_comm] using normalized_polynomial_exponent_bound m hm3

end DGRHS.Concentration

#print axioms DGRHS.Concentration.normalized_factorial_sum_bound
#print axioms DGRHS.Concentration.power_le_second_add_high
