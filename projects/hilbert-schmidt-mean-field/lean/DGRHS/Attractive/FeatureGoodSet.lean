/- Source2700–2744 good-set arithmetic. Native logarithmic Taylor remainder
is reused; no Gaussian law, Taylor coefficients or moment estimates assumed
as a paper theorem. This file supplies deterministic downstream inequalities. -/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import DGRHS.CLT.PartitionComparison
import Mathlib.Tactic
noncomputable section
namespace DGRHS.Attractive

lemma abs_log_one_add_sub_le (y : ℝ) (hy : |y| ≤ 1/2) :
    |Real.log (1+y)-y| ≤ 2*y^2 := by
  have hy1 : |-y|<1 := by simpa only [abs_neg] using (hy.trans_lt (by norm_num : (1/2:ℝ)<1))
  have h := Real.abs_log_sub_add_sum_range_le hy1 1
  have h' : |Real.log (1+y)-y| ≤ y^2/(1-|y|) := by
    simpa [Finset.sum_range_one,sub_eq_add_neg,add_comm,sq_abs] using h
  have hd : 0<1-|y| := by linarith
  exact h'.trans ((div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg y]))

lemma source_good_set_delta (A B R E n : ℝ) (hn : 0<n)
    (htaylor : A=1+B/n+R/(n*Real.sqrt n)+E/n^2)
    (hgood : |A-1|≤1/2) :
    |n*Real.log A-B| ≤ |R|/Real.sqrt n+|E|/n+2*n*(A-1)^2 := by
  have hs : 0<Real.sqrt n := Real.sqrt_pos.mpr hn
  have hl : |Real.log A-(A-1)|≤2*(A-1)^2 := by
    simpa only [add_sub_cancel] using abs_log_one_add_sub_le (A-1) hgood
  have he : n*Real.log A-B =
      (R/Real.sqrt n+E/n)+n*(Real.log A-(A-1)) := by
    rw [htaylor]
    field_simp [hn.ne',hs.ne']
    <;> ring
  rw [he]
  calc
    _ ≤ |R/Real.sqrt n+E/n|+|n*(Real.log A-(A-1))| := abs_add_le _ _
    _ ≤ |R/Real.sqrt n|+|E/n|+|n*(Real.log A-(A-1))| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ |R|/Real.sqrt n+|E|/n+2*n*(A-1)^2 := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hs,abs_of_pos hn]
      nlinarith [mul_le_mul_of_nonneg_left hl hn.le]

lemma source_good_set_power_difference (A B : ℝ) (N : ℕ) (hA : 0<A) :
    |A^N-Real.exp B| ≤ |(N:ℝ)*Real.log A-B| * (A^N+Real.exp B) := by
  have he : Real.exp ((N:ℝ)*Real.log A)=A^N := by
    rw [Real.exp_nat_mul,Real.exp_log hA]
  simpa only [he] using DGRHS.CLT.abs_exp_sub_exp_le ((N:ℝ)*Real.log A) B

end DGRHS.Attractive
#print axioms DGRHS.Attractive.abs_log_one_add_sub_le
#print axioms DGRHS.Attractive.source_good_set_delta
#print axioms DGRHS.Attractive.source_good_set_power_difference
