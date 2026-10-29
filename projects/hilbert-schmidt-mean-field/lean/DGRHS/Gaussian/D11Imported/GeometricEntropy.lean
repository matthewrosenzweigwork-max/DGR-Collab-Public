import DGRHS.Gaussian.D11Imported.CountableShannon
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The normalized two-sided geometric reference law used for the integer
shift, and its relative-entropy estimate in terms of the absolute first moment. -/
noncomputable section
namespace DGRHS.Gaussian.D11Imported.CountableShannon

def twoSidedGeometric (r : ℝ) (n : ℤ) : ℝ :=
  (1-r)/(1+r) * r^n.natAbs

lemma twoSidedGeometric_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℤ) :
    0 < twoSidedGeometric r n := by
  unfold twoSidedGeometric
  exact mul_pos (div_pos (sub_pos.mpr hr1) (by linarith)) (pow_pos hr _)

lemma twoSidedGeometric_hasSum {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasSum (twoSidedGeometric r) 1 := by
  have h := hasSum_geometric_of_lt_one hr.le hr1
  have hpos : HasSum (fun n : ℕ => r^(Int.natAbs (n:ℤ))) (1-r)⁻¹ := by simpa using h
  have hneg : HasSum (fun n : ℕ => r^(Int.natAbs (-(n+1:ℤ)))) (r*(1-r)⁻¹) := by
    simpa only [Int.natAbs_neg, ← Int.natCast_one, ← Int.natCast_add, Int.natAbs_natCast, pow_succ'] using h.mul_left r
  have hi : HasSum (fun n : ℤ => r^n.natAbs) ((1-r)⁻¹+r*(1-r)⁻¹) :=
    HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => r^n.natAbs) hpos hneg
  have ht := hi.mul_left ((1-r)/(1+r))
  convert ht using 1 <;> first | rfl | (field_simp [show 1-r ≠ 0 by linarith, show 1+r ≠ 0 by linarith] <;> ring)

lemma geometric_cross_entropy {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℤ) :
    -Real.log (twoSidedGeometric r n) =
      -Real.log r * (n.natAbs:ℝ) + Real.log ((1+r)/(1-r)) := by
  unfold twoSidedGeometric
  rw [Real.log_mul (by positivity) (pow_pos hr _).ne', Real.log_pow,
    Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
  ring

theorem entropy_le_geometric_moment (p : ℤ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hps : HasSum p 1)
    (hm : Summable (fun n : ℤ => p n*(n.natAbs:ℝ)))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n => p n*Real.log (p n)) ∧
    -(∑' n, p n*Real.log (p n)) ≤
      -Real.log r * (∑' n : ℤ, p n*(n.natAbs:ℝ)) + Real.log ((1+r)/(1-r)) := by
  have he (n : ℤ) : -(p n*Real.log (twoSidedGeometric r n)) =
      -Real.log r*(p n*(n.natAbs:ℝ)) + Real.log ((1+r)/(1-r))*p n := by
    have h := geometric_cross_entropy hr hr1 n
    calc
      _ = p n * (-Real.log (twoSidedGeometric r n)) := by ring
      _ = _ := by rw [h]; ring
  have hs : Summable (fun n => -(p n*Real.log (twoSidedGeometric r n))) := by
    simp_rw [he]
    exact (hm.mul_left _).add (hps.summable.mul_left _)
  have hh := entropy_comparison p (twoSidedGeometric r) hp
    (twoSidedGeometric_pos hr hr1) hps (twoSidedGeometric_hasSum hr hr1) (by simpa using hs.neg)
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  rw [← tsum_neg]
  simp_rw [he]
  rw [Summable.tsum_add (hm.mul_left _) (hps.summable.mul_left _), tsum_mul_left,
    tsum_mul_left, hps.tsum_eq, mul_one]

lemma geometric_log_normalizer {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.log ((1+r)/(1-r)) ≤ 2*r/(1-r^2) := by
  have h := Real.log_div_le_sum_range_add hr hr1 0
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_one] at h
  simp only [div_eq_mul_inv] at h ⊢
  linarith

theorem eleven_label_entropy_of_moment (p : ℤ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hps : HasSum p 1)
    (hm : Summable (fun n : ℤ => p n*(n.natAbs:ℝ)))
    (hm_bound : (∑' n : ℤ, p n*(n.natAbs:ℝ)) < 83927/8121093750) :
    Summable (fun n => p n*Real.log (p n)) ∧
      11 * (-(∑' n, p n*Real.log (p n))) < (1/600:ℝ) := by
  have hh := entropy_le_geometric_moment p hp hps hm
    (by norm_num : (0:ℝ)<1/2^18) (by norm_num : (1:ℝ)/2^18<1)
  have hl : -Real.log ((1:ℝ)/2^18) = 18*Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, Real.log_pow]
    norm_num
  rw [hl] at hh
  have hnorm := geometric_log_normalizer (by norm_num : (0:ℝ)≤1/2^18)
    (by norm_num : (1:ℝ)/2^18<1)
  norm_num only at hnorm
  have hlog : Real.log 2 < (7/10:ℝ) := by linarith [Real.log_two_lt_d9]
  have hmoment : 0 ≤ ∑' n : ℤ, p n*(n.natAbs:ℝ) := tsum_nonneg (fun n => mul_nonneg (hp n) (by positivity))
  refine ⟨hh.1, ?_⟩
  have hb : (18*Real.log 2)*(∑' n : ℤ, p n*(n.natAbs:ℝ)) < (63/5)*(83927/8121093750) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith : 18*Real.log 2 ≤ (63/5:ℝ)) hmoment)
      (mul_lt_mul_of_pos_left hm_bound (by norm_num))
  norm_num at hnorm
  linarith [hh.2]

#print axioms eleven_label_entropy_of_moment
end DGRHS.Gaussian.D11Imported.CountableShannon
