import FullLabeledLSI.Examples.E01h6_Unique
import FullLabeledLSI.Examples.E01h1_Poisson

/-!
# Lane D, Task D (E01h6): numerical facts about the Poisson kernel
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem abs_poisson_le (x : Torus 1) : |poissonKernel x| ≤ 32 / 99 := by
  have h := poisson_series x
  have hg : HasSum (fun j : ℕ => 32 * (1 / 100 : ℝ) ^ (j + 1)) (32 / 99) := by
    have := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num)).mul_left (32 * (1 / 100 : ℝ))
    convert this using 1
    · funext j; ring
    · norm_num
  have := h.norm_le_of_bounded hg (fun j => by
    rw [Real.norm_eq_abs, abs_mul]
    calc |32 * (1 / 100 : ℝ) ^ (j + 1)| * |cm (2 * ((j : ℤ) + 1)) x| ≤
          |32 * (1 / 100 : ℝ) ^ (j + 1)| * 1 := mul_le_mul_of_nonneg_left (abs_cm_le _ _) (abs_nonneg _)
      _ = 32 * (1 / 100 : ℝ) ^ (j + 1) := by rw [mul_one, abs_of_nonneg (by positivity)])
  simpa [Real.norm_eq_abs] using this

theorem chat_poisson_nonneg_le (n : ℤ) (hn : n ≠ 0) :
    0 ≤ chat poissonKernel n ∧ chat poissonKernel n ≤ 4 / 25 := by
  rcases Int.even_or_odd n with ⟨j, hj⟩ | hodd
  · have hj' : n = 2 * j := by omega
    have hj0 : j ≠ 0 := by rintro rfl; simp at hj'; exact hn hj'
    rw [hj', chat_poisson_even j hj0]
    have h1 : (0 : ℝ) < (1 / 100) ^ j.natAbs := by positivity
    have h2 : (1 / 100 : ℝ) ^ j.natAbs ≤ 1 / 100 := by
      have : 1 ≤ j.natAbs := Int.natAbs_pos.2 hj0
      calc (1 / 100 : ℝ) ^ j.natAbs ≤ (1 / 100) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) this
        _ = 1 / 100 := by norm_num
    constructor <;> nlinarith
  · rw [chat_poisson_odd n hodd]; norm_num

end SharpLSI.FL.Ex.LaneD
