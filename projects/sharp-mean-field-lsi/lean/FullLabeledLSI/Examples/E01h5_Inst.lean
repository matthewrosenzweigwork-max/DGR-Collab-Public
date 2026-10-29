import FullLabeledLSI.Examples.E01h1_Poisson
import FullLabeledLSI.Examples.E01h3_Dbl
import FullLabeledLSI.Examples.E01h4_Schur

/-!
# Lane D, Task B5 (part 1): the Poisson kernel and its derivatives as cosine/sine series
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- Coefficients of `C = ∑_m pa m cos(4π m ·)`. -/
noncomputable def pa (m : ℕ) : ℝ := if m = 0 then 0 else 32 * (1 / 100 : ℝ) ^ m

/-- Coefficients of `C' = ∑_m pb m sin(4π m ·)`. -/
noncomputable def pb (m : ℕ) : ℝ := -(128 * π) * (m : ℝ) * (1 / 100 : ℝ) ^ m

/-- Coefficients of `C'' = ∑_m pa2 m cos(4π m ·)`. -/
noncomputable def pa2 (m : ℕ) : ℝ := -(32 : ℝ) * (1 / 100 : ℝ) ^ m * (4 * π * m) ^ 2

theorem geom_lt : ‖(1 / 100 : ℝ)‖ < 1 := by norm_num

theorem summable_pa : Summable fun m => |pa m| := by
  refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num)).mul_left 32)
  unfold pa
  split_ifs
  · simp
  · rw [abs_of_nonneg (by positivity)]

theorem summable_pb : Summable fun m => |pb m| := by
  have := (summable_pow_mul_geometric_of_norm_lt_one 1 geom_lt).mul_left (128 * π)
  refine this.congr (fun m => ?_)
  unfold pb
  rw [abs_of_nonpos]
  · simp; ring
  · have : 0 ≤ (128 * π) * (m : ℝ) * (1 / 100 : ℝ) ^ m := by positivity
    linarith

theorem summable_pa2 : Summable fun m => |pa2 m| := by
  have := (summable_pow_mul_geometric_of_norm_lt_one 2 geom_lt).mul_left (32 * (4 * π) ^ 2)
  refine this.congr (fun m => ?_)
  unfold pa2
  rw [abs_of_nonpos]
  · simp; ring
  · have : 0 ≤ 32 * (1 / 100 : ℝ) ^ m * (4 * π * m) ^ 2 := by positivity
    linarith

theorem hasSum_C (u : Torus 1) :
    HasSum (fun m : ℕ => pa m * cm (2 * (m : ℤ)) u + 0 * sm (2 * (m : ℤ)) u) (poissonKernel u) := by
  have h := poisson_series u
  refine hasSum_shift0 (by simp [pa]) ?_
  convert h using 1
  funext j
  simp only [pa, zero_mul, add_zero, Nat.succ_ne_zero, if_false]
  push_cast
  rfl

theorem hasSum_C' (u : Torus 1) :
    HasSum (fun m : ℕ => 0 * cm (2 * (m : ℤ)) u + pb m * sm (2 * (m : ℤ)) u) (dT poissonKernel u) := by
  simpa [pb] using dT_poisson_series u

theorem hasSum_C'_sm (u : Torus 1) :
    HasSum (fun m : ℕ => pb m * sm (2 * (m : ℤ)) u) (dT poissonKernel u) := by
  simpa [pb] using dT_poisson_series u

theorem hasSum_C'' (u : Torus 1) :
    HasSum (fun m : ℕ => pa2 m * cm (2 * (m : ℤ)) u + 0 * sm (2 * (m : ℤ)) u)
      (dT (dT poissonKernel) u) := by
  simpa [pa2] using dT2_poisson_series u

theorem pb_mul (p : ℕ × ℕ) : pb p.1 * pb p.2 = (128 * π) ^ 2 * wgt p := by
  unfold pb wgt
  rw [pow_add]; ring

end SharpLSI.FL.Ex.LaneD
