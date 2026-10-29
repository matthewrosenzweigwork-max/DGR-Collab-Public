import FullLabeledLSI.Examples.E01h3_Series

/-!
# Lane D, Task B3 (part 2): convolution of a cosine/sine series with `σ`, and `σ(g * σ)`
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

variable (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (x : Torus 1)

theorem abs_lin_le {a b c d M : ℝ} (hc : |c| ≤ M) (hd : |d| ≤ M) :
    |a * c - b * d| ≤ (|a| + |b|) * M := by
  calc |a * c - b * d| ≤ |a * c| + |b * d| := abs_sub _ _
    _ = |a| * |c| + |b| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * M + |b| * M := add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = (|a| + |b|) * M := by ring

theorem abs_lin_le' {a b c d M : ℝ} (hc : |c| ≤ M) (hd : |d| ≤ M) :
    |a * d + b * c| ≤ (|a| + |b|) * M := by
  have := abs_lin_le (a := a) (b := -b) (c := d) (d := c) (M := M) hd hc
  simpa [sub_eq_add_neg, abs_neg, add_comm] using this

/-- `g * σ` for a cosine/sine series `g`. -/
theorem convS_hasSum {g : Torus 1 → ℝ} {a b : ℕ → ℝ} (ha : Summable fun m => |a m|)
    (hb : Summable fun m => |b m|)
    (hg : ∀ u, HasSum (fun m : ℕ => a m * cm (2 * (m : ℤ)) u + b m * sm (2 * (m : ℤ)) u) (g u))
    (z : Torus 1) :
    HasSum (fun m : ℕ =>
      (a m * cI α β x (2 * (m : ℤ)) - b m * sI α β x (2 * (m : ℤ))) * cm (2 * (m : ℤ)) (z - x) +
      (a m * sI α β x (2 * (m : ℤ)) + b m * cI α β x (2 * (m : ℤ))) * sm (2 * (m : ℤ)) (z - x))
      (convS g α β z) := by
  set f : ℕ → Torus 1 → ℝ := fun m y =>
    a m * cm (2 * (m : ℤ)) (z - y) + b m * sm (2 * (m : ℤ)) (z - y) with hf
  have hcont : ∀ m, Continuous (f m) := fun m =>
    (continuous_const.mul ((continuous_cm _).comp (continuous_const.sub continuous_id))).add
      (continuous_const.mul ((continuous_sm _).comp (continuous_const.sub continuous_id)))
  have hbd : ∀ m y, |f m y| ≤ |a m| + |b m| := by
    intro m y
    calc |f m y| ≤ |a m * cm (2 * (m : ℤ)) (z - y)| + |b m * sm (2 * (m : ℤ)) (z - y)| := abs_add_le _ _
      _ = |a m| * |cm (2 * (m : ℤ)) (z - y)| + |b m| * |sm (2 * (m : ℤ)) (z - y)| := by
          rw [abs_mul, abs_mul]
      _ ≤ |a m| * 1 + |b m| * 1 := add_le_add
          (mul_le_mul_of_nonneg_left (abs_cm_le _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (abs_sm_le _ _) (abs_nonneg _))
      _ = _ := by ring
  have h := intS_tsum α β hcont (ha.add hb) hbd
  have hfun : (fun y => ∑' m, f m y) = fun y => g (z - y) := funext fun y => (hg (z - y)).tsum_eq
  rw [hfun] at h
  have key : ∀ m, intS (f m) α β =
      (a m * cI α β x (2 * (m : ℤ)) - b m * sI α β x (2 * (m : ℤ))) * cm (2 * (m : ℤ)) (z - x) +
      (a m * sI α β x (2 * (m : ℤ)) + b m * cI α β x (2 * (m : ℤ))) * sm (2 * (m : ℤ)) (z - x) := by
    intro m
    have := (linC_intS α β).add (fun y => a m * cm (2 * (m : ℤ)) (z - y))
      (fun y => b m * sm (2 * (m : ℤ)) (z - y))
      (continuous_const.mul ((continuous_cm _).comp (continuous_const.sub continuous_id)))
      (continuous_const.mul ((continuous_sm _).comp (continuous_const.sub continuous_id)))
    simp only [hf]
    rw [this, (linC_intS α β).smul, (linC_intS α β).smul, intS_cm_conv α β x, intS_sm_conv α β x]
    ring
  convert h using 1
  · funext m
    exact (key m).symm
  · rfl

/-- `σ(g * σ) = ∑_m a_m (c_m² + d_m²)`. -/
theorem intS_convS_hasSum {g : Torus 1 → ℝ} {a b : ℕ → ℝ} (ha : Summable fun m => |a m|)
    (hb : Summable fun m => |b m|)
    (hg : ∀ u, HasSum (fun m : ℕ => a m * cm (2 * (m : ℤ)) u + b m * sm (2 * (m : ℤ)) u) (g u)) :
    HasSum (fun m : ℕ => a m * (cI α β x (2 * (m : ℤ)) ^ 2 + sI α β x (2 * (m : ℤ)) ^ 2))
      (intS (convS g α β) α β) := by
  set P : ℕ → ℝ := fun m => a m * cI α β x (2 * (m : ℤ)) - b m * sI α β x (2 * (m : ℤ)) with hP
  set Q : ℕ → ℝ := fun m => a m * sI α β x (2 * (m : ℤ)) + b m * cI α β x (2 * (m : ℤ)) with hQ
  set F : ℕ → Torus 1 → ℝ := fun m z =>
    P m * cm (2 * (m : ℤ)) (z - x) + Q m * sm (2 * (m : ℤ)) (z - x) with hF
  have hcont : ∀ m, Continuous (F m) := fun m =>
    (continuous_const.mul (cont_cm_sub x _)).add (continuous_const.mul (cont_sm_sub x _))
  have hPb : ∀ m, |P m| ≤ (|a m| + |b m|) * mass α β := fun m =>
    abs_lin_le (abs_cI_le α β x _) (abs_sI_le α β x _)
  have hQb : ∀ m, |Q m| ≤ (|a m| + |b m|) * mass α β := fun m =>
    abs_lin_le' (abs_cI_le α β x _) (abs_sI_le α β x _)
  have hbd : ∀ m z, |F m z| ≤ 2 * ((|a m| + |b m|) * mass α β) := by
    intro m z
    calc |F m z| ≤ |P m * cm (2 * (m : ℤ)) (z - x)| + |Q m * sm (2 * (m : ℤ)) (z - x)| := abs_add_le _ _
      _ = |P m| * |cm (2 * (m : ℤ)) (z - x)| + |Q m| * |sm (2 * (m : ℤ)) (z - x)| := by
          rw [abs_mul, abs_mul]
      _ ≤ |P m| * 1 + |Q m| * 1 := add_le_add
          (mul_le_mul_of_nonneg_left (abs_cm_le _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (abs_sm_le _ _) (abs_nonneg _))
      _ ≤ _ := by linarith [hPb m, hQb m]
  have hsum : Summable fun m : ℕ => 2 * ((|a m| + |b m|) * mass α β) :=
    ((ha.add hb).mul_right (mass α β)).mul_left 2
  have h := intS_tsum α β hcont hsum hbd
  have hfun : (fun z => ∑' m, F m z) = convS g α β :=
    funext fun z => (convS_hasSum α β x ha hb hg z).tsum_eq
  rw [hfun] at h
  have key : ∀ m, intS (F m) α β = a m * (cI α β x (2 * (m : ℤ)) ^ 2 + sI α β x (2 * (m : ℤ)) ^ 2) := by
    intro m
    have := (linC_intS α β).add (fun z => P m * cm (2 * (m : ℤ)) (z - x))
      (fun z => Q m * sm (2 * (m : ℤ)) (z - x)) (continuous_const.mul (cont_cm_sub x _))
      (continuous_const.mul (cont_sm_sub x _))
    simp only [hF]
    rw [this, (linC_intS α β).smul, (linC_intS α β).smul]
    show P m * cI α β x _ + Q m * sI α β x _ = _
    simp only [hP, hQ]
    ring
  convert h using 1
  funext m
  exact (key m).symm

end SharpLSI.FL.Ex.LaneD
