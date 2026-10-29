import FullLabeledLSI.Examples.E01h2_Calc

/-!
# Lane D, Task B: trigonometric identities for `cm`, `sm` on `Torus 1`

All identities are proved by passing to real representatives (`x = lift1 t`).
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem lift1_zero : lift1 0 = 0 := by
  funext i; fin_cases i
  show ((0 : ℝ) : UnitAddCircle) = 0
  simp

theorem lift1_add (a b : ℝ) : lift1 (a + b) = lift1 a + lift1 b := by
  funext i; fin_cases i
  show ((a + b : ℝ) : UnitAddCircle) = (a : UnitAddCircle) + (b : UnitAddCircle)
  simp

theorem lift1_neg (a : ℝ) : lift1 (-a) = -lift1 a := by
  funext i; fin_cases i
  show ((-a : ℝ) : UnitAddCircle) = -(a : UnitAddCircle)
  simp

theorem lift1_sub (a b : ℝ) : lift1 (a - b) = lift1 a - lift1 b := by
  funext i; fin_cases i
  show ((a - b : ℝ) : UnitAddCircle) = (a : UnitAddCircle) - (b : UnitAddCircle)
  simp

theorem exists_lift1 (x : Torus 1) : ∃ t : ℝ, x = lift1 t := ⟨rep x, (lift1_rep x).symm⟩

theorem cm_lift1 (n : ℤ) (t : ℝ) : cm n (lift1 t) = Real.cos (2 * π * n * t) := by
  unfold cm
  rw [lift1_apply, fourier_coe_apply]
  have : (2 * (π : ℂ) * Complex.I * n * t / ((1 : ℝ) : ℂ)) = ((2 * π * n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem sm_lift1 (n : ℤ) (t : ℝ) : sm n (lift1 t) = Real.sin (2 * π * n * t) := by
  unfold sm
  rw [lift1_apply, fourier_coe_apply]
  have : (2 * (π : ℂ) * Complex.I * n * t / ((1 : ℝ) : ℂ)) = ((2 * π * n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im]

theorem cm_sub (n : ℤ) (x y : Torus 1) :
    cm n (x - y) = cm n x * cm n y + sm n x * sm n y := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  obtain ⟨b, rfl⟩ := exists_lift1 y
  rw [← lift1_sub, cm_lift1, cm_lift1, cm_lift1, sm_lift1, sm_lift1,
    show 2 * π * n * (a - b) = 2 * π * n * a - 2 * π * n * b by ring, Real.cos_sub]

theorem sm_sub (n : ℤ) (x y : Torus 1) :
    sm n (x - y) = sm n x * cm n y - cm n x * sm n y := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  obtain ⟨b, rfl⟩ := exists_lift1 y
  rw [← lift1_sub, sm_lift1, cm_lift1, sm_lift1, cm_lift1, sm_lift1,
    show 2 * π * n * (a - b) = 2 * π * n * a - 2 * π * n * b by ring, Real.sin_sub]

theorem cm_neg_arg (n : ℤ) (x : Torus 1) : cm n (-x) = cm n x := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  rw [← lift1_neg, cm_lift1, cm_lift1, show 2 * π * n * (-a) = -(2 * π * n * a) by ring, Real.cos_neg]

theorem sm_neg_arg (n : ℤ) (x : Torus 1) : sm n (-x) = - sm n x := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  rw [← lift1_neg, sm_lift1, sm_lift1, show 2 * π * n * (-a) = -(2 * π * n * a) by ring, Real.sin_neg]

theorem cm_neg_idx (n : ℤ) (x : Torus 1) : cm (-n) x = cm n x := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  rw [cm_lift1, cm_lift1]
  push_cast
  rw [show 2 * π * (-(n : ℝ)) * a = -(2 * π * n * a) by ring, Real.cos_neg]

theorem sm_neg_idx (n : ℤ) (x : Torus 1) : sm (-n) x = - sm n x := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  rw [sm_lift1, sm_lift1]
  push_cast
  rw [show 2 * π * (-(n : ℝ)) * a = -(2 * π * n * a) by ring, Real.sin_neg]

theorem cm_zero_idx (x : Torus 1) : cm 0 x = 1 := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  rw [cm_lift1]; simp

theorem sm_zero_idx (x : Torus 1) : sm 0 x = 0 := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  rw [sm_lift1]; simp

theorem cm_zero_pt (n : ℤ) : cm n 0 = 1 := by
  rw [← lift1_zero, cm_lift1]; simp

theorem sm_zero_pt (n : ℤ) : sm n 0 = 0 := by
  rw [← lift1_zero, sm_lift1]; simp

theorem cm_mul_cm (a b : ℤ) (x : Torus 1) :
    cm a x * cm b x = (cm (a + b) x + cm (a - b) x) / 2 := by
  obtain ⟨t, rfl⟩ := exists_lift1 x
  simp only [cm_lift1]
  push_cast
  rw [show 2 * π * ((a : ℝ) + b) * t = 2 * π * a * t + 2 * π * b * t by ring,
    show 2 * π * ((a : ℝ) - b) * t = 2 * π * a * t - 2 * π * b * t by ring, Real.cos_add, Real.cos_sub]
  ring

theorem sm_mul_sm (a b : ℤ) (x : Torus 1) :
    sm a x * sm b x = (cm (a - b) x - cm (a + b) x) / 2 := by
  obtain ⟨t, rfl⟩ := exists_lift1 x
  simp only [cm_lift1, sm_lift1]
  push_cast
  rw [show 2 * π * ((a : ℝ) + b) * t = 2 * π * a * t + 2 * π * b * t by ring,
    show 2 * π * ((a : ℝ) - b) * t = 2 * π * a * t - 2 * π * b * t by ring, Real.cos_add, Real.cos_sub]
  ring

theorem sm_mul_cm (a b : ℤ) (x : Torus 1) :
    sm a x * cm b x = (sm (a + b) x + sm (a - b) x) / 2 := by
  obtain ⟨t, rfl⟩ := exists_lift1 x
  simp only [cm_lift1, sm_lift1]
  push_cast
  rw [show 2 * π * ((a : ℝ) + b) * t = 2 * π * a * t + 2 * π * b * t by ring,
    show 2 * π * ((a : ℝ) - b) * t = 2 * π * a * t - 2 * π * b * t by ring, Real.sin_add, Real.sin_sub]
  ring

theorem abs_cm_le (n : ℤ) (x : Torus 1) : |cm n x| ≤ 1 := by
  obtain ⟨t, rfl⟩ := exists_lift1 x
  rw [cm_lift1]; exact Real.abs_cos_le_one _

theorem abs_sm_le (n : ℤ) (x : Torus 1) : |sm n x| ≤ 1 := by
  obtain ⟨t, rfl⟩ := exists_lift1 x
  rw [sm_lift1]; exact Real.abs_sin_le_one _

theorem continuous_cm (n : ℤ) : Continuous (cm n) :=
  Complex.continuous_re.comp ((fourier n).continuous.comp (continuous_apply 0))

theorem continuous_sm (n : ℤ) : Continuous (sm n) :=
  Complex.continuous_im.comp ((fourier n).continuous.comp (continuous_apply 0))

theorem dT_cm (n : ℤ) (x : Torus 1) : dT (cm n) x = -(2 * π * n) * sm n x := by
  rw [dT_apply]
  have h : (fun s : ℝ => cm n (lift1 s)) = fun s => Real.cos (2 * π * n * s) := funext fun s => cm_lift1 n s
  rw [h]
  have h2 : HasDerivAt (fun s : ℝ => Real.cos (2 * π * n * s)) (-Real.sin (2 * π * n * rep x) * (2 * π * n)) (rep x) := by
    have := ((hasDerivAt_id (rep x)).const_mul (2 * π * n)).cos
    simpa using this
  rw [h2.deriv]
  conv_rhs => rw [← lift1_rep x, sm_lift1]
  ring

theorem dT_sm (n : ℤ) (x : Torus 1) : dT (sm n) x = (2 * π * n) * cm n x := by
  rw [dT_apply]
  have h : (fun s : ℝ => sm n (lift1 s)) = fun s => Real.sin (2 * π * n * s) := funext fun s => sm_lift1 n s
  rw [h]
  have h2 : HasDerivAt (fun s : ℝ => Real.sin (2 * π * n * s)) (Real.cos (2 * π * n * rep x) * (2 * π * n)) (rep x) := by
    have := ((hasDerivAt_id (rep x)).const_mul (2 * π * n)).sin
    simpa using this
  rw [h2.deriv]
  conv_rhs => rw [← lift1_rep x, cm_lift1]
  ring

end SharpLSI.FL.Ex.LaneD
