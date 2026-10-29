import FullLabeledLSI.Examples.E01h6_Core
import FullLabeledLSI.Examples.E01h5_Concavity

/-!
# Lane D, Task D (E01h7): the trial density `1 + t cos(2πx) + (t²/4) cos(4πx)` (skeleton)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-! ### Moments of `cos(2πx)` against Haar measure -/

theorem cm1_eq_cos_secT (y : Torus 1) : cm 1 y = Real.cos (2 * π * secT y 0) := by
  have h : y = lift1 (secT y 0) := by
    have := liftT_secT y
    rw [liftT_eq_lift1] at this
    exact this.symm
  conv_lhs => rw [h]
  rw [cm_lift1]; push_cast; ring_nf

theorem int_cm1_pow_eq (k : ℕ) :
    ∫ y, (cm 1 y) ^ k ∂haar 1 = (2 * π)⁻¹ * ∫ s in (0:ℝ)..(2 * π), Real.cos s ^ k := by
  have h1 : ∫ y : Torus 1, (cm 1 y) ^ k = ∫ y : Torus 1, (fun s : ℝ => Real.cos (2 * π * s) ^ k) (secT y 0) := by
    congr 1; funext y; rw [cm1_eq_cos_secT]
  have h2 := integral_torus1_secT (fun s : ℝ => Real.cos (2 * π * s) ^ k)
  show ∫ y : Torus 1, (cm 1 y) ^ k = _
  rw [h1, h2, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_comp_mul_left (fun s : ℝ => Real.cos s ^ k) (by positivity : (2 * π) ≠ 0)]
  simp


theorem int_cm1_pow_succ_succ (k : ℕ) :
    ∫ y, (cm 1 y) ^ (k + 2) ∂haar 1 = ((k : ℝ) + 1) / ((k : ℝ) + 2) * ∫ y, (cm 1 y) ^ k ∂haar 1 := by
  rw [int_cm1_pow_eq, int_cm1_pow_eq, integral_cos_pow]
  simp [Real.sin_two_pi]
  ring

theorem int_cm1_pow_zero : ∫ y, (cm 1 y) ^ 0 ∂haar 1 = 1 := by simp

theorem int_cm1_pow_one : ∫ y, (cm 1 y) ^ 1 ∂haar 1 = 0 := by
  rw [int_cm1_pow_eq]; simp [Real.sin_two_pi]

theorem int_cm1_pow_two : ∫ y, (cm 1 y) ^ 2 ∂haar 1 = 1 / 2 := by
  rw [int_cm1_pow_succ_succ 0, int_cm1_pow_zero]; norm_num
theorem int_cm1_pow_three : ∫ y, (cm 1 y) ^ 3 ∂haar 1 = 0 := by
  rw [int_cm1_pow_succ_succ 1, int_cm1_pow_one]; norm_num
theorem int_cm1_pow_four : ∫ y, (cm 1 y) ^ 4 ∂haar 1 = 3 / 8 := by
  rw [int_cm1_pow_succ_succ 2, int_cm1_pow_two]; norm_num
theorem int_cm1_pow_five : ∫ y, (cm 1 y) ^ 5 ∂haar 1 = 0 := by
  rw [int_cm1_pow_succ_succ 3, int_cm1_pow_three]; norm_num
theorem int_cm1_pow_six : ∫ y, (cm 1 y) ^ 6 ∂haar 1 = 5 / 16 := by
  rw [int_cm1_pow_succ_succ 4, int_cm1_pow_four]; norm_num
theorem int_cm1_pow_seven : ∫ y, (cm 1 y) ^ 7 ∂haar 1 = 0 := by
  rw [int_cm1_pow_succ_succ 5, int_cm1_pow_five]; norm_num
theorem int_cm1_pow_eight : ∫ y, (cm 1 y) ^ 8 ∂haar 1 = 35 / 128 := by
  rw [int_cm1_pow_succ_succ 6, int_cm1_pow_six]; norm_num

theorem trial_integ_cont {f : Torus 1 → ℝ} (hf : Continuous f) : Integrable f (haar 1) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem int_cm1 : ∫ y, cm 1 y ∂haar 1 = 0 := by simpa using int_cm1_pow_one

theorem int_poly8 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℝ) :
    ∫ y, (a0 + a1 * cm 1 y + a2 * cm 1 y ^ 2 + a3 * cm 1 y ^ 3 + a4 * cm 1 y ^ 4 + a5 * cm 1 y ^ 5 +
      a6 * cm 1 y ^ 6 + a7 * cm 1 y ^ 7 + a8 * cm 1 y ^ 8) ∂haar 1 =
    a0 + a2 / 2 + 3 * a4 / 8 + 5 * a6 / 16 + 35 * a8 / 128 := by
  have hcm := continuous_cm 1
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_add]
  · simp only [integral_const_mul, int_cm1_pow_two, int_cm1_pow_three, int_cm1_pow_four,
      int_cm1_pow_five, int_cm1_pow_six, int_cm1_pow_seven, int_cm1_pow_eight, int_cm1]
    simp
    ring
  all_goals
    apply trial_integ_cont
    fun_prop

theorem int_poly8' {f : Torus 1 → ℝ} (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℝ)
    (hf : ∀ y, f y = a0 + a1 * cm 1 y + a2 * cm 1 y ^ 2 + a3 * cm 1 y ^ 3 + a4 * cm 1 y ^ 4 +
      a5 * cm 1 y ^ 5 + a6 * cm 1 y ^ 6 + a7 * cm 1 y ^ 7 + a8 * cm 1 y ^ 8) :
    ∫ y, f y ∂haar 1 = a0 + a2 / 2 + 3 * a4 / 8 + 5 * a6 / 16 + 35 * a8 / 128 := by
  have : f = fun y => a0 + a1 * cm 1 y + a2 * cm 1 y ^ 2 + a3 * cm 1 y ^ 3 + a4 * cm 1 y ^ 4 +
      a5 * cm 1 y ^ 5 + a6 * cm 1 y ^ 6 + a7 * cm 1 y ^ 7 + a8 * cm 1 y ^ 8 := funext hf
  rw [this]; exact int_poly8 ..

theorem cm2_eq (x : Torus 1) : cm 2 x = 2 * cm 1 x ^ 2 - 1 := by
  have h := cm_mul_cm 1 1 x
  norm_num [cm_zero_idx] at h
  nlinarith

theorem sm2_eq (x : Torus 1) : sm 2 x = 2 * sm 1 x * cm 1 x := by
  have h := sm_mul_cm 1 1 x
  norm_num [sm_zero_idx] at h
  nlinarith

theorem cm_sq_add_sm_sq (n : ℤ) (x : Torus 1) : cm n x ^ 2 + sm n x ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := exists_lift1 x
  rw [cm_lift1, sm_lift1]; exact Real.cos_sq_add_sin_sq _

theorem isSmoothT_cm (n : ℤ) : IsSmoothT (cm n) := by
  rw [isSmoothT_iff_lift1]
  have : (fun s : ℝ => cm n (lift1 s)) = fun s => Real.cos (2 * π * n * s) := funext fun s => cm_lift1 n s
  rw [this]; fun_prop

theorem isSmoothT_sm (n : ℤ) : IsSmoothT (sm n) := by
  rw [isSmoothT_iff_lift1]
  have : (fun s : ℝ => sm n (lift1 s)) = fun s => Real.sin (2 * π * n * s) := funext fun s => sm_lift1 n s
  rw [this]; fun_prop

/-- The trial density. -/
noncomputable def trho (t : ℝ) (x : Torus 1) : ℝ := 1 + t * cm 1 x + t ^ 2 / 4 * cm 2 x

theorem trho_eq (t : ℝ) (x : Torus 1) :
    trho t x = 1 + (t * cm 1 x + t ^ 2 / 2 * cm 1 x ^ 2 - t ^ 2 / 4) := by
  unfold trho; rw [cm2_eq]; ring

theorem abs_v_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) :
    |trho t x - 1| ≤ 2 * t := by
  unfold trho
  have h1 := abs_cm_le 1 x
  have h2 := abs_cm_le 2 x
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [mul_nonneg ht0 ht0]

theorem trho_pos {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) : 1 / 2 ≤ trho t x := by
  have := abs_v_le ht0 ht x
  rw [abs_le] at this; linarith

theorem trho_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) : trho t x ≤ 2 := by
  have := abs_v_le ht0 ht x
  rw [abs_le] at this; linarith

theorem continuous_trho (t : ℝ) : Continuous (trho t) := by
  unfold trho
  have := continuous_cm 1; have := continuous_cm 2; fun_prop

theorem isSmoothT_trho (t : ℝ) : IsSmoothT (trho t) := by
  have h1 := isSmoothT_cm 1; have h2 := isSmoothT_cm 2
  rw [isSmoothT_iff_lift1] at *
  unfold trho
  exact (contDiff_const.add (contDiff_const.mul h1)).add (contDiff_const.mul h2)

theorem trho_int (t : ℝ) : ∫ x, trho t x ∂haar 1 = 1 := by
  rw [int_poly8' (f := trho t) (1 - t ^ 2 / 4) t (t ^ 2 / 2) 0 0 0 0 0 0 (fun y => by
    rw [trho_eq]; ring)]
  ring

theorem convT_cm {C : Torus 1 → ℝ} (hC : GoodKernel C) (n : ℤ) (x : Torus 1) :
    convT C (cm n) x = chat C n * cm n x := by
  have h := conv_two_re C hC.even (continuous_of_smooth hC.smooth) 1 (K1 n) x
  simp only [mFourier_K1, one_mul] at h
  unfold convT
  rw [chat_eq]
  have e : ∀ y : Torus 1, C (x - y) * cm n y = (1 / 2) * (C (x - y) * (2 * (fourier n (y 0)).re)) := by
    intro y; unfold cm; ring
  simp_rw [e]
  rw [integral_const_mul]
  have h' : ∫ y : Torus 1, C (x - y) * (2 * (fourier n (y 0)).re) = (cf C (K1 n)).re * (2 * (fourier n (x 0)).re) := h
  rw [h']
  unfold cm; ring

theorem convT_add3 {C f g h : Torus 1 → ℝ} (hC : Continuous C) (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (a b c : ℝ) (x : Torus 1) :
    convT C (fun y => a * f y + b * g y + c * h y) x =
      a * convT C f x + b * convT C g x + c * convT C h x := by
  unfold convT
  have hi : ∀ u : Torus 1 → ℝ, Continuous u → Integrable (fun y => C (x - y) * u y) (haar 1) := fun u hu =>
    trial_integ_cont ((hC.comp (continuous_const.sub continuous_id)).mul hu)
  have e : ∀ y, C (x - y) * (a * f y + b * g y + c * h y) =
      a * (C (x - y) * f y) + b * (C (x - y) * g y) + c * (C (x - y) * h y) := fun y => by ring
  simp_rw [e]
  have i1 := (hi f hf).const_mul a
  have i2 := (hi g hg).const_mul b
  have i3 := (hi h hh).const_mul c
  have i12 : Integrable (fun y => a * (C (x - y) * f y) + b * (C (x - y) * g y)) (haar 1) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul]

theorem trho_eq3 (t : ℝ) : trho t = fun y => 1 * cm 0 y + t * cm 1 y + t ^ 2 / 4 * cm 2 y := by
  funext y; unfold trho; rw [cm_zero_idx]; ring

theorem chat_two : chat poissonKernel 2 = 4 / 25 := by
  have := chat_poisson_even 1 one_ne_zero
  norm_num at this
  rw [this]

theorem convT_trho (t : ℝ) (x : Torus 1) : convT poissonKernel (trho t) x = t ^ 2 / 25 * cm 2 x := by
  have hC := poisson_good
  rw [trho_eq3, convT_add3 (continuous_of_smooth hC.smooth) (continuous_cm 0) (continuous_cm 1)
    (continuous_cm 2), convT_cm hC, convT_cm hC, convT_cm hC, chat_poisson_zero,
    chat_poisson_odd 1 (by decide)]
  rw [chat_two]
  ring

theorem dT_convT_s {g ρ : Torus 1 → ℝ} (hg : IsSmoothT g) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) : dT (convT g ρ) = convT (dT g) ρ := by
  have := isProbabilityMeasure_densMeasure' h0 h1
  funext x
  have e1 : convT (dT g) ρ = fun x => ∫ y, dT g (x - y) ∂densMeasure ρ := convT_eq_conv h0 h1
  have e2 : convT g ρ = fun x => ∫ y, g (x - y) ∂densMeasure ρ := convT_eq_conv h0 h1
  rw [e2, dT_conv hg, e1]

theorem dT_const_mul_cm (a : ℝ) (n : ℤ) (x : Torus 1) :
    dT (fun y => a * cm n y) x = a * (-(2 * π * n) * sm n x) := by
  rw [dT_apply]
  have h : (fun s : ℝ => a * cm n (lift1 s)) = fun s => a * Real.cos (2 * π * n * s) :=
    funext fun s => by rw [cm_lift1]
  simp only [h]
  have h2 : HasDerivAt (fun s : ℝ => a * Real.cos (2 * π * n * s))
      (a * (-Real.sin (2 * π * n * rep x) * (2 * π * n))) (rep x) := by
    have := (((hasDerivAt_id (rep x)).const_mul (2 * π * n)).cos).const_mul a
    simpa using this
  rw [h2.deriv]
  conv_rhs => rw [← lift1_rep x, sm_lift1]
  ring

theorem dT_const_mul_sm (a : ℝ) (n : ℤ) (x : Torus 1) :
    dT (fun y => a * sm n y) x = a * ((2 * π * n) * cm n x) := by
  rw [dT_apply]
  have h : (fun s : ℝ => a * sm n (lift1 s)) = fun s => a * Real.sin (2 * π * n * s) :=
    funext fun s => by rw [sm_lift1]
  simp only [h]
  have h2 : HasDerivAt (fun s : ℝ => a * Real.sin (2 * π * n * s))
      (a * (Real.cos (2 * π * n * rep x) * (2 * π * n))) (rep x) := by
    have := (((hasDerivAt_id (rep x)).const_mul (2 * π * n)).sin).const_mul a
    simpa using this
  rw [h2.deriv]
  conv_rhs => rw [← lift1_rep x, cm_lift1]
  ring

theorem trho_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) : 0 ≤ trho t x :=
  (by norm_num : (0:ℝ) ≤ 1 / 2).trans (trho_pos ht0 ht x)

theorem convT_dT_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) :
    convT (dT poissonKernel) (trho t) x = -(4 * π * t ^ 2 / 25) * sm 2 x := by
  rw [← dT_convT_s poisson_good.smooth (trho_nonneg ht0 ht) (trho_int t)]
  have : convT poissonKernel (trho t) = fun y => t ^ 2 / 25 * cm 2 y := funext (convT_trho t)
  rw [this, dT_const_mul_cm]
  push_cast; ring

theorem convT_dT2_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) :
    convT (dT (dT poissonKernel)) (trho t) x = -(16 * π ^ 2 * t ^ 2 / 25) * cm 2 x := by
  rw [← dT_convT_s (isSmoothT_dT poisson_good.smooth) (trho_nonneg ht0 ht) (trho_int t)]
  have : convT (dT poissonKernel) (trho t) = fun y => -(4 * π * t ^ 2 / 25) * sm 2 y :=
    funext (convT_dT_trho ht0 ht)
  rw [this, dT_const_mul_sm]
  push_cast; ring

theorem cqR_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    cqR poissonKernel (trho t) = t ^ 4 / 200 := by
  unfold cqR
  simp_rw [convT_trho]
  rw [int_poly8' (f := fun x => trho t x * (t ^ 2 / 25 * cm 2 x))
    (t^2/25*(-1 + t^2/4)) (t^2/25*(-t)) (t^2/25*(2 - t^2)) (t^2/25*(2*t)) (t^2/25*(t^2)) 0 0 0 0
    (fun y => by rw [trho_eq, cm2_eq]; ring)]
  ring

theorem int_C2_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    ∫ x, trho t x * convT (dT (dT poissonKernel)) (trho t) x ∂haar 1 = -(2 * π ^ 2 * t ^ 4 / 25) := by
  simp_rw [convT_dT2_trho ht0 ht]
  rw [int_poly8' (f := fun x => trho t x * (-(16 * π ^ 2 * t ^ 2 / 25) * cm 2 x))
    (-(16 * π ^ 2 * t ^ 2 / 25) * (-1 + t^2/4)) (-(16 * π ^ 2 * t ^ 2 / 25) * (-t))
    (-(16 * π ^ 2 * t ^ 2 / 25) * (2 - t^2)) (-(16 * π ^ 2 * t ^ 2 / 25) * (2 * t))
    (-(16 * π ^ 2 * t ^ 2 / 25) * (t^2)) 0 0 0 0
    (fun y => by rw [trho_eq, cm2_eq]; ring)]
  ring

theorem int_C1sq_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    ∫ x, trho t x * (convT (dT poissonKernel) (trho t) x) ^ 2 ∂haar 1 = 8 * π ^ 2 * t ^ 4 / 625 := by
  simp_rw [convT_dT_trho ht0 ht]
  rw [int_poly8' (f := fun x => trho t x * (-(4 * π * t ^ 2 / 25) * sm 2 x) ^ 2)
    (0) (0) ((4 * π * t ^ 2 / 25) ^ 2 * (4 - t^2)) ((4 * π * t ^ 2 / 25) ^ 2 * (4 * t))
    ((4 * π * t ^ 2 / 25) ^ 2 * (-4 + 3 * t^2)) ((4 * π * t ^ 2 / 25) ^ 2 * (-4 * t))
    ((4 * π * t ^ 2 / 25) ^ 2 * (-2 * t^2)) 0 0
    (fun y => by
      have h := cm_sq_add_sm_sq 2 y
      have : sm 2 y ^ 2 = 1 - (2 * cm 1 y ^ 2 - 1) ^ 2 := by rw [← cm2_eq]; linarith
      rw [mul_pow, neg_sq, this, trho_eq]; ring)]
  ring

theorem klFun_one_add_bound {v : ℝ} (hv : |v| ≤ 1 / 2) :
    |klFun (1 + v) - (v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 12)| ≤ 4 * |v| ^ 5 := by
  have hv1 : |-v| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hv1 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h
  have hlog : 1 - -v = 1 + v := by ring
  rw [hlog] at h
  set E := Real.log (1 + v) - (v - v ^ 2 / 2 + v ^ 3 / 3 - v ^ 4 / 4) with hE
  have hE' : |E| ≤ 2 * |v| ^ 5 := by
    have h2 : |E| ≤ |v| ^ 5 / (1 - |v|) := by
      convert h using 2
      simp only [hE]; norm_num; ring_nf
    have h3 : |v| ^ 5 / (1 - |v|) ≤ 2 * |v| ^ 5 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_nonneg (abs_nonneg v) 5]
    linarith
  have hk : klFun (1 + v) = (v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 12) - v ^ 5 / 4 + (1 + v) * E := by
    rw [klFun_apply, hE]; ring
  have hv5 : |v ^ 5| = |v| ^ 5 := abs_pow v 5
  rw [hk]
  have : (v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 12 - v ^ 5 / 4 + (1 + v) * E) - (v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 12)
      = -(v ^ 5 / 4) + (1 + v) * E := by ring
  rw [this]
  have hb : |(1 + v) * E| ≤ 3 * |v| ^ 5 := by
    rw [abs_mul]
    have : |1 + v| ≤ 3 / 2 := by rw [abs_le] at hv ⊢; constructor <;> linarith
    calc |1 + v| * |E| ≤ (3 / 2) * (2 * |v| ^ 5) :=
          mul_le_mul this hE' (abs_nonneg _) (by norm_num)
      _ = 3 * |v| ^ 5 := by ring
  calc |-(v ^ 5 / 4) + (1 + v) * E| ≤ |-(v ^ 5 / 4)| + |(1 + v) * E| := abs_add_le _ _
    _ ≤ |v| ^ 5 / 4 + 3 * |v| ^ 5 := by
        exact add_le_add (by rw [abs_neg, abs_div, hv5]; norm_num) hb
    _ ≤ 4 * |v| ^ 5 := by nlinarith [pow_nonneg (abs_nonneg v) 5]

theorem inv_one_add_bound {v : ℝ} (hv : |v| ≤ 1 / 2) :
    1 / (1 + v) ≤ 1 - v + v ^ 2 + 2 * |v| ^ 3 := by
  have hpos : 0 < 1 + v := by rw [abs_le] at hv; linarith
  have e : 1 / (1 + v) = (1 - v + v ^ 2) - v ^ 3 / (1 + v) := by
    field_simp; ring
  rw [e]
  have : -(v ^ 3 / (1 + v)) ≤ 2 * |v| ^ 3 := by
    have h1 : -(v ^ 3) ≤ |v| ^ 3 := by
      have := neg_abs_le (v ^ 3); rw [abs_pow] at this; linarith
    have h2 : 1 / (1 + v) ≤ 2 := by
      rw [div_le_iff₀ hpos]; rw [abs_le] at hv; linarith
    calc -(v ^ 3 / (1 + v)) = (-(v ^ 3)) * (1 / (1 + v)) := by ring
      _ ≤ |v| ^ 3 * 2 := by
          by_cases hn : 0 ≤ -(v ^ 3)
          · exact mul_le_mul h1 h2 (by positivity) (by positivity)
          · push Not at hn
            have : (-(v ^ 3)) * (1 / (1 + v)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn.le (by positivity)
            have : 0 ≤ |v| ^ 3 * 2 := by positivity
            linarith
      _ = 2 * |v| ^ 3 := by ring
  linarith

theorem entR_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    entR (trho t) = ∫ x, klFun (trho t x) ∂haar 1 := by
  have := (klDiv_densMeasure_bdd (continuous_trho t).measurable (trho_nonneg ht0 ht) (trho_int t)
    (B := 2) (trho_le ht0 ht)).2
  exact this

theorem qpoly_eq (t : ℝ) (x : Torus 1) :
    (trho t x - 1) ^ 2 / 2 - (trho t x - 1) ^ 3 / 6 + (trho t x - 1) ^ 4 / 12 =
      (t ^ 4 / 32 + t ^ 6 / 384 + t ^ 8 / 3072) + (-t ^ 3 / 4 - t ^ 5 / 32 - t ^ 7 / 192) * cm 1 x +
      (t ^ 2 / 2 + t ^ 6 / 64 - t ^ 8 / 384) * cm 1 x ^ 2 +
      (t ^ 3 / 3 + t ^ 5 / 24 + t ^ 7 / 32) * cm 1 x ^ 3 +
      (-t ^ 4 / 24 - 3 * t ^ 6 / 32 + t ^ 8 / 128) * cm 1 x ^ 4 +
      (t ^ 5 / 24 - t ^ 7 / 16) * cm 1 x ^ 5 + (5 * t ^ 6 / 48 - t ^ 8 / 96) * cm 1 x ^ 6 +
      (t ^ 7 / 24) * cm 1 x ^ 7 + (t ^ 8 / 192) * cm 1 x ^ 8 := by
  rw [trho_eq]; ring

theorem H_lower {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    t ^ 2 / 4 + t ^ 4 / 64 + t ^ 6 / 128 + t ^ 8 / 8192 - 128 * t ^ 5 ≤ entR (trho t) := by
  rw [entR_trho ht0 ht]
  have hI := int_poly8' (f := fun x => (trho t x - 1) ^ 2 / 2 - (trho t x - 1) ^ 3 / 6 + (trho t x - 1) ^ 4 / 12)
    (t ^ 4 / 32 + t ^ 6 / 384 + t ^ 8 / 3072) (-t ^ 3 / 4 - t ^ 5 / 32 - t ^ 7 / 192)
    (t ^ 2 / 2 + t ^ 6 / 64 - t ^ 8 / 384) (t ^ 3 / 3 + t ^ 5 / 24 + t ^ 7 / 32)
    (-t ^ 4 / 24 - 3 * t ^ 6 / 32 + t ^ 8 / 128) (t ^ 5 / 24 - t ^ 7 / 16)
    (5 * t ^ 6 / 48 - t ^ 8 / 96) (t ^ 7 / 24) (t ^ 8 / 192) (fun y => qpoly_eq t y)
  have hq : Integrable (fun x => (trho t x - 1) ^ 2 / 2 - (trho t x - 1) ^ 3 / 6 + (trho t x - 1) ^ 4 / 12)
      (haar 1) := by
    apply trial_integ_cont
    have := continuous_trho t; fun_prop
  have hk : Integrable (fun x => klFun (trho t x)) (haar 1) :=
    trial_integ_cont (continuous_klFun.comp (continuous_trho t))
  have hmono : ∫ x, ((trho t x - 1) ^ 2 / 2 - (trho t x - 1) ^ 3 / 6 + (trho t x - 1) ^ 4 / 12 - 128 * t ^ 5) ∂haar 1
      ≤ ∫ x, klFun (trho t x) ∂haar 1 := by
    refine integral_mono (hq.sub (integrable_const _)) hk (fun x => ?_)
    have hv := abs_v_le ht0 ht x
    have hb := klFun_one_add_bound (v := trho t x - 1) (by
      have : 2 * t ≤ 1 / 2 := by linarith
      linarith)
    have e : 1 + (trho t x - 1) = trho t x := by ring
    rw [e] at hb
    have h5 : |trho t x - 1| ^ 5 ≤ (2 * t) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hv 5
    have := (abs_le.mp hb).1
    show _ ≤ klFun (trho t x)
    nlinarith
  rw [integral_sub hq (integrable_const _), hI] at hmono
  simp at hmono
  nlinarith

theorem hasDerivAt_cm_lift (n : ℤ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => cm n (lift1 s)) (-(2 * π * n) * sm n (lift1 s)) s := by
  have h : (fun s : ℝ => cm n (lift1 s)) = fun s => Real.cos (2 * π * n * s) := funext fun s => cm_lift1 n s
  rw [h, sm_lift1]
  have := ((hasDerivAt_id s).const_mul (2 * π * n)).cos
  simpa [mul_comm] using this

theorem hasDerivAt_sm_lift (n : ℤ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => sm n (lift1 s)) ((2 * π * n) * cm n (lift1 s)) s := by
  have h : (fun s : ℝ => sm n (lift1 s)) = fun s => Real.sin (2 * π * n * s) := funext fun s => sm_lift1 n s
  rw [h, cm_lift1]
  have := ((hasDerivAt_id s).const_mul (2 * π * n)).sin
  simpa [mul_comm] using this

theorem hasDerivAt_trho_lift (t s : ℝ) :
    HasDerivAt (fun s : ℝ => trho t (lift1 s))
      (t * (-(2 * π * (1:ℤ)) * sm 1 (lift1 s)) + t ^ 2 / 4 * (-(2 * π * (2:ℤ)) * sm 2 (lift1 s))) s := by
  have h1 := (hasDerivAt_cm_lift 1 s).const_mul t
  have h2 := (hasDerivAt_cm_lift 2 s).const_mul (t ^ 2 / 4)
  have := (h1.add h2).const_add 1
  convert this using 1
  funext y
  simp [trho, add_assoc]

theorem dT_sqrt_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) :
    dT (fun y => Real.sqrt (trho t y)) x =
      (-(2 * π * t) * sm 1 x - π * t ^ 2 * sm 2 x) / (2 * Real.sqrt (trho t x)) := by
  rw [dT_apply]
  have hpos : trho t (lift1 (rep x)) ≠ 0 := by
    rw [lift1_rep]; have := trho_pos ht0 ht x; exact ne_of_gt (by linarith)
  have h := (hasDerivAt_trho_lift t (rep x)).sqrt hpos
  rw [h.deriv, lift1_rep]
  push_cast
  congr 1
  ring

theorem isSmoothT_sqrt_trho {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    IsSmoothT (fun y => Real.sqrt (trho t y)) := by
  have h := isSmoothT_trho t
  rw [isSmoothT_iff_lift1] at h ⊢
  refine h.sqrt (fun s => ?_)
  have := trho_pos ht0 ht (lift1 s)
  linarith

theorem four_dT_sqrt_sq {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (x : Torus 1) :
    4 * dT (fun y => Real.sqrt (trho t y)) x ^ 2 =
      4 * π ^ 2 * t ^ 2 * ((1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2) / trho t x := by
  rw [dT_sqrt_trho ht0 ht]
  have hp : 0 < trho t x := by have := trho_pos ht0 ht x; linarith
  have hs : Real.sqrt (trho t x) ^ 2 = trho t x := Real.sq_sqrt hp.le
  have hsm : sm 1 x ^ 2 = 1 - cm 1 x ^ 2 := by have := cm_sq_add_sm_sq 1 x; linarith
  rw [div_pow, mul_pow, hs, sm2_eq]
  field_simp
  rw [hsm] at *
  ring

theorem IR_trho_eq {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    IR (trho t) = ∫ x, 4 * π ^ 2 * t ^ 2 * ((1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2) / trho t x ∂haar 1 := by
  unfold IR
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [weakGrad_ae_dT (isSmoothT_sqrt_trho ht0 ht)] with x hx
  show 4 * weakGrad (fun y => Real.sqrt (trho t y)) x 0 ^ 2 = _
  rw [hx, four_dT_sqrt_sq ht0 ht]

theorem wpoly_eq (t : ℝ) (x : Torus 1) :
    (1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2 *
      (1 - (trho t x - 1) + (trho t x - 1) ^ 2) =
    (1 + t ^ 2 / 4 + t ^ 4 / 16) + (t + t ^ 5 / 8) * cm 1 x +
      (-1 - 3 * t ^ 2 / 4 - 17 * t ^ 4 / 16 + t ^ 6 / 16) * cm 1 x ^ 2 +
      (-t + t ^ 3 - 9 * t ^ 5 / 8) * cm 1 x ^ 3 +
      (t ^ 2 / 2 + 15 * t ^ 4 / 4 - 5 * t ^ 6 / 16) * cm 1 x ^ 4 +
      (-t ^ 3 + 5 * t ^ 5 / 2) * cm 1 x ^ 5 + (-11 * t ^ 4 / 4 + t ^ 6 / 2) * cm 1 x ^ 6 +
      (-3 * t ^ 5 / 2) * cm 1 x ^ 7 + (-t ^ 6 / 4) * cm 1 x ^ 8 := by
  rw [trho_eq]; ring

theorem IR_upper {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) :
    IR (trho t) ≤ 4 * π ^ 2 * t ^ 2 * (1 / 2 + t ^ 2 / 16 + 5 * t ^ 4 / 64 + t ^ 6 / 512 + 32 * t ^ 3) := by
  rw [IR_trho_eq ht0 ht]
  have hI := int_poly8' (f := fun x => (1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2 *
      (1 - (trho t x - 1) + (trho t x - 1) ^ 2))
    (1 + t ^ 2 / 4 + t ^ 4 / 16) (t + t ^ 5 / 8)
    (-1 - 3 * t ^ 2 / 4 - 17 * t ^ 4 / 16 + t ^ 6 / 16) (-t + t ^ 3 - 9 * t ^ 5 / 8)
    (t ^ 2 / 2 + 15 * t ^ 4 / 4 - 5 * t ^ 6 / 16) (-t ^ 3 + 5 * t ^ 5 / 2)
    (-11 * t ^ 4 / 4 + t ^ 6 / 2) (-3 * t ^ 5 / 2) (-t ^ 6 / 4) (fun y => wpoly_eq t y)
  have hc := continuous_trho t
  have hcm := continuous_cm 1
  have hq : Integrable (fun x => (1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2 *
      (1 - (trho t x - 1) + (trho t x - 1) ^ 2)) (haar 1) := by
    apply trial_integ_cont; fun_prop
  have hg : Integrable (fun x => 4 * π ^ 2 * t ^ 2 * ((1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2) / trho t x)
      (haar 1) := by
    apply trial_integ_cont
    refine Continuous.div (by fun_prop) hc (fun x => ?_)
    have := trho_pos ht0 ht x; exact ne_of_gt (by linarith)
  have hmono : ∫ x, 4 * π ^ 2 * t ^ 2 * ((1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2) / trho t x ∂haar 1 ≤
      ∫ x, 4 * π ^ 2 * t ^ 2 * ((1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2 *
        (1 - (trho t x - 1) + (trho t x - 1) ^ 2) + 32 * t ^ 3) ∂haar 1 := by
    refine integral_mono hg ((hq.add (integrable_const _)).const_mul _) (fun x => ?_)
    have hv := abs_v_le ht0 ht x
    have hp : 0 < trho t x := by have := trho_pos ht0 ht x; linarith
    have hinv := inv_one_add_bound (v := trho t x - 1) (by
      have : 2 * t ≤ 1 / 2 := by linarith
      linarith)
    have e : 1 + (trho t x - 1) = trho t x := by ring
    rw [e] at hinv
    have h3 : |trho t x - 1| ^ 3 ≤ (2 * t) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hv 3
    set w := (1 - cm 1 x ^ 2) * (1 + t * cm 1 x) ^ 2 with hw
    have hc1 := abs_cm_le 1 x
    have hc1' : cm 1 x ^ 2 ≤ 1 := by
      have := sq_abs (cm 1 x); nlinarith [abs_nonneg (cm 1 x)]
    have hw0 : 0 ≤ w := mul_nonneg (by linarith) (sq_nonneg _)
    have hw2 : w ≤ 2 := by
      have h1 : 1 - cm 1 x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (cm 1 x)]
      have h2 : (1 + t * cm 1 x) ^ 2 ≤ 2 := by
        have := abs_le.mp hc1
        nlinarith
      calc w ≤ 1 * 2 := mul_le_mul h1 h2 (sq_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have key : w / trho t x ≤ w * (1 - (trho t x - 1) + (trho t x - 1) ^ 2) + 32 * t ^ 3 := by
      have : w / trho t x = w * (1 / trho t x) := by ring
      rw [this]
      calc w * (1 / trho t x) ≤ w * (1 - (trho t x - 1) + (trho t x - 1) ^ 2 + 2 * |trho t x - 1| ^ 3) :=
            mul_le_mul_of_nonneg_left hinv hw0
        _ ≤ w * (1 - (trho t x - 1) + (trho t x - 1) ^ 2) + 32 * t ^ 3 := by
            have : w * (2 * |trho t x - 1| ^ 3) ≤ 2 * (2 * (2 * t) ^ 3) := by
              have h4 : 2 * |trho t x - 1| ^ 3 ≤ 2 * (2 * t) ^ 3 := by linarith
              have h5 : 0 ≤ 2 * |trho t x - 1| ^ 3 := by positivity
              exact mul_le_mul hw2 h4 h5 (by norm_num)
            have h6 : 2 * (2 * (2 * t) ^ 3) = 32 * t ^ 3 := by ring
            have h7 : w * (1 - (trho t x - 1) + (trho t x - 1) ^ 2 + 2 * |trho t x - 1| ^ 3) =
                w * (1 - (trho t x - 1) + (trho t x - 1) ^ 2) + w * (2 * |trho t x - 1| ^ 3) := by ring
            linarith
    have hπ : 0 ≤ 4 * π ^ 2 * t ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left key hπ
    rw [mul_div_assoc]
    show _ ≤ 4 * π ^ 2 * t ^ 2 * _
    linarith
  refine hmono.trans ?_
  rw [integral_const_mul, integral_add hq (integrable_const _), hI]
  simp
  nlinarith [sq_nonneg π, sq_nonneg t]

/-- The trial density at `t = 10⁻⁶` has all the required properties. -/
theorem trial_exists_aux :
    ∃ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
      MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) ∧ 0 < GR poissonKernel ρ ∧
      DR poissonKernel ρ < aCos * (2 * GR poissonKernel ρ) := by
  have ht0 : (0 : ℝ) ≤ 1 / 1000000 := by norm_num
  have ht : (1 / 1000000 : ℝ) ≤ 1 / 100 := by norm_num
  set t : ℝ := 1 / 1000000 with htdef
  have h0 := trho_nonneg ht0 ht
  have h1 := trho_int t
  have hH : MemH1 (haar 1) (fun x => Real.sqrt (trho t x)) :=
    memH1_of_contDiff (isSmoothT_sqrt_trho ht0 ht)
  refine ⟨trho t, h0, h1, hH, ?_, ?_⟩
  · unfold GR
    rw [cqR_trho ht0 ht]
    have := H_lower ht0 ht
    have e : t = 1 / 1000000 := htdef
    rw [e] at this ⊢
    norm_num at this ⊢
    linarith
  · have hd := diss_expand poisson_good h0 h1 hH
    rw [int_C2_trho ht0 ht, int_C1sq_trho ht0 ht] at hd
    have hIR := IR_upper ht0 ht
    have hHl := H_lower ht0 ht
    have hπ : 0 < π ^ 2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hHl hπ.le
    unfold GR aCos
    rw [cqR_trho ht0 ht, hd]
    have e : t = 1 / 1000000 := htdef
    rw [e] at hIR hm ⊢
    norm_num at hIR hm ⊢
    nlinarith [hIR, hm, hπ]
/-- A smooth positive probability density `ρ` with `D(ρ) < 4π² · 2 G(ρ)` and `G(ρ) > 0` for the
Poisson kernel (the trial density of Proposition 9.10). -/
theorem trial_exists :
    ∃ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
      MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) ∧ 0 < GR poissonKernel ρ ∧
      DR poissonKernel ρ < aCos * (2 * GR poissonKernel ρ) := by
  exact trial_exists_aux

end SharpLSI.FL.Ex.LaneD
