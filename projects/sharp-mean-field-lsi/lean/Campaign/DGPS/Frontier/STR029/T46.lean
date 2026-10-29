import DGPS.Frontier.STR029.T45
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# STR029.46 — Exact trigonometric information coefficients

Provides (all declarations are in the namespace `DGPS.Frontier.STR029`):
* `str029_46_exact_trigonometric_information_coefficients`: the closed polynomial forms of
  `H4_STR02945` and `I4_STR02945` in the coefficients `A B C D E F`, with `R0^2 = A^2 + B^2`
  and `P3 = A^3 - 3AB^2` written out.
* `cos4_STR02946`, `sin4_STR02946`: the multiple-angle formulas for `cos 4t` and `sin 4t`.
* `b_cs_STR02946`, `p_cs_STR02946`, `v_cs_STR02946`, `q_cs_STR02946`: the profiles `bFun`,
  `pFun`, `vFun`, `qFun` written as polynomials in `Real.cos t` and `Real.sin t`.
* `dp_cs_STR02946`, `dq_cs_STR02946`: the derivatives of `pFun` and `qFun` in the same form.
* `cosW_STR02946`: Wallis recursion `⟨cos^(n+2)⟩ = (n+1)/(n+2) ⟨cos^n⟩` for the normalized integral.
* `sinW_STR02946`: `⟨cos^n · sin⟩ = 0` for every natural `n`.
* `w0_STR02946`, `w2_STR02946`, `w4_STR02946`, `w6_STR02946`, `w8_STR02946`: the even moments
  `⟨cos^n⟩` for `n = 0, 2, 4, 6, 8`, equal to `1, 1/2, 3/8, 5/16, 35/128`.
* `mean9_STR02946`: the normalized mean of a nine-term trigonometric polynomial.
* `mom_q2_STR02946`, `mom_pbq_STR02946`, `mom_p2q_STR02946`, `mom_p2b2_STR02946`,
  `mom_p2_STR02946`, `mom_b2_STR02946`, `mom_p3b_STR02946`, `mom_p4_STR02946`,
  `mom_qd2_STR02946`, `mom_pdqdv_STR02946`, `mom_pd2q_STR02946`, `mom_pd2v2_STR02946`,
  `mom_pd2_STR02946`, `mom_v2_STR02946`: the fourteen scalar moments that occur in
  `H4_STR02945` and `I4_STR02945`, each as a polynomial in the coefficients.

R5 notes:
* Statement: the main declaration is the specification's two identities, read literally for all
  real `A B C D E F`. No hypothesis is added and nothing is weakened. `R0^2` and `P3` are
  written out as `A^2 + B^2` and `A^3 - 3*A*B^2`.
* Definitions: `H4_STR02945` and `I4_STR02945` are used exactly as defined in the T45 file,
  including the product of two normalized integrals in the `¼(⟨p²b²⟩ − ⟨p²⟩⟨b²⟩)` term of `H4`
  and the `−½⟨p'²⟩⟨v²⟩` term of `I4`.
* Normalization: `normInt_STR02933 f = (2π)⁻¹ ∫_{(0,2π]} f`, the normalized angular measure
  `dt/(2π)` of T33 and T45. Every moment below is taken with this convention.
* Moments: the specification lists the moment values. This file does not take them as inputs.
  Each of the fourteen moments is computed from the T45 definitions by a pointwise reduction of the
  integrand to a polynomial in `Real.cos t` and `Real.sin t`, modulo `sin² + cos² = 1`, with an
  explicit quotient certificate checked by `linear_combination`. The even powers of cosine are then
  averaged with the Wallis values, and the terms `cos^n · sin` average to zero by the fundamental
  theorem of calculus with primitive `−cos^(n+1)/(n+1)`.
* Combination: the main declaration rewrites the fourteen moments in the unfolded `H4` and `I4`
  and closes each identity by `ring`.
* Mathlib facts used: `integral_cos_pow` (at the pinned commit), `intervalIntegral.integral_of_le`,
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `HasDerivAt.pow`, `Real.cos_three_mul`,
  `Real.cos_two_mul`, `Real.sin_two_mul`, `Real.sin_sq_add_cos_sq`.
* Length: the file is longer than the 125–150 line estimate, because the quotient certificates
  are written out explicitly. The estimate was not measured.
-/

open MeasureTheory Set Real

namespace DGPS.Frontier.STR029

theorem cos4_STR02946 (t : ℝ) :
    Real.cos (4 * t) = 8 * Real.cos t ^ 4 - 8 * Real.cos t ^ 2 + 1 := by
  have h : Real.cos (4 * t) = 2 * Real.cos (2 * t) ^ 2 - 1 := by
    rw [show (4 : ℝ) * t = 2 * (2 * t) by ring, Real.cos_two_mul (2 * t)]
  rw [h, Real.cos_two_mul t]
  ring

theorem sin4_STR02946 (t : ℝ) :
    Real.sin (4 * t) = 4 * Real.sin t * Real.cos t * (2 * Real.cos t ^ 2 - 1) := by
  rw [show (4 : ℝ) * t = 2 * (2 * t) by ring, Real.sin_two_mul (2 * t), Real.sin_two_mul t,
    Real.cos_two_mul t]
  ring

theorem b_cs_STR02946 (t : ℝ) :
    bFun_STR02945 t = 4 * Real.cos t ^ 3 - 3 * Real.cos t := by
  rw [bFun_STR02945, Real.cos_three_mul]

theorem p_cs_STR02946 (A B t : ℝ) :
    pFun_STR02945 A B t = A * Real.cos t + B * Real.sin t := rfl

theorem v_cs_STR02946 (A B t : ℝ) :
    vFun_STR02945 A B t =
      (4 * Real.cos t ^ 3 - 3 * Real.cos t) + (A * Real.cos t + B * Real.sin t) := by
  rw [vFun_STR02945, b_cs_STR02946, p_cs_STR02946]

theorem q_cs_STR02946 (C D E F t : ℝ) :
    qFun_STR02945 C D E F t =
      C * (2 * Real.cos t ^ 2 - 1) + D * (2 * Real.sin t * Real.cos t) +
        E * (8 * Real.cos t ^ 4 - 8 * Real.cos t ^ 2 + 1) +
        F * (4 * Real.sin t * Real.cos t * (2 * Real.cos t ^ 2 - 1)) := by
  rw [qFun_STR02945, Real.cos_two_mul t, Real.sin_two_mul t, cos4_STR02946, sin4_STR02946]

theorem dp_cs_STR02946 (A B t : ℝ) :
    deriv (pFun_STR02945 A B) t = B * Real.cos t - A * Real.sin t := by
  rw [congrFun (deriv_pFun_STR02945 A B) t]
  simp only [mode2_STR02945, mode1_STR02945, Nat.cast_one, one_mul, zero_mul, add_zero]
  ring

theorem dq_cs_STR02946 (C D E F t : ℝ) :
    deriv (qFun_STR02945 C D E F) t =
      2 * D * (2 * Real.cos t ^ 2 - 1) - 2 * C * (2 * Real.sin t * Real.cos t) +
        4 * F * (8 * Real.cos t ^ 4 - 8 * Real.cos t ^ 2 + 1) -
        4 * E * (4 * Real.sin t * Real.cos t * (2 * Real.cos t ^ 2 - 1)) := by
  rw [congrFun (deriv_qFun_STR02945 C D E F) t]
  simp only [mode2_STR02945, mode1_STR02945, Nat.cast_ofNat]
  rw [cos4_STR02946, sin4_STR02946, Real.cos_two_mul t, Real.sin_two_mul t]
  ring

theorem cosW_STR02946 (m n : ℕ) (h : m = n + 2) :
    normInt_STR02933 (fun t => Real.cos t ^ m) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * normInt_STR02933 (fun t => Real.cos t ^ n) := by
  subst h
  have hle : (0 : ℝ) ≤ 2 * π := by positivity
  unfold normInt_STR02933
  rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle,
    integral_cos_pow, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  ring

theorem sinW_STR02946 (n : ℕ) :
    normInt_STR02933 (fun t => Real.cos t ^ n * Real.sin t) = 0 := by
  have hc : Continuous (fun t : ℝ => Real.cos t ^ n * Real.sin t) := by fun_prop
  have hF : ∀ x ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun y : ℝ => -(Real.cos y ^ (n + 1)) / ((n : ℝ) + 1))
        (Real.cos x ^ n * Real.sin x) x := by
    intro x _
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have h1 := (((Real.hasDerivAt_cos x).pow (n + 1)).neg).div_const ((n : ℝ) + 1)
    convert h1 using 1
    rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, eq_div_iff hn]
    ring
  have hle : (0 : ℝ) ≤ 2 * π := by positivity
  unfold normInt_STR02933
  rw [← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hc.intervalIntegrable 0 (2 * π))]
  simp

theorem w0_STR02946 : normInt_STR02933 (fun t => Real.cos t ^ 0) = 1 := by
  simp only [pow_zero]
  exact normInt_const_STR02944 1

theorem w2_STR02946 : normInt_STR02933 (fun t => Real.cos t ^ 2) = 1 / 2 := by
  rw [cosW_STR02946 2 0 rfl, w0_STR02946]
  norm_num

theorem w4_STR02946 : normInt_STR02933 (fun t => Real.cos t ^ 4) = 3 / 8 := by
  rw [cosW_STR02946 4 2 rfl, w2_STR02946]
  norm_num

theorem w6_STR02946 : normInt_STR02933 (fun t => Real.cos t ^ 6) = 5 / 16 := by
  rw [cosW_STR02946 6 4 rfl, w4_STR02946]
  norm_num

theorem w8_STR02946 : normInt_STR02933 (fun t => Real.cos t ^ 8) = 35 / 128 := by
  rw [cosW_STR02946 8 6 rfl, w6_STR02946]
  norm_num

theorem mean9_STR02946 (x0 x2 x4 x6 x8 y1 y3 y5 y7 : ℝ) :
    normInt_STR02933 (fun t => x0 * Real.cos t ^ 0 + x2 * Real.cos t ^ 2 +
      x4 * Real.cos t ^ 4 + x6 * Real.cos t ^ 6 + x8 * Real.cos t ^ 8 +
      y1 * (Real.cos t ^ 1 * Real.sin t) + y3 * (Real.cos t ^ 3 * Real.sin t) +
      y5 * (Real.cos t ^ 5 * Real.sin t) + y7 * (Real.cos t ^ 7 * Real.sin t)) =
      x0 + x2 / 2 + x4 * (3 / 8) + x6 * (5 / 16) + x8 * (35 / 128) := by
  simp (disch := fun_prop) only [normInt_add_STR02944, normInt_mul_const_STR02933,
    sinW_STR02946, w0_STR02946, w2_STR02946, w4_STR02946, w6_STR02946, w8_STR02946]
  ring

theorem mom_q2_STR02946 (C D E F : ℝ) :
    normInt_STR02933 (fun t => qFun_STR02945 C D E F t ^ 2) = ((1/2) * F ^ 2 + (1/2) * E ^ 2 + (1/2) * D ^ 2 + (1/2) * C ^ 2) := by
  have h1 : ∀ t : ℝ, qFun_STR02945 C D E F t ^ 2 = (E ^ 2 + (-2) * C * E + C ^ 2) * Real.cos t ^ 0 + ((16) * F ^ 2 + (-16) * E ^ 2 + (-16) * D * F + (4) * D ^ 2 + (20) * C * E + (-4) * C ^ 2) * Real.cos t ^ 2 + ((-80) * F ^ 2 + (80) * E ^ 2 + (48) * D * F + (-4) * D ^ 2 + (-48) * C * E + (4) * C ^ 2) * Real.cos t ^ 4 + ((128) * F ^ 2 + (-128) * E ^ 2 + (-32) * D * F + (32) * C * E) * Real.cos t ^ 6 + ((-64) * F ^ 2 + (64) * E ^ 2) * Real.cos t ^ 8 + ((-8) * E * F + (4) * D * E + (8) * C * F + (-4) * C * D) * (Real.cos t ^ 1 * Real.sin t) + ((80) * E * F + (-32) * D * E + (-32) * C * F + (8) * C * D) * (Real.cos t ^ 3 * Real.sin t) + ((-192) * E * F + (32) * D * E + (32) * C * F) * (Real.cos t ^ 5 * Real.sin t) + ((128) * E * F) * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [q_cs_STR02946]
    linear_combination (((16) * F ^ 2 * Real.cos t ^ 2 + (-64) * F ^ 2 * Real.cos t ^ 4 + (64) * F ^ 2 * Real.cos t ^ 6 + (-16) * D * F * Real.cos t ^ 2 + (32) * D * F * Real.cos t ^ 4 + (4) * D ^ 2 * Real.cos t ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_pbq_STR02946 (A B C D E F : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t * bFun_STR02945 t * qFun_STR02945 C D E F t) = ((1/4) * B * F + (-1/4) * B * D + (1/4) * A * E + (1/4) * A * C) := by
  have h1 : ∀ t : ℝ, pFun_STR02945 A B t * bFun_STR02945 t * qFun_STR02945 C D E F t = 0 * Real.cos t ^ 0 + ((12) * B * F + (-6) * B * D + (-3) * A * E + (3) * A * C) * Real.cos t ^ 2 + ((-52) * B * F + (14) * B * D + (28) * A * E + (-10) * A * C) * Real.cos t ^ 4 + ((72) * B * F + (-8) * B * D + (-56) * A * E + (8) * A * C) * Real.cos t ^ 6 + ((-32) * B * F + (32) * A * E) * Real.cos t ^ 8 + ((-3) * B * E + (3) * B * C) * (Real.cos t ^ 1 * Real.sin t) + ((28) * B * E + (-10) * B * C + (12) * A * F + (-6) * A * D) * (Real.cos t ^ 3 * Real.sin t) + ((-56) * B * E + (8) * B * C + (-40) * A * F + (8) * A * D) * (Real.cos t ^ 5 * Real.sin t) + ((32) * B * E + (32) * A * F) * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946, b_cs_STR02946, q_cs_STR02946]
    linear_combination (((12) * B * F * Real.cos t ^ 2 + (-40) * B * F * Real.cos t ^ 4 + (32) * B * F * Real.cos t ^ 6 + (-6) * B * D * Real.cos t ^ 2 + (8) * B * D * Real.cos t ^ 4)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_p2q_STR02946 (A B C D E F : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2 * qFun_STR02945 C D E F t) = ((-1/4) * B ^ 2 * C + (1/2) * A * B * D + (1/4) * A ^ 2 * C) := by
  have h1 : ∀ t : ℝ, pFun_STR02945 A B t ^ 2 * qFun_STR02945 C D E F t = (B ^ 2 * E + (-1) * B ^ 2 * C) * Real.cos t ^ 0 + ((-9) * B ^ 2 * E + (3) * B ^ 2 * C + (-8) * A * B * F + (4) * A * B * D + A ^ 2 * E + (-1) * A ^ 2 * C) * Real.cos t ^ 2 + ((16) * B ^ 2 * E + (-2) * B ^ 2 * C + (24) * A * B * F + (-4) * A * B * D + (-8) * A ^ 2 * E + (2) * A ^ 2 * C) * Real.cos t ^ 4 + ((-8) * B ^ 2 * E + (-16) * A * B * F + (8) * A ^ 2 * E) * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + ((-4) * B ^ 2 * F + (2) * B ^ 2 * D + (2) * A * B * E + (-2) * A * B * C) * (Real.cos t ^ 1 * Real.sin t) + ((12) * B ^ 2 * F + (-2) * B ^ 2 * D + (-16) * A * B * E + (4) * A * B * C + (-4) * A ^ 2 * F + (2) * A ^ 2 * D) * (Real.cos t ^ 3 * Real.sin t) + ((-8) * B ^ 2 * F + (16) * A * B * E + (8) * A ^ 2 * F) * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946, q_cs_STR02946]
    linear_combination (((-4) * B ^ 2 * F * Real.cos t * Real.sin t + (8) * B ^ 2 * F * Real.cos t ^ 3 * Real.sin t + B ^ 2 * E + (-8) * B ^ 2 * E * Real.cos t ^ 2 + (8) * B ^ 2 * E * Real.cos t ^ 4 + (2) * B ^ 2 * D * Real.cos t * Real.sin t + (-1) * B ^ 2 * C + (2) * B ^ 2 * C * Real.cos t ^ 2 + (-8) * A * B * F * Real.cos t ^ 2 + (16) * A * B * F * Real.cos t ^ 4 + (4) * A * B * D * Real.cos t ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_p2b2_STR02946 (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2 * bFun_STR02945 t ^ 2) = ((1/4) * B ^ 2 + (1/4) * A ^ 2) := by
  have h1 : ∀ t : ℝ, pFun_STR02945 A B t ^ 2 * bFun_STR02945 t ^ 2 = 0 * Real.cos t ^ 0 + ((9) * B ^ 2) * Real.cos t ^ 2 + ((-33) * B ^ 2 + (9) * A ^ 2) * Real.cos t ^ 4 + ((40) * B ^ 2 + (-24) * A ^ 2) * Real.cos t ^ 6 + ((-16) * B ^ 2 + (16) * A ^ 2) * Real.cos t ^ 8 + 0 * (Real.cos t ^ 1 * Real.sin t) + ((18) * A * B) * (Real.cos t ^ 3 * Real.sin t) + ((-48) * A * B) * (Real.cos t ^ 5 * Real.sin t) + ((32) * A * B) * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946, b_cs_STR02946]
    linear_combination (((9) * B ^ 2 * Real.cos t ^ 2 + (-24) * B ^ 2 * Real.cos t ^ 4 + (16) * B ^ 2 * Real.cos t ^ 6)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_p2_STR02946 (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 2) = ((1/2) * B ^ 2 + (1/2) * A ^ 2) := by
  have h1 : ∀ t : ℝ, pFun_STR02945 A B t ^ 2 = (B ^ 2) * Real.cos t ^ 0 + ((-1) * B ^ 2 + A ^ 2) * Real.cos t ^ 2 + 0 * Real.cos t ^ 4 + 0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + ((2) * A * B) * (Real.cos t ^ 1 * Real.sin t) + 0 * (Real.cos t ^ 3 * Real.sin t) + 0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946]
    linear_combination ((B ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_b2_STR02946 :
    normInt_STR02933 (fun t => bFun_STR02945 t ^ 2) = ((1/2)) := by
  have h1 : ∀ t : ℝ, bFun_STR02945 t ^ 2 = 0 * Real.cos t ^ 0 + ((9)) * Real.cos t ^ 2 + ((-24)) * Real.cos t ^ 4 + ((16)) * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + 0 * (Real.cos t ^ 1 * Real.sin t) + 0 * (Real.cos t ^ 3 * Real.sin t) + 0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [b_cs_STR02946]
    linear_combination (0) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_p3b_STR02946 (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 3 * bFun_STR02945 t) = ((-3/8) * A * B ^ 2 + (1/8) * A ^ 3) := by
  have h1 : ∀ t : ℝ, pFun_STR02945 A B t ^ 3 * bFun_STR02945 t = 0 * Real.cos t ^ 0 + ((-9) * A * B ^ 2) * Real.cos t ^ 2 + ((21) * A * B ^ 2 + (-3) * A ^ 3) * Real.cos t ^ 4 + ((-12) * A * B ^ 2 + (4) * A ^ 3) * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + ((-3) * B ^ 3) * (Real.cos t ^ 1 * Real.sin t) + ((7) * B ^ 3 + (-9) * A ^ 2 * B) * (Real.cos t ^ 3 * Real.sin t) + ((-4) * B ^ 3 + (12) * A ^ 2 * B) * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946, b_cs_STR02946]
    linear_combination (((-3) * B ^ 3 * Real.cos t * Real.sin t + (4) * B ^ 3 * Real.cos t ^ 3 * Real.sin t + (-9) * A * B ^ 2 * Real.cos t ^ 2 + (12) * A * B ^ 2 * Real.cos t ^ 4)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_p4_STR02946 (A B : ℝ) :
    normInt_STR02933 (fun t => pFun_STR02945 A B t ^ 4) = ((3/8) * B ^ 4 + (3/4) * A ^ 2 * B ^ 2 + (3/8) * A ^ 4) := by
  have h1 : ∀ t : ℝ, pFun_STR02945 A B t ^ 4 = (B ^ 4) * Real.cos t ^ 0 + ((-2) * B ^ 4 + (6) * A ^ 2 * B ^ 2) * Real.cos t ^ 2 + (B ^ 4 + (-6) * A ^ 2 * B ^ 2 + A ^ 4) * Real.cos t ^ 4 + 0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + ((4) * A * B ^ 3) * (Real.cos t ^ 1 * Real.sin t) + ((-4) * A * B ^ 3 + (4) * A ^ 3 * B) * (Real.cos t ^ 3 * Real.sin t) + 0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [p_cs_STR02946]
    linear_combination ((B ^ 4 + B ^ 4 * Real.sin t ^ 2 + (-1) * B ^ 4 * Real.cos t ^ 2 + (4) * A * B ^ 3 * Real.cos t * Real.sin t + (6) * A ^ 2 * B ^ 2 * Real.cos t ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_qd2_STR02946 (C D E F : ℝ) :
    normInt_STR02933 (fun t => deriv (qFun_STR02945 C D E F) t ^ 2) = ((8) * F ^ 2 + (8) * E ^ 2 + (2) * D ^ 2 + (2) * C ^ 2) := by
  have h1 : ∀ t : ℝ, deriv (qFun_STR02945 C D E F) t ^ 2 = ((16) * F ^ 2 + (-16) * D * F + (4) * D ^ 2) * Real.cos t ^ 0 + ((-256) * F ^ 2 + (256) * E ^ 2 + (160) * D * F + (-16) * D ^ 2 + (-128) * C * E + (16) * C ^ 2) * Real.cos t ^ 2 + ((1280) * F ^ 2 + (-1280) * E ^ 2 + (-384) * D * F + (16) * D ^ 2 + (384) * C * E + (-16) * C ^ 2) * Real.cos t ^ 4 + ((-2048) * F ^ 2 + (2048) * E ^ 2 + (256) * D * F + (-256) * C * E) * Real.cos t ^ 6 + ((1024) * F ^ 2 + (-1024) * E ^ 2) * Real.cos t ^ 8 + ((128) * E * F + (-64) * D * E + (-32) * C * F + (16) * C * D) * (Real.cos t ^ 1 * Real.sin t) + ((-1280) * E * F + (256) * D * E + (256) * C * F + (-32) * C * D) * (Real.cos t ^ 3 * Real.sin t) + ((3072) * E * F + (-256) * D * E + (-256) * C * F) * (Real.cos t ^ 5 * Real.sin t) + ((-2048) * E * F) * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [dq_cs_STR02946]
    linear_combination (((256) * E ^ 2 * Real.cos t ^ 2 + (-1024) * E ^ 2 * Real.cos t ^ 4 + (1024) * E ^ 2 * Real.cos t ^ 6 + (-128) * C * E * Real.cos t ^ 2 + (256) * C * E * Real.cos t ^ 4 + (16) * C ^ 2 * Real.cos t ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_pdqdv_STR02946 (A B C D E F : ℝ) :
    normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t * deriv (qFun_STR02945 C D E F) t * vFun_STR02945 A B t) = (B * F + (1/2) * B * D + (-1/2) * B ^ 2 * C + A * E + (-1/2) * A * C + A * B * D + (1/2) * A ^ 2 * C) := by
  have h1 : ∀ t : ℝ, deriv (pFun_STR02945 A B) t * deriv (qFun_STR02945 C D E F) t * vFun_STR02945 A B t = ((-4) * A * B * F + (2) * A * B * D) * Real.cos t ^ 0 + ((-12) * B * F + (6) * B * D + (16) * B ^ 2 * E + (-4) * B ^ 2 * C + (48) * A * E + (-12) * A * C + (40) * A * B * F + (-8) * A * B * D + (-16) * A ^ 2 * E + (4) * A ^ 2 * C) * Real.cos t ^ 2 + ((112) * B * F + (-20) * B * D + (-48) * B ^ 2 * E + (4) * B ^ 2 * C + (-208) * A * E + (28) * A * C + (-96) * A * B * F + (8) * A * B * D + (48) * A ^ 2 * E + (-4) * A ^ 2 * C) * Real.cos t ^ 4 + ((-224) * B * F + (16) * B * D + (32) * B ^ 2 * E + (288) * A * E + (-16) * A * C + (64) * A * B * F + (-32) * A ^ 2 * E) * Real.cos t ^ 6 + ((128) * B * F + (-128) * A * E) * Real.cos t ^ 8 + ((4) * B ^ 2 * F + (-2) * B ^ 2 * D + (12) * A * F + (-6) * A * D + (-16) * A * B * E + (4) * A * B * C + (-4) * A ^ 2 * F + (2) * A ^ 2 * D) * (Real.cos t ^ 1 * Real.sin t) + ((-48) * B * E + (12) * B * C + (-32) * B ^ 2 * F + (4) * B ^ 2 * D + (-112) * A * F + (20) * A * D + (64) * A * B * E + (-8) * A * B * C + (32) * A ^ 2 * F + (-4) * A ^ 2 * D) * (Real.cos t ^ 3 * Real.sin t) + ((160) * B * E + (-16) * B * C + (32) * B ^ 2 * F + (224) * A * F + (-16) * A * D + (-64) * A * B * E + (-32) * A ^ 2 * F) * (Real.cos t ^ 5 * Real.sin t) + ((-128) * B * E + (-128) * A * F) * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [dp_cs_STR02946, dq_cs_STR02946, v_cs_STR02946]
    linear_combination (((16) * B ^ 2 * E * Real.cos t ^ 2 + (-32) * B ^ 2 * E * Real.cos t ^ 4 + (-4) * B ^ 2 * C * Real.cos t ^ 2 + (48) * A * E * Real.cos t ^ 2 + (-160) * A * E * Real.cos t ^ 4 + (128) * A * E * Real.cos t ^ 6 + (-12) * A * C * Real.cos t ^ 2 + (16) * A * C * Real.cos t ^ 4 + (-4) * A * B * F + (32) * A * B * F * Real.cos t ^ 2 + (-32) * A * B * F * Real.cos t ^ 4 + (-16) * A * B * E * Real.cos t * Real.sin t + (32) * A * B * E * Real.cos t ^ 3 * Real.sin t + (2) * A * B * D + (-4) * A * B * D * Real.cos t ^ 2 + (4) * A * B * C * Real.cos t * Real.sin t + (-16) * A ^ 2 * E * Real.cos t ^ 2 + (32) * A ^ 2 * E * Real.cos t ^ 4 + (4) * A ^ 2 * C * Real.cos t ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_pd2q_STR02946 (A B C D E F : ℝ) :
    normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2 * qFun_STR02945 C D E F t) = ((1/4) * B ^ 2 * C + (-1/2) * A * B * D + (-1/4) * A ^ 2 * C) := by
  have h1 : ∀ t : ℝ, deriv (pFun_STR02945 A B) t ^ 2 * qFun_STR02945 C D E F t = (A ^ 2 * E + (-1) * A ^ 2 * C) * Real.cos t ^ 0 + (B ^ 2 * E + (-1) * B ^ 2 * C + (8) * A * B * F + (-4) * A * B * D + (-9) * A ^ 2 * E + (3) * A ^ 2 * C) * Real.cos t ^ 2 + ((-8) * B ^ 2 * E + (2) * B ^ 2 * C + (-24) * A * B * F + (4) * A * B * D + (16) * A ^ 2 * E + (-2) * A ^ 2 * C) * Real.cos t ^ 4 + ((8) * B ^ 2 * E + (16) * A * B * F + (-8) * A ^ 2 * E) * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + ((-2) * A * B * E + (2) * A * B * C + (-4) * A ^ 2 * F + (2) * A ^ 2 * D) * (Real.cos t ^ 1 * Real.sin t) + ((-4) * B ^ 2 * F + (2) * B ^ 2 * D + (16) * A * B * E + (-4) * A * B * C + (12) * A ^ 2 * F + (-2) * A ^ 2 * D) * (Real.cos t ^ 3 * Real.sin t) + ((8) * B ^ 2 * F + (-16) * A * B * E + (-8) * A ^ 2 * F) * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [dp_cs_STR02946, q_cs_STR02946]
    linear_combination (((8) * A * B * F * Real.cos t ^ 2 + (-16) * A * B * F * Real.cos t ^ 4 + (-4) * A * B * D * Real.cos t ^ 2 + (-4) * A ^ 2 * F * Real.cos t * Real.sin t + (8) * A ^ 2 * F * Real.cos t ^ 3 * Real.sin t + A ^ 2 * E + (-8) * A ^ 2 * E * Real.cos t ^ 2 + (8) * A ^ 2 * E * Real.cos t ^ 4 + (2) * A ^ 2 * D * Real.cos t * Real.sin t + (-1) * A ^ 2 * C + (2) * A ^ 2 * C * Real.cos t ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_pd2v2_STR02946 (A B : ℝ) :
    normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2 * vFun_STR02945 A B t ^ 2) = ((1/4) * B ^ 2 + (1/8) * B ^ 4 + (3/4) * A * B ^ 2 + (1/4) * A ^ 2 + (1/4) * A ^ 2 * B ^ 2 + (-1/4) * A ^ 3 + (1/8) * A ^ 4) := by
  have h1 : ∀ t : ℝ, deriv (pFun_STR02945 A B) t ^ 2 * vFun_STR02945 A B t ^ 2 = (A ^ 2 * B ^ 2) * Real.cos t ^ 0 + (B ^ 4 + (12) * A * B ^ 2 + (9) * A ^ 2 + (-6) * A ^ 2 * B ^ 2 + (-6) * A ^ 3 + A ^ 4) * Real.cos t ^ 2 + ((9) * B ^ 2 + (-1) * B ^ 4 + (-34) * A * B ^ 2 + (-33) * A ^ 2 + (6) * A ^ 2 * B ^ 2 + (14) * A ^ 3 + (-1) * A ^ 4) * Real.cos t ^ 4 + ((-24) * B ^ 2 + (24) * A * B ^ 2 + (40) * A ^ 2 + (-8) * A ^ 3) * Real.cos t ^ 6 + ((16) * B ^ 2 + (-16) * A ^ 2) * Real.cos t ^ 8 + ((-2) * A * B ^ 3 + (-6) * A ^ 2 * B + (2) * A ^ 3 * B) * (Real.cos t ^ 1 * Real.sin t) + ((-6) * B ^ 3 + (-18) * A * B + (4) * A * B ^ 3 + (26) * A ^ 2 * B + (-4) * A ^ 3 * B) * (Real.cos t ^ 3 * Real.sin t) + ((8) * B ^ 3 + (48) * A * B + (-24) * A ^ 2 * B) * (Real.cos t ^ 5 * Real.sin t) + ((-32) * A * B) * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [dp_cs_STR02946, v_cs_STR02946]
    linear_combination ((B ^ 4 * Real.cos t ^ 2 + (12) * A * B ^ 2 * Real.cos t ^ 2 + (-16) * A * B ^ 2 * Real.cos t ^ 4 + (-2) * A * B ^ 3 * Real.cos t * Real.sin t + (9) * A ^ 2 * Real.cos t ^ 2 + (-24) * A ^ 2 * Real.cos t ^ 4 + (16) * A ^ 2 * Real.cos t ^ 6 + (-6) * A ^ 2 * B * Real.cos t * Real.sin t + (8) * A ^ 2 * B * Real.cos t ^ 3 * Real.sin t + A ^ 2 * B ^ 2 + A ^ 2 * B ^ 2 * Real.sin t ^ 2 + (-5) * A ^ 2 * B ^ 2 * Real.cos t ^ 2 + (-6) * A ^ 3 * Real.cos t ^ 2 + (8) * A ^ 3 * Real.cos t ^ 4 + (2) * A ^ 3 * B * Real.cos t * Real.sin t + A ^ 4 * Real.cos t ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_pd2_STR02946 (A B : ℝ) :
    normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2) = ((1/2) * B ^ 2 + (1/2) * A ^ 2) := by
  have h1 : ∀ t : ℝ, deriv (pFun_STR02945 A B) t ^ 2 = (A ^ 2) * Real.cos t ^ 0 + (B ^ 2 + (-1) * A ^ 2) * Real.cos t ^ 2 + 0 * Real.cos t ^ 4 + 0 * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + ((-2) * A * B) * (Real.cos t ^ 1 * Real.sin t) + 0 * (Real.cos t ^ 3 * Real.sin t) + 0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [dp_cs_STR02946]
    linear_combination ((A ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem mom_v2_STR02946 (A B : ℝ) :
    normInt_STR02933 (fun t => vFun_STR02945 A B t ^ 2) = ((1/2) + (1/2) * B ^ 2 + (1/2) * A ^ 2) := by
  have h1 : ∀ t : ℝ, vFun_STR02945 A B t ^ 2 = (B ^ 2) * Real.cos t ^ 0 + ((9) + (-1) * B ^ 2 + (-6) * A + A ^ 2) * Real.cos t ^ 2 + ((-24) + (8) * A) * Real.cos t ^ 4 + ((16)) * Real.cos t ^ 6 + 0 * Real.cos t ^ 8 + ((-6) * B + (2) * A * B) * (Real.cos t ^ 1 * Real.sin t) + ((8) * B) * (Real.cos t ^ 3 * Real.sin t) + 0 * (Real.cos t ^ 5 * Real.sin t) + 0 * (Real.cos t ^ 7 * Real.sin t) := by
    intro t
    rw [v_cs_STR02946]
    linear_combination ((B ^ 2)) * Real.sin_sq_add_cos_sq t
  rw [normInt_congr_STR02945 h1, mean9_STR02946]
  ring

theorem str029_46_exact_trigonometric_information_coefficients (A B C D E F : ℝ) :
    H4_STR02945 A B C D E F = (C ^ 2 + D ^ 2 + E ^ 2 + F ^ 2) / 4 +
      (A * (C + E) + B * (F - D)) / 4 + ((A ^ 2 - B ^ 2) * C + 2 * A * B * D) / 4 +
      (A ^ 3 - 3 * A * B ^ 2) / 24 - 3 * (A ^ 2 + B ^ 2) ^ 2 / 64 ∧
    I4_STR02945 A B C D E F = 2 * (C ^ 2 + D ^ 2) + 8 * (E ^ 2 + F ^ 2) - A * C + B * D +
      2 * A * E + 2 * B * F + 3 / 4 * (A ^ 2 - B ^ 2) * C + 3 / 2 * A * B * D -
      (A ^ 3 - 3 * A * B ^ 2) / 8 - (A ^ 2 + B ^ 2) ^ 2 / 16 := by
  unfold H4_STR02945 I4_STR02945
  rw [mom_q2_STR02946, mom_pbq_STR02946, mom_p2q_STR02946, mom_p2b2_STR02946, mom_p2_STR02946,
    mom_b2_STR02946, mom_p3b_STR02946, mom_p4_STR02946, mom_qd2_STR02946, mom_pdqdv_STR02946,
    mom_pd2q_STR02946, mom_pd2v2_STR02946, mom_pd2_STR02946, mom_v2_STR02946]
  constructor <;> ring

end DGPS.Frontier.STR029
