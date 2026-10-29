import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# STR029.52: Kernel uniqueness of the range operator

Task id: STR029.52. Title: Kernel uniqueness of the range operator (node STR029, size M,
leaf formalization, verification level V1, dispatch tier 6, no prerequisites inside the frontier).

Statement (specification): if a periodic `C^2` function `w` satisfies `w'' + w = 0` and is
orthogonal to `cos t` and `sin t`, then `w = 0`.

Proof route (specification): the functions `w cos t - w' sin t` and `w sin t + w' cos t` have
derivative zero, hence are constant, with values `A` and `B`. Then `w = A cos t + B sin t`.
The orthogonality relations give `A / 2 = 0` and `B / 2 = 0`, because the normalized integrals of
`cos t ^ 2` and `sin t ^ 2` over one period are `1 / 2` and the normalized integral of
`sin t cos t` vanishes.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_52_kernel_uniqueness_range_operator`: the main theorem. A
  `2π`-periodic `C^2` function `w : ℝ → ℝ` with `w'' + w = 0` pointwise and normalized
  orthogonality `∫ w cos dm = 0`, `∫ w sin dm = 0` is the zero function.
* `DGPS.Frontier.STR029.mInt_STR02952`: the normalized integral `∫ f dm = (2π)⁻¹ ∫_0^{2π} f`.
* `DGPS.Frontier.STR029.firstConst_STR02952`: the first constant of motion
  `t ↦ w t cos t - w' t sin t`.
* `DGPS.Frontier.STR029.secondConst_STR02952`: the second constant of motion
  `t ↦ w t sin t + w' t cos t`.
* `DGPS.Frontier.STR029.firstConst_hasDerivAt_STR02952`: the first constant of motion has
  derivative zero everywhere when `w'' + w = 0`.
* `DGPS.Frontier.STR029.secondConst_hasDerivAt_STR02952`: the same for the second constant.
* `DGPS.Frontier.STR029.firstConst_eq_STR02952`, `DGPS.Frontier.STR029.secondConst_eq_STR02952`:
  both constants of motion are constant on the real line.
* `DGPS.Frontier.STR029.w_eq_STR02952`: `w t = A cos t + B sin t` with the two constant values.

R5 notes:
* Carrier: `w : ℝ → ℝ` is a function of the real variable `t` (the specification's `t = 2πx`),
  `2π`-periodic (`Function.Periodic w (2 * π)`) and `C^2` on the whole line (`ContDiff ℝ 2 w`).
  This is the concrete carrier the brief fixes for analytic tasks; the identification with the
  packet carriers is the business of STR029.01, not of this task.
* `w'' + w = 0` is read pointwise for every `t`, with `w''` written `deriv (deriv w) t`.
* Orthogonality is read as `∫ w cos dm = 0` and `∫ w sin dm = 0` for the normalized measure
  `m(dt) = dt/(2π)` over one period `[0, 2π]`. The factor `(2π)⁻¹` does not affect vanishing; it
  is kept so that `mInt_STR02952` is the normalized integral of the specification.
* The periodicity hypothesis is part of the specification and is kept. The proof does not need it,
  because the integrals are taken over one full period by definition.
* The conclusion `w = 0` is an equality of functions on `ℝ`; it is equivalent to `w = 0` on the
  circle `ℝ / 2πℤ`.
* No Hölder norm, `H^1` space, entropy, Fisher information, range map of the Euler equation, or
  variational range map enters. The statement concerns only the kernel of `w ↦ w'' + w` on the
  concrete carrier, as the specification states it.
* Library facts (verified by compilation at the pin, not assumed): `is_const_of_deriv_eq_zero`
  (derivative-zero implies constancy on `ℝ`), `ContDiff.differentiable_deriv_two` (the derivative of a
  `C^2` function is differentiable), and the trigonometric integrals `integral_cos_sq`,
  `integral_sin_sq`, `integral_sin_mul_cos₁`.
-/

namespace DGPS.Frontier.STR029

open Real

/-- The normalized integral `∫ f dm` with `m(dt) = dt/(2π)`, over one period `[0, 2π]`. -/
noncomputable def mInt_STR02952 (f : ℝ → ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), f t

/-- The first constant of motion `t ↦ w t * cos t - w' t * sin t`. -/
noncomputable def firstConst_STR02952 (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t * Real.cos t - deriv w t * Real.sin t

/-- The second constant of motion `t ↦ w t * sin t + w' t * cos t`. -/
noncomputable def secondConst_STR02952 (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t * Real.sin t + deriv w t * Real.cos t

/-- For a `C^2` function with `w'' + w = 0`, the first constant of motion has derivative zero. -/
theorem firstConst_hasDerivAt_STR02952 {w : ℝ → ℝ} (hC2 : ContDiff ℝ 2 w)
    (hker : ∀ t, deriv (deriv w) t + w t = 0) (t : ℝ) :
    HasDerivAt (firstConst_STR02952 w) 0 t := by
  have hw : HasDerivAt w (deriv w t) t := (hC2.differentiable (by norm_num) t).hasDerivAt
  have hw' : HasDerivAt (deriv w) (deriv (deriv w) t) t :=
    (hC2.differentiable_deriv_two t).hasDerivAt
  have h := (hw.mul (Real.hasDerivAt_cos t)).sub (hw'.mul (Real.hasDerivAt_sin t))
  unfold firstConst_STR02952
  convert h using 1
  linear_combination Real.sin t * hker t

/-- For a `C^2` function with `w'' + w = 0`, the second constant of motion has derivative zero. -/
theorem secondConst_hasDerivAt_STR02952 {w : ℝ → ℝ} (hC2 : ContDiff ℝ 2 w)
    (hker : ∀ t, deriv (deriv w) t + w t = 0) (t : ℝ) :
    HasDerivAt (secondConst_STR02952 w) 0 t := by
  have hw : HasDerivAt w (deriv w t) t := (hC2.differentiable (by norm_num) t).hasDerivAt
  have hw' : HasDerivAt (deriv w) (deriv (deriv w) t) t :=
    (hC2.differentiable_deriv_two t).hasDerivAt
  have h := (hw.mul (Real.hasDerivAt_sin t)).add (hw'.mul (Real.hasDerivAt_cos t))
  unfold secondConst_STR02952
  convert h using 1
  linear_combination (-Real.cos t) * hker t

/-- The first constant of motion is constant on `ℝ`. -/
theorem firstConst_eq_STR02952 {w : ℝ → ℝ} (hC2 : ContDiff ℝ 2 w)
    (hker : ∀ t, deriv (deriv w) t + w t = 0) (t : ℝ) :
    firstConst_STR02952 w t = firstConst_STR02952 w 0 :=
  is_const_of_deriv_eq_zero
    (fun s => (firstConst_hasDerivAt_STR02952 hC2 hker s).differentiableAt)
    (fun s => (firstConst_hasDerivAt_STR02952 hC2 hker s).deriv) t 0

/-- The second constant of motion is constant on `ℝ`. -/
theorem secondConst_eq_STR02952 {w : ℝ → ℝ} (hC2 : ContDiff ℝ 2 w)
    (hker : ∀ t, deriv (deriv w) t + w t = 0) (t : ℝ) :
    secondConst_STR02952 w t = secondConst_STR02952 w 0 :=
  is_const_of_deriv_eq_zero
    (fun s => (secondConst_hasDerivAt_STR02952 hC2 hker s).differentiableAt)
    (fun s => (secondConst_hasDerivAt_STR02952 hC2 hker s).deriv) t 0

/-- The solution has the form `w t = A cos t + B sin t` with the constant values `A, B` of the
two constants of motion, read at `0`. -/
theorem w_eq_STR02952 {w : ℝ → ℝ} (hC2 : ContDiff ℝ 2 w)
    (hker : ∀ t, deriv (deriv w) t + w t = 0) (t : ℝ) :
    w t = firstConst_STR02952 w 0 * Real.cos t + secondConst_STR02952 w 0 * Real.sin t := by
  have key : w t = firstConst_STR02952 w t * Real.cos t
      + secondConst_STR02952 w t * Real.sin t := by
    unfold firstConst_STR02952 secondConst_STR02952
    linear_combination (-w t) * Real.sin_sq_add_cos_sq t
  rw [firstConst_eq_STR02952 hC2 hker t, secondConst_eq_STR02952 hC2 hker t] at key
  exact key

/-- Kernel uniqueness of the range operator. A `2π`-periodic `C^2` function `w` with
`w'' + w = 0` and `∫ w cos dm = 0`, `∫ w sin dm = 0` (normalized integrals) is the zero function. -/
theorem str029_52_kernel_uniqueness_range_operator (w : ℝ → ℝ)
    (hC2 : ContDiff ℝ 2 w) (_hper : Function.Periodic w (2 * π))
    (hker : ∀ t, deriv (deriv w) t + w t = 0)
    (hcos : mInt_STR02952 (fun t => w t * Real.cos t) = 0)
    (hsin : mInt_STR02952 (fun t => w t * Real.sin t) = 0) :
    w = 0 := by
  have hw := w_eq_STR02952 hC2 hker
  set a := firstConst_STR02952 w 0 with ha
  set b := secondConst_STR02952 w 0 with hb
  have hcs : (fun t => w t * Real.cos t)
      = fun t => a * Real.cos t ^ 2 + b * (Real.sin t * Real.cos t) := by
    funext t
    rw [hw t]
    ring
  have hsn : (fun t => w t * Real.sin t)
      = fun t => a * (Real.sin t * Real.cos t) + b * Real.sin t ^ 2 := by
    funext t
    rw [hw t]
    ring
  have c1 : Continuous fun t : ℝ => a * Real.cos t ^ 2 := by fun_prop
  have c2 : Continuous fun t : ℝ => b * (Real.sin t * Real.cos t) := by fun_prop
  have c3 : Continuous fun t : ℝ => a * (Real.sin t * Real.cos t) := by fun_prop
  have c4 : Continuous fun t : ℝ => b * Real.sin t ^ 2 := by fun_prop
  have hIc : ∫ t in (0 : ℝ)..(2 * π), w t * Real.cos t = a * π := by
    rw [hcs, intervalIntegral.integral_add (c1.intervalIntegrable _ _)
      (c2.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_mul_cos₁]
    simp
  have hIs : ∫ t in (0 : ℝ)..(2 * π), w t * Real.sin t = b * π := by
    rw [hsn, intervalIntegral.integral_add (c3.intervalIntegrable _ _)
      (c4.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_sin_mul_cos₁, integral_sin_sq]
    simp
  have hpi : (2 * π)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  have ha0 : a = 0 := by
    have hc' : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), w t * Real.cos t = 0 := hcos
    rw [hIc] at hc'
    have h2 : a * π = 0 := (mul_eq_zero.mp hc').resolve_left hpi
    exact (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
  have hb0 : b = 0 := by
    have hs' : (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), w t * Real.sin t = 0 := hsin
    rw [hIs] at hs'
    have h2 : b * π = 0 := (mul_eq_zero.mp hs').resolve_left hpi
    exact (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
  funext t
  rw [hw t, ha0, hb0]
  simp

end DGPS.Frontier.STR029
