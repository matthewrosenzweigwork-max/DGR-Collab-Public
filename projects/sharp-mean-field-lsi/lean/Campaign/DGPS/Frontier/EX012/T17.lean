import Mathlib

/-!
# EX012.17: Periodic angular integration by parts

Task id: EX012.17 (node EX012, one-site complementary range equation).
Title: Periodic angular integration by parts.

Provides:
* `DGPS.Frontier.EX012.angD_EX01217`: the angular derivative `D f = (2π)⁻¹ • deriv f`
  as a function `ℝ → ℝ`.
* `DGPS.Frontier.EX012.ex012_17_periodic_angular_integration_parts`: for smooth one-periodic
  real `f g`, `∫ x in 0..1, D f x = 0` and
  `∫ x in 0..1, D f x * D g x = -∫ x in 0..1, D (D f) x * g x`, with `D = (2π)⁻¹ ∂ₓ`.
* `DGPS.Frontier.EX012.ex012_17_periodic_angular_integration_parts_mean_zero`: the first
  conjunct on its own.
* `DGPS.Frontier.EX012.ex012_17_periodic_angular_integration_parts_by_parts`: the second
  conjunct on its own.
* Helpers (public, suffix `_EX01217`): `angD_EX01217_apply` (pointwise formula),
  `hasDerivAt_angD_EX01217` (`D f` has derivative `2π * D² f`), `contDiff_angD_EX01217`
  (`D f` is smooth), `periodic_angD_EX01217` (`D f` is one-periodic).

R5 notes:
* Hypotheses are exactly those of the specification: `f` and `g` are smooth (`ContDiff ℝ ∞`)
  and one-periodic (`Function.Periodic _ 1`); there are no other hypotheses.
* "Smooth" is read as `ContDiff ℝ ∞` (infinitely differentiable; `∞` is the `C^∞` index of
  `ℕ∞ω`, not the analytic index `ω`, so the hypothesis is the weaker, literal one); only `C^2` for `f` and `C^1` for `g` is used, via
  `ContDiff.of_le`.
* `D = (2π)⁻¹ ∂ₓ` is read as `angD_EX01217 f = (2 * π)⁻¹ • deriv f`, with `x` the unit-period
  variable; `D²f` is `angD_EX01217 (angD_EX01217 f)`. The angular factors are kept explicitly.
* "Integrals run from 0 to 1" is read as the interval integral `∫ x in (0:ℝ)..1`, which for
  `0 ≤ 1` is the Lebesgue integral over `[0,1]` (Haar measure of the circle).
* The domain is all of `ℝ` (periodic functions), not a quotient circle.
-/

open intervalIntegral
open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- The angular derivative `D f = (2π)⁻¹ ∂ₓ f` as a function. -/
noncomputable def angD_EX01217 (f : ℝ → ℝ) : ℝ → ℝ := (2 * Real.pi)⁻¹ • deriv f

theorem angD_EX01217_apply (f : ℝ → ℝ) (x : ℝ) :
    angD_EX01217 f x = (2 * Real.pi)⁻¹ * deriv f x := rfl

theorem hasDerivAt_angD_EX01217 {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    HasDerivAt (angD_EX01217 f) ((2 * Real.pi) * angD_EX01217 (angD_EX01217 f) x) x := by
  have hd : Differentiable ℝ (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)
  have := ((hd x).hasDerivAt).const_mul (2 * Real.pi)⁻¹
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [angD_EX01217_apply]
  convert this using 1
  · ext y; rfl
  · have hD : deriv (angD_EX01217 f) x = (2 * Real.pi)⁻¹ * deriv (deriv f) x := this.deriv
    rw [hD]
    field_simp

theorem contDiff_angD_EX01217 {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (angD_EX01217 f) :=
  (((contDiff_infty_iff_deriv.mp hf).2).const_smul (2 * Real.pi)⁻¹ :)

theorem periodic_angD_EX01217 {f : ℝ → ℝ} (hf : Function.Periodic f 1) :
    Function.Periodic (angD_EX01217 f) 1 := fun x => by
  simp only [angD_EX01217_apply]
  have h : deriv (fun y => f (y + 1)) x = deriv f (x + 1) := deriv_comp_add_const (f := f) (a := 1) (x := x)
  have h' : (fun y => f (y + 1)) = f := funext hf
  rw [h'] at h
  rw [h]

/-- The mean of the angular derivative of a one-periodic smooth function is zero. -/
theorem ex012_17_periodic_angular_integration_parts_mean_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfp : Function.Periodic f 1) :
    ∫ x in (0:ℝ)..1, angD_EX01217 f x = 0 := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt f (deriv f x) x := fun x _ =>
    (hf.differentiable (by simp) x).hasDerivAt
  have hint : IntervalIntegrable (deriv f) MeasureTheory.volume 0 1 :=
    ((contDiff_infty_iff_deriv.mp hf).2.continuous).intervalIntegrable _ _
  have h := integral_eq_sub_of_hasDerivAt hd hint
  have h1 : f 1 = f 0 := by simpa using hfp 0
  simp only [angD_EX01217_apply]
  rw [intervalIntegral.integral_const_mul, h, h1, sub_self, mul_zero]

/-- Periodic angular integration by parts. -/
theorem ex012_17_periodic_angular_integration_parts_by_parts {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f 1) (hgp : Function.Periodic g 1) :
    ∫ x in (0:ℝ)..1, angD_EX01217 f x * angD_EX01217 g x
      = -∫ x in (0:ℝ)..1, angD_EX01217 (angD_EX01217 f) x * g x := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hDf := contDiff_angD_EX01217 hf
  have hDDf := contDiff_angD_EX01217 hDf
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y => angD_EX01217 f y * g y)
        ((2 * Real.pi) * (angD_EX01217 (angD_EX01217 f) x * g x
          + angD_EX01217 f x * angD_EX01217 g x)) x := by
    intro x _
    have h1 := hasDerivAt_angD_EX01217 hf x
    have h2 : HasDerivAt g ((2 * Real.pi) * angD_EX01217 g x) x := by
      have := (hg.differentiable (by simp) x).hasDerivAt
      simp only [angD_EX01217_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
      exact this
    convert h1.mul h2 using 1
    ring
  have hint : IntervalIntegrable
      (fun x => (2 * Real.pi) * (angD_EX01217 (angD_EX01217 f) x * g x
          + angD_EX01217 f x * angD_EX01217 g x)) MeasureTheory.volume 0 1 := by
    have : Continuous (fun x => (2 * Real.pi) * (angD_EX01217 (angD_EX01217 f) x * g x
          + angD_EX01217 f x * angD_EX01217 g x)) := by
      have := hDDf.continuous
      have := hDf.continuous
      have := hg.continuous
      have := (contDiff_angD_EX01217 hg).continuous
      fun_prop
    exact this.intervalIntegrable _ _
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  have hz : (angD_EX01217 f 1 * g 1) - (angD_EX01217 f 0 * g 0) = 0 := by
    have e1 : angD_EX01217 f 1 = angD_EX01217 f 0 := by
      simpa using (periodic_angD_EX01217 hfp) 0
    have e2 : g 1 = g 0 := by simpa using hgp 0
    rw [e1, e2, sub_self]
  rw [hz, intervalIntegral.integral_const_mul, mul_eq_zero] at h
  have h0 := h.resolve_left hpi
  rw [intervalIntegral.integral_add] at h0
  · linarith
  · exact (hDDf.continuous.mul hg.continuous).intervalIntegrable _ _
  · exact (hDf.continuous.mul (contDiff_angD_EX01217 hg).continuous).intervalIntegrable _ _

/-- Periodic angular integration by parts: for smooth one-periodic `f g`,
`∫₀¹ D f = 0` and `∫₀¹ D f * D g = -∫₀¹ D² f * g`, with `D = (2π)⁻¹ ∂ₓ`. -/
theorem ex012_17_periodic_angular_integration_parts {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f 1) (hgp : Function.Periodic g 1) :
    (∫ x in (0:ℝ)..1, angD_EX01217 f x = 0) ∧
    (∫ x in (0:ℝ)..1, angD_EX01217 f x * angD_EX01217 g x
      = -∫ x in (0:ℝ)..1, angD_EX01217 (angD_EX01217 f) x * g x) :=
  ⟨ex012_17_periodic_angular_integration_parts_mean_zero hf hfp,
   ex012_17_periodic_angular_integration_parts_by_parts hf hg hfp hgp⟩

end DGPS.Frontier.EX012
