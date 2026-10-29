import DGPS.Frontier.EX012.T16
import DGPS.Frontier.EX012.T17

/-!
# EX012.19: Kinetic and potential first variations

Task id: EX012.19 (node EX012, leaf formalization).
Title: Kinetic and potential first variations.

For an admissible `u` (`IsAdmSmooth_EX01236`), a smooth one-periodic `ξ`, the normalized variation
`u_t = (u + tξ)/N_t` of EX012.16 (`ucurve_EX01216`), `η = ξ - u ∫ uξ` (`eta_EX01216`), `D = (2π)⁻¹ ∂ₓ`
(`angD_EX01217`), `s₁(x) = sin(2πx)` and a real `τ`, the function
`t ↦ 4 ∫₀¹ (D u_t)² + τ ∫₀¹ s₁² u_t²` has derivative at `t = 0`
`8 ∫₀¹ D u D η + 2 τ ∫₀¹ s₁² u η`.

## Provides

* `DGPS.Frontier.EX012.ex012_19_kinetic_potential_first_variations`: the `HasDerivAt` statement
  above, at `t = 0`.
* `DGPS.Frontier.EX012.ex012_19_kinetic_potential_first_variations_deriv`: the same statement as
  an equation for `deriv` of the same function at `0`.
* Helpers (suffix `_EX01219`): `angD_ucurve_EX01219` (`D u_t = (Du + tDξ)/N_t`),
  `kinetic_integral_EX01219` (`∫ (D u_t)² = ∫ (Du + tDξ)² / ∫ v_t²`),
  `potential_integral_EX01219` (`∫ s₁² u_t² = ∫ (s₁u + t s₁ξ)² / ∫ v_t²`),
  `hasDerivAt_quotient_EX01219` (derivative at `0` of a quadratic over a quadratic with constant
  term `1`), `angD_eta_EX01219` (`D η = Dξ - (∫ uξ) Du`), and `continuous_*_EX01219` lemmas.

## R5 notes

* Hypotheses are exactly those of EX012.16 and EX012.17: `u` admissible (smooth, one-periodic,
  positive, `∫ u² = 1`), `ξ` smooth (`ContDiff ℝ ∞`) and one-periodic, `τ : ℝ` arbitrary. No
  constants `m, M, Q` are needed in the statement.
* `hξp` (periodicity of `ξ`) is carried because EX012.16 and the specification list it, but the
  proof never uses it: the kinetic and potential integrals are over the fixed interval `[0,1]` and
  the closed forms hold without periodicity (it is kept in the signature, bound by `have _hp`).
* `s₁² u_t²` is written `Real.sin (2 * π * x) ^ 2 * ucurve_EX01216 u ξ t x ^ 2`, `s₁² u η` as
  `Real.sin (2 * π * x) ^ 2 * u x * eta_EX01216 u ξ x`; the Haar integral is the interval integral
  over `[0,1]`, as in EX012.16/17.
* The derivative `(d/dt)|₀` is `HasDerivAt` of the real function of `t` at `0` (that function is
  defined for every `t`; only a neighbourhood of `0` matters).
* Proof route (non-literal with respect to the specification's proof sketch): the specification
  differentiates under the integral sign with constant dominators. Here, because `N_t` does not
  depend on the spatial variable, `∫ (D u_t)²` and `∫ s₁² u_t²` are computed exactly as
  quadratic polynomials in `t` divided by the quadratic `∫ v_t²`, so no differentiation under the
  integral sign, no dominators and no EX012.18 bounds are needed. The identification of the
  derivative with the Euler expression `8∫Du Dη + 2τ∫s₁²uη` is by linearity of `D`; EX012.17
  (integration by parts) is not used beyond the shared definition `angD_EX01217` and its
  smoothness/periodicity lemmas.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX012

theorem hasDerivAt_quotient_EX01219 (a b c e f : ℝ) :
    HasDerivAt (fun t : ℝ => (a + 2 * t * b + t ^ 2 * c) / (1 + 2 * t * e + t ^ 2 * f))
      (2 * b - 2 * a * e) 0 := by
  have hn : HasDerivAt (fun t : ℝ => a + 2 * t * b + t ^ 2 * c) (2 * b) 0 := by
    have h1 := (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const b).const_add a
    have h2 := (hasDerivAt_pow 2 (0:ℝ)).mul_const c
    refine HasDerivAt.congr_deriv (h1.add h2) ?_
    simp
  have hd : HasDerivAt (fun t : ℝ => 1 + 2 * t * e + t ^ 2 * f) (2 * e) 0 := by
    have h1 := (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const e).const_add 1
    have h2 := (hasDerivAt_pow 2 (0:ℝ)).mul_const f
    refine HasDerivAt.congr_deriv (h1.add h2) ?_
    simp
  have h0 : (1 + 2 * (0:ℝ) * e + (0:ℝ) ^ 2 * f) ≠ 0 := by simp
  refine HasDerivAt.congr_deriv (hn.div hd h0) ?_
  simp
  ring

theorem angD_ucurve_EX01219 {u ξ : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hξ : ContDiff ℝ ∞ ξ) (t x : ℝ) :
    angD_EX01217 (ucurve_EX01216 u ξ t) x
      = vcurve_EX01216 (angD_EX01217 u) (angD_EX01217 ξ) t x / normCurve_EX01216 u ξ t := by
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  have hξd : Differentiable ℝ ξ := hξ.differentiable (by simp)
  have h := (((hud x).hasDerivAt).add (((hξd x).hasDerivAt).const_mul t)).div_const
    (normCurve_EX01216 u ξ t)
  have e : ucurve_EX01216 u ξ t
      = fun y => (u y + t * ξ y) / normCurve_EX01216 u ξ t := rfl
  have hd : deriv (fun y => (u y + t * ξ y) / normCurve_EX01216 u ξ t) x
      = (deriv u x + t * deriv ξ x) / normCurve_EX01216 u ξ t := h.deriv
  rw [angD_EX01217_apply, e, hd]
  simp only [vcurve_EX01216, angD_EX01217_apply]
  ring

theorem massSq_nonneg_EX01219 (u ξ : ℝ → ℝ) (t : ℝ) : 0 ≤ massSq_EX01216 u ξ t := by
  unfold massSq_EX01216
  exact intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg _)

theorem kinetic_integral_EX01219 {u ξ : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hξ : ContDiff ℝ ∞ ξ)
    (t : ℝ) :
    ∫ x in (0:ℝ)..1, angD_EX01217 (ucurve_EX01216 u ξ t) x ^ 2
      = massSq_EX01216 (angD_EX01217 u) (angD_EX01217 ξ) t / massSq_EX01216 u ξ t := by
  have hS := massSq_nonneg_EX01219 u ξ t
  have e : ∀ x, angD_EX01217 (ucurve_EX01216 u ξ t) x ^ 2
      = vcurve_EX01216 (angD_EX01217 u) (angD_EX01217 ξ) t x ^ 2 / massSq_EX01216 u ξ t := by
    intro x
    rw [angD_ucurve_EX01219 hu hξ, div_pow]
    unfold normCurve_EX01216
    rw [Real.sq_sqrt hS]
  simp_rw [e]
  rw [intervalIntegral.integral_div]
  rfl

theorem potential_integral_EX01219 {u ξ : ℝ → ℝ} (t : ℝ) :
    ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * ucurve_EX01216 u ξ t x ^ 2
      = massSq_EX01216 (fun x => Real.sin (2 * Real.pi * x) * u x)
          (fun x => Real.sin (2 * Real.pi * x) * ξ x) t / massSq_EX01216 u ξ t := by
  have hS := massSq_nonneg_EX01219 u ξ t
  have e : ∀ x, Real.sin (2 * Real.pi * x) ^ 2 * ucurve_EX01216 u ξ t x ^ 2
      = vcurve_EX01216 (fun x => Real.sin (2 * Real.pi * x) * u x)
          (fun x => Real.sin (2 * Real.pi * x) * ξ x) t x ^ 2 / massSq_EX01216 u ξ t := by
    intro x
    unfold ucurve_EX01216 normCurve_EX01216 vcurve_EX01216
    rw [div_pow, Real.sq_sqrt hS]
    beta_reduce
    field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_div]
  rfl

theorem angD_eta_EX01219 {u ξ : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hξ : ContDiff ℝ ∞ ξ) (x : ℝ) :
    angD_EX01217 (eta_EX01216 u ξ) x
      = angD_EX01217 ξ x - (∫ y in (0:ℝ)..1, u y * ξ y) * angD_EX01217 u x := by
  have hud : Differentiable ℝ u := hu.differentiable (by simp)
  have hξd : Differentiable ℝ ξ := hξ.differentiable (by simp)
  have h := ((hξd x).hasDerivAt).sub (((hud x).hasDerivAt).mul_const (∫ y in (0:ℝ)..1, u y * ξ y))
  have e : eta_EX01216 u ξ = fun y => ξ y - u y * ∫ y in (0:ℝ)..1, u y * ξ y := rfl
  have hd : deriv (fun y => ξ y - u y * ∫ y in (0:ℝ)..1, u y * ξ y) x
      = deriv ξ x - deriv u x * ∫ y in (0:ℝ)..1, u y * ξ y := h.deriv
  rw [angD_EX01217_apply, e, hd]
  simp only [angD_EX01217_apply]
  ring

theorem ex012_19_kinetic_potential_first_variations {u ξ : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u) (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1) (τ : ℝ) :
    HasDerivAt
      (fun t : ℝ => 4 * (∫ x in (0:ℝ)..1, angD_EX01217 (ucurve_EX01216 u ξ t) x ^ 2)
        + τ * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * ucurve_EX01216 u ξ t x ^ 2)
      (8 * (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 (eta_EX01216 u ξ) x)
        + 2 * τ * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * u x * eta_EX01216 u ξ x) 0 := by
  have _hp := hξp
  have hus := hu.smooth
  have huc : Continuous u := hus.continuous
  have hξc : Continuous ξ := hξ.continuous
  have hDu : Continuous (angD_EX01217 u) := (contDiff_angD_EX01217 hus).continuous
  have hDξ : Continuous (angD_EX01217 ξ) := (contDiff_angD_EX01217 hξ).continuous
  have hsc : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x) := by fun_prop
  have hsu : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x) * u x := hsc.mul huc
  have hsξ : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x) * ξ x := hsc.mul hξc
  -- closed form of the function of `t`
  have hfun : (fun t : ℝ => 4 * (∫ x in (0:ℝ)..1, angD_EX01217 (ucurve_EX01216 u ξ t) x ^ 2)
        + τ * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * ucurve_EX01216 u ξ t x ^ 2)
      = fun t : ℝ =>
        4 * (((∫ x in (0:ℝ)..1, angD_EX01217 u x ^ 2)
            + 2 * t * (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 ξ x)
            + t ^ 2 * ∫ x in (0:ℝ)..1, angD_EX01217 ξ x ^ 2)
          / (1 + 2 * t * (∫ x in (0:ℝ)..1, u x * ξ x) + t ^ 2 * ∫ x in (0:ℝ)..1, ξ x ^ 2))
        + τ * (((∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * u x) ^ 2)
            + 2 * t * (∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * u x)
              * (Real.sin (2 * Real.pi * x) * ξ x))
            + t ^ 2 * ∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * ξ x) ^ 2)
          / (1 + 2 * t * (∫ x in (0:ℝ)..1, u x * ξ x) + t ^ 2 * ∫ x in (0:ℝ)..1, ξ x ^ 2)) := by
    funext t
    rw [kinetic_integral_EX01219 hus hξ, potential_integral_EX01219,
      massSq_expand_EX01216 hDu hDξ, massSq_expand_EX01216 hsu hsξ,
      massSq_expand_EX01216 huc hξc, hu.mass]
  rw [hfun]
  have hK := hasDerivAt_quotient_EX01219 (∫ x in (0:ℝ)..1, angD_EX01217 u x ^ 2)
    (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 ξ x)
    (∫ x in (0:ℝ)..1, angD_EX01217 ξ x ^ 2) (∫ x in (0:ℝ)..1, u x * ξ x)
    (∫ x in (0:ℝ)..1, ξ x ^ 2)
  have hP := hasDerivAt_quotient_EX01219 (∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * u x) ^ 2)
    (∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * u x) * (Real.sin (2 * Real.pi * x) * ξ x))
    (∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * ξ x) ^ 2) (∫ x in (0:ℝ)..1, u x * ξ x)
    (∫ x in (0:ℝ)..1, ξ x ^ 2)
  have hK' := hK.const_mul 4
  have hP' := hP.const_mul τ
  have hT := hK'.add hP'
  -- value of the derivative
  have i1 : (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 (eta_EX01216 u ξ) x)
      = (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 ξ x)
        - (∫ x in (0:ℝ)..1, u x * ξ x) * ∫ x in (0:ℝ)..1, angD_EX01217 u x ^ 2 := by
    have e : ∀ x, angD_EX01217 u x * angD_EX01217 (eta_EX01216 u ξ) x
        = angD_EX01217 u x * angD_EX01217 ξ x
          - (∫ y in (0:ℝ)..1, u y * ξ y) * angD_EX01217 u x ^ 2 := by
      intro x
      rw [angD_eta_EX01219 hus hξ]
      ring
    simp_rw [e]
    have h1 : IntervalIntegrable (fun x => angD_EX01217 u x * angD_EX01217 ξ x)
        MeasureTheory.volume 0 1 := (hDu.mul hDξ).intervalIntegrable _ _
    have h2 : IntervalIntegrable
        (fun x => (∫ y in (0:ℝ)..1, u y * ξ y) * angD_EX01217 u x ^ 2)
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hDu.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  have i2 : (∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * u x * eta_EX01216 u ξ x)
      = (∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * u x) * (Real.sin (2 * Real.pi * x) * ξ x))
        - (∫ x in (0:ℝ)..1, u x * ξ x)
          * ∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) * u x) ^ 2 := by
    have e : ∀ x, Real.sin (2 * Real.pi * x) ^ 2 * u x * eta_EX01216 u ξ x
        = (Real.sin (2 * Real.pi * x) * u x) * (Real.sin (2 * Real.pi * x) * ξ x)
          - (∫ y in (0:ℝ)..1, u y * ξ y) * (Real.sin (2 * Real.pi * x) * u x) ^ 2 := by
      intro x
      unfold eta_EX01216
      ring
    simp_rw [e]
    have h1 : IntervalIntegrable
        (fun x => (Real.sin (2 * Real.pi * x) * u x) * (Real.sin (2 * Real.pi * x) * ξ x))
        MeasureTheory.volume 0 1 := (hsu.mul hsξ).intervalIntegrable _ _
    have h2 : IntervalIntegrable
        (fun x => (∫ y in (0:ℝ)..1, u y * ξ y) * (Real.sin (2 * Real.pi * x) * u x) ^ 2)
        MeasureTheory.volume 0 1 :=
      (continuous_const.mul (hsu.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  rw [i1, i2]
  refine HasDerivAt.congr_deriv hT ?_
  ring

theorem ex012_19_kinetic_potential_first_variations_deriv {u ξ : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u) (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1) (τ : ℝ) :
    deriv
      (fun t : ℝ => 4 * (∫ x in (0:ℝ)..1, angD_EX01217 (ucurve_EX01216 u ξ t) x ^ 2)
        + τ * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * ucurve_EX01216 u ξ t x ^ 2) 0
      = 8 * (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 (eta_EX01216 u ξ) x)
        + 2 * τ * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * u x * eta_EX01216 u ξ x :=
  (ex012_19_kinetic_potential_first_variations hu hξ hξp τ).deriv

end DGPS.Frontier.EX012
