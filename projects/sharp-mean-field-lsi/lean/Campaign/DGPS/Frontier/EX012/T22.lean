import DGPS.Frontier.EX012.T17

/-!
# EX012.22: Determine that constant by integration

Task id: EX012.22 (node EX012, leaf formalization).
Title: Determine that constant by integration.

For a smooth one-periodic mean-zero `v`, integrating the identity of EX012.21,
`D²v + v + (Dv)²/2 + (τ/4) c₂ = K` with a real constant `K`, over the period cell gives
`K = (1/2) ∫ (Dv)²`. Substituting this constant, the Euler residual
`R(v,τ) = D²v + v + (1/2)((Dv)² - ∫(Dv)²) + (τ/4) c₂` vanishes pointwise.

Provides:
* `DGPS.Frontier.EX012.eulerR_EX01222`: the residual `R(v,τ)` as a function `ℝ → ℝ`.
* `DGPS.Frontier.EX012.ex012_22_determine_constant_integration`: main statement. Under the
  hypotheses of the specification, `K = (1/2) ∫₀¹ (Dv)²`, and `R(v,τ) x = 0` for every `x`.
* `DGPS.Frontier.EX012.ex012_22_determine_constant_integration_exists`: the same conclusion
  with the constant supplied as `∃ K`, the form in which EX012.21 delivers it.
* Helpers (suffix `_EX01222`): `int_cos_two_EX01222` (`∫₀¹ cos(2π·2x) dx = 0`) and
  `int_angD_angD_EX01222` (`∫₀¹ D²v = 0` for smooth one-periodic `v`).

R5 notes:
* `D = (2π)⁻¹ ∂ₓ` is `angD_EX01217` from EX012.17, and `D²v` is `angD_EX01217 (angD_EX01217 v)`.
  `c₂(x) = cos(2π · 2 · x)`, the same convention as EX012.21 (`θ = 2πx`).
* Hypotheses: `v` is smooth (`ContDiff ℝ ∞`) and one-periodic (`Function.Periodic v 1`),
  matching EX012.17 and the smooth setting of the identity in EX012.21. The specification's
  "mean-zero periodic `v`" is read as the zero interval integral `∫ x in (0:ℝ)..1, v x = 0`.
  Smoothness is a substantive choice: the specification states no regularity for `v` here, and
  the identity it integrates (EX012.21) is proved only for smooth functions. The frozen
  `C^{2,α}` setting is not used.
* The identity of EX012.21 enters as the hypothesis `hK`, a pointwise equation with an explicit
  real constant `K`. The main statement's `K` is determined by the hypotheses; the
  `_exists` variant takes `∃ K` instead. Neither assumes the value of `K`.
* `τ` is an arbitrary real parameter. The specification sets `τ = h²`; the argument uses no sign
  condition, so the statement holds for all real `τ`, and `τ = h²` is an instance.
* Integrals are interval integrals over `[0,1]`, the Haar integral of the period cell. The
  domain is all of `ℝ`, not a quotient circle.
* The conclusion `K = (1/2) ∫ (Dv)²` and `R(v,τ) = 0` are both proved. No integrability
  hypothesis is needed: all integrands are continuous, since `v` is smooth.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- The Euler residual `R(v,τ) = D²v + v + (1/2)((Dv)² - ∫₀¹(Dv)²) + (τ/4) cos(2π·2x)`. -/
noncomputable def eulerR_EX01222 (τ : ℝ) (v : ℝ → ℝ) : ℝ → ℝ :=
  fun x => angD_EX01217 (angD_EX01217 v) x + v x
    + (1 / 2 : ℝ) * ((angD_EX01217 v x) ^ 2 - ∫ t in (0:ℝ)..1, (angD_EX01217 v t) ^ 2)
    + (τ / 4) * Real.cos (2 * Real.pi * 2 * x)

theorem int_cos_two_EX01222 :
    ∫ x in (0:ℝ)..1, Real.cos (2 * Real.pi * 2 * x) = 0 := by
  have hc : (2 * Real.pi * 2) ≠ 0 := by positivity
  have hF : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y => Real.sin (2 * Real.pi * 2 * y) / (2 * Real.pi * 2))
        (Real.cos (2 * Real.pi * 2 * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => 2 * Real.pi * 2 * y) (2 * Real.pi * 2) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * 2)
    have h2 := (h1.sin).div_const (2 * Real.pi * 2)
    convert h2 using 1
    field_simp
  have hint : IntervalIntegrable (fun x => Real.cos (2 * Real.pi * 2 * x))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => Real.cos (2 * Real.pi * 2 * x)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  have e1 : Real.sin (2 * Real.pi * 2 * 1) = 0 := by
    have : 2 * Real.pi * 2 * (1:ℝ) = ((4:ℕ):ℝ) * Real.pi := by push_cast; ring
    rw [this, Real.sin_nat_mul_pi]
  show Real.sin (2 * Real.pi * 2 * 1) / (2 * Real.pi * 2)
      - Real.sin (2 * Real.pi * 2 * 0) / (2 * Real.pi * 2) = 0
  rw [e1]
  simp

theorem int_angD_angD_EX01222 {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hp : Function.Periodic v 1) :
    ∫ x in (0:ℝ)..1, angD_EX01217 (angD_EX01217 v) x = 0 :=
  ex012_17_periodic_angular_integration_parts_mean_zero
    (contDiff_angD_EX01217 hv) (periodic_angD_EX01217 hp)

/-- Determine the constant by integration: if `D²v + v + (Dv)²/2 + (τ/4) c₂ = K` pointwise for a
smooth one-periodic mean-zero `v`, then `K = (1/2) ∫₀¹ (Dv)²`, and `R(v,τ) = 0` pointwise. -/
theorem ex012_22_determine_constant_integration (τ : ℝ) {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hp : Function.Periodic v 1)
    (hmean : ∫ x in (0:ℝ)..1, v x = 0) {K : ℝ}
    (hK : ∀ x, angD_EX01217 (angD_EX01217 v) x + v x + (angD_EX01217 v x) ^ 2 / 2
      + (τ / 4) * Real.cos (2 * Real.pi * 2 * x) = K) :
    K = (1 / 2 : ℝ) * ∫ x in (0:ℝ)..1, (angD_EX01217 v x) ^ 2 ∧
      ∀ x, eulerR_EX01222 τ v x = 0 := by
  have hDv : ContDiff ℝ ∞ (angD_EX01217 v) := contDiff_angD_EX01217 hv
  have hDDv : Continuous (angD_EX01217 (angD_EX01217 v)) :=
    (contDiff_angD_EX01217 hDv).continuous
  have hvc : Continuous v := hv.continuous
  have hsq : Continuous (fun x => (angD_EX01217 v x) ^ 2 / 2) :=
    (hDv.continuous.pow 2).div_const 2
  have hcos : Continuous (fun x : ℝ => (τ / 4) * Real.cos (2 * Real.pi * 2 * x)) := by
    fun_prop
  -- integrate the pointwise identity over the period cell
  have hK' : ∫ x in (0:ℝ)..1, (angD_EX01217 (angD_EX01217 v) x + v x
      + (angD_EX01217 v x) ^ 2 / 2 + (τ / 4) * Real.cos (2 * Real.pi * 2 * x))
      = ∫ x in (0:ℝ)..1, K :=
    intervalIntegral.integral_congr (fun x _ => hK x)
  rw [intervalIntegral.integral_const, sub_zero, one_smul] at hK'
  have i1 : IntervalIntegrable (fun x => angD_EX01217 (angD_EX01217 v) x + v x
      + (angD_EX01217 v x) ^ 2 / 2) MeasureTheory.volume 0 1 :=
    ((hDDv.add hvc).add hsq).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => (τ / 4) * Real.cos (2 * Real.pi * 2 * x))
      MeasureTheory.volume 0 1 :=
    hcos.intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x => angD_EX01217 (angD_EX01217 v) x + v x)
      MeasureTheory.volume 0 1 :=
    (hDDv.add hvc).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun x => (angD_EX01217 v x) ^ 2 / 2) MeasureTheory.volume 0 1 :=
    hsq.intervalIntegrable _ _
  have i5 : IntervalIntegrable (angD_EX01217 (angD_EX01217 v)) MeasureTheory.volume 0 1 :=
    hDDv.intervalIntegrable _ _
  have i6 : IntervalIntegrable v MeasureTheory.volume 0 1 := hvc.intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_add i5 i6, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, int_angD_angD_EX01222 hv hp, hmean,
    int_cos_two_EX01222] at hK'
  have hKI : K = (1 / 2 : ℝ) * ∫ x in (0:ℝ)..1, (angD_EX01217 v x) ^ 2 := by
    linarith
  refine ⟨hKI, fun x => ?_⟩
  unfold eulerR_EX01222
  linear_combination hK x + hKI

/-- The same conclusion with the constant given as `∃ K`, the form delivered by EX012.21. -/
theorem ex012_22_determine_constant_integration_exists (τ : ℝ) {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hp : Function.Periodic v 1)
    (hmean : ∫ x in (0:ℝ)..1, v x = 0)
    (hex : ∃ K : ℝ, ∀ x, angD_EX01217 (angD_EX01217 v) x + v x + (angD_EX01217 v x) ^ 2 / 2
      + (τ / 4) * Real.cos (2 * Real.pi * 2 * x) = K) :
    ∀ x, eulerR_EX01222 τ v x = 0 := by
  obtain ⟨K, hK⟩ := hex
  exact (ex012_22_determine_constant_integration τ hv hp hmean hK).2

end DGPS.Frontier.EX012
