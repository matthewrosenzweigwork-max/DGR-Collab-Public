import DGPS.Frontier.EX012.T13

/-!
# EX012.14: Normalized centered logarithm

Task id: EX012.14 (node EX012, leaf formalization).
Title: Normalized centered logarithm.

For a strictly positive smooth one-periodic `r` on the torus with Haar mass one (the smooth
representative transferred by EX012.13), put `ℓ = ∫ log r` and `v = log r - ℓ`. Then `∫ v = 0`,
`exp v = exp(-ℓ) r`, `∫ exp v = exp(-ℓ) > 0`, and `√r = exp(v/2) / (∫ exp v)^(1/2)` pointwise.

## Provides

* `DGPS.Frontier.EX012.ex012_14_normalized_centered_logarithm_mean_zero`: `∫ (log r - ℓ) = 0`.
* `DGPS.Frontier.EX012.ex012_14_normalized_centered_logarithm_exp_formula`: pointwise
  `exp (log r x - ℓ) = exp (-ℓ) * r x`.
* `DGPS.Frontier.EX012.ex012_14_normalized_centered_logarithm_exp_integral`: `∫ exp (log r - ℓ) = exp (-ℓ)`.
* `DGPS.Frontier.EX012.ex012_14_normalized_centered_logarithm_sqrt_formula`: pointwise
  `√(r x) = exp ((log r x - ℓ)/2) / (∫ exp (log r - ℓ))^(1/2)` (real power `1/2`).
* `DGPS.Frontier.EX012.ex012_14_normalized_centered_logarithm`: the conjunction of the four
  identities above with `0 < exp (-ℓ)`, for one `r`.
* `DGPS.Frontier.EX012.ex012_14_normalized_centered_logarithm_ex011`: the same conclusions for the
  representative `r` of every minimizing `ρ` covered by EX011 (small `h`), with `r` supplied by
  EX012.13 (`∃ h0`, `∀ h ∈ (0, h0)`, `∀ minimizing ρ`, `∃ r`).

## R5 notes

* Domain: `r : Torus 1 → ℝ`, the representative of EX012.13 (the torus is the period cell of the
  one-periodic lift; the Haar probability measure `haar 1` is the "probability integral"). The
  specification's `∫` is read as `∫ x, _ ∂haar 1`.
* Hypotheses used: `∀ x, 0 < r x` (needed: `exp (log r) = r` requires `r > 0`), `IsSmoothPeriodic r`
  (used only through its continuity on the torus, which makes `log r` continuous and integrable;
  smoothness is not otherwise needed), and `∫ r = 1`. The mass hypothesis is not written in the
  specification's statement list, but the claim `∫ exp v = exp (-ℓ)` is false without it
  (`∫ exp v = exp (-ℓ) ∫ r`). It is the mass-one property delivered by EX012.13 for the density
  representative, and it is the only additional hypothesis.
* `√` and `(∫ exp v)^(1/2)` are stated literally: `Real.sqrt` for `√r`, and the real power
  `(·) ^ (1/2 : ℝ)` for the denominator. The proof uses `Real.sqrt_eq_rpow` and
  `Real.rpow_def_of_pos`, so no positivity-of-square-root claim is taken as an assumption.
* The specification's "probability integral" is the Haar integral; no interval form is used here.
* No limiting argument is involved; all integrals are of continuous functions on the compact torus.
-/

open MeasureTheory
open DGPS.Circle.VonMisesSmallField

namespace DGPS.Frontier.EX012

theorem continuous_log_EX01214 {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) : Continuous fun x => Real.log (r x) :=
  hsm.continuous_torus.log fun x => (hr x).ne'

theorem integrable_log_EX01214 {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) : Integrable (fun x => Real.log (r x)) (haar 1) :=
  (continuous_log_EX01214 hr hsm).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem ex012_14_normalized_centered_logarithm_mean_zero {r : Torus 1 → ℝ}
    (hr : ∀ x, 0 < r x) (hsm : IsSmoothPeriodic r) :
    ∫ x, (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 = 0 := by
  rw [integral_sub (integrable_log_EX01214 hr hsm) (integrable_const _), integral_const]
  simp

theorem ex012_14_normalized_centered_logarithm_exp_formula {r : Torus 1 → ℝ}
    (hr : ∀ x, 0 < r x) :
    ∀ x, Real.exp (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) =
      Real.exp (-(∫ y, Real.log (r y) ∂haar 1)) * r x := by
  intro x
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (hr x)]
  ring

theorem ex012_14_normalized_centered_logarithm_exp_integral {r : Torus 1 → ℝ}
    (hr : ∀ x, 0 < r x) (hmass : ∫ x, r x ∂haar 1 = 1) :
    ∫ x, Real.exp (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 =
      Real.exp (-(∫ y, Real.log (r y) ∂haar 1)) := by
  simp only [ex012_14_normalized_centered_logarithm_exp_formula hr]
  rw [integral_const_mul, hmass, mul_one]

theorem ex012_14_normalized_centered_logarithm_sqrt_formula {r : Torus 1 → ℝ}
    (hr : ∀ x, 0 < r x) (hmass : ∫ x, r x ∂haar 1 = 1) (x : Torus 1) :
    Real.sqrt (r x) = Real.exp ((Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) / 2) /
      (∫ z, Real.exp (Real.log (r z) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1) ^ (1 / 2 : ℝ) := by
  rw [ex012_14_normalized_centered_logarithm_exp_integral hr hmass, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (hr x), Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← Real.exp_sub]
  congr 1
  ring

theorem ex012_14_normalized_centered_logarithm {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) (hmass : ∫ x, r x ∂haar 1 = 1) :
    (∫ x, (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 = 0) ∧
    (∀ x, Real.exp (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) =
      Real.exp (-(∫ y, Real.log (r y) ∂haar 1)) * r x) ∧
    (∫ x, Real.exp (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 =
      Real.exp (-(∫ y, Real.log (r y) ∂haar 1))) ∧
    0 < Real.exp (-(∫ y, Real.log (r y) ∂haar 1)) ∧
    (∀ x, Real.sqrt (r x) = Real.exp ((Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) / 2) /
      (∫ z, Real.exp (Real.log (r z) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1) ^ (1 / 2 : ℝ)) :=
  ⟨ex012_14_normalized_centered_logarithm_mean_zero hr hsm,
    ex012_14_normalized_centered_logarithm_exp_formula hr,
    ex012_14_normalized_centered_logarithm_exp_integral hr hmass,
    Real.exp_pos _,
    fun x => ex012_14_normalized_centered_logarithm_sqrt_formula hr hmass x⟩

theorem ex012_14_normalized_centered_logarithm_ex011 :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 → ∀ ρ : AbsoluteDensity 1,
      (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
      ∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r ∧
        (∫ x, (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 = 0) ∧
        (∀ x, Real.exp (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) =
          Real.exp (-(∫ y, Real.log (r y) ∂haar 1)) * r x) ∧
        (∫ x, Real.exp (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 =
          Real.exp (-(∫ y, Real.log (r y) ∂haar 1))) ∧
        0 < Real.exp (-(∫ y, Real.log (r y) ∂haar 1)) ∧
        (∀ x, Real.sqrt (r x) = Real.exp ((Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) / 2) /
          (∫ z, Real.exp (Real.log (r z) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1) ^ (1 / 2 : ℝ)) := by
  obtain ⟨h0, hh0, hT⟩ := ex012_13_transfer_smooth_representative_mass_ex011
  refine ⟨h0, hh0, fun h hpos hlt ρ hmin => ?_⟩
  obtain ⟨r, hr, hsm, hρ, -, -, hmass, -⟩ := hT h hpos hlt ρ hmin
  exact ⟨r, hr, hsm, hρ, ex012_14_normalized_centered_logarithm hr hsm hmass⟩

end DGPS.Frontier.EX012
