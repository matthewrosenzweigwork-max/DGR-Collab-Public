import Mathlib
import DGPS.Frontier.EX012.T17

/-!
# EX012.23: Reverse the logarithmic transformation

Task id: EX012.23 (node EX012, one-site complementary range equation).
Title: Reverse the logarithmic transformation.

Provides:
* `DGPS.Frontier.EX012.massZ_EX01223 v`: the normalizing integral `Z = ∫₀¹ exp (v y) dy`.
* `DGPS.Frontier.EX012.logReverse_EX01223 v`: the map `u x = exp (v x / 2) / √Z`.
* `DGPS.Frontier.EX012.residual_EX01223 τ v`: the angular range residual
  `R(v,τ) x = D²v x + v x + ½ ((D v x)² − ∫₀¹ (D v)²) + (τ/4) cos (2θ)` with `θ = 2π x`.
* `DGPS.Frontier.EX012.ex012_23_reverse_logarithmic_transformation`: for a smooth one-periodic
  mean-zero `v` with `R(v,τ) = 0`, the map `u = logReverse_EX01223 v` is smooth, positive,
  has `∫₀¹ u² = 1`, and satisfies `-4 D²u + τ s₁² u - 4 u log u = λ u` pointwise for some
  real constant `λ`, with `D = (2π)⁻¹ ∂ₓ` and `s₁ x = sin (2π x)`.
* `DGPS.Frontier.EX012.ex012_23_reverse_logarithmic_transformation_multiplier`: the same
  pointwise equation with the explicit multiplier
  `λ = 2 log Z - ∫₀¹ (D v)² + τ/2`.
* Helpers (public, suffix `_EX01223`): `angD_div_const_EX01223` and
  `angD_angD_div_const_EX01223` (angular derivatives commute with division by a constant),
  `massZ_pos_EX01223` (`Z > 0`), `logReverse_contDiff_EX01223` (smoothness),
  `logReverse_pos_EX01223` (positivity), `logReverse_sq_mass_EX01223` (`∫₀¹ u² = 1`).

R5 notes:
* Hypotheses are those of the specification: `v` is smooth (`ContDiff ℝ ∞ v`), one-periodic
  (`Function.Periodic v 1`), mean-zero (`∫₀¹ v = 0`), and solves `R(v,τ) = 0` pointwise.
  "Smooth" is read as `C^∞`, not analytic (`ω`), as in EX012.17.
* The periodicity and mean-zero hypotheses are listed in the specification but are not used by
  the proof: the conclusions hold for every smooth solution of `R(v,τ) = 0`. They are kept as
  stated so the statement matches the specification exactly, under the names `_hvp` and
  `_hmean` (underscore only to silence the unused-variable linter).
* `D = (2π)⁻¹ ∂ₓ` is `angD_EX01217` from EX012.17.
* The residual's `cos (2θ)` is read as `cos (2 * (2π x))`, i.e. `c₂(x) = cos (4π x)` with
  `θ = 2π x`. This reading is forced: `τ s₁² + (τ/2) c₂ = τ/2` is what makes the multiplier
  constant, so the existence of a real `λ` depends on it.
* The Haar integral `∫ y` is the interval integral `∫ y in (0:ℝ)..1`. `Z` is the integral of
  `exp v` over `[0,1]`, and `u = exp (v/2) / √Z` uses the real square root.
* The log is `Real.log`. It is well defined because `u > 0`.
* "For a real `λ`" is read as an existential over a constant `λ` that does not depend on `x`.
  The explicit value `2 log Z - ∫₀¹ (D v)² + τ/2` is given in the multiplier lemma.
* The specification's optional identification `λ = E_h(u²)` (the ground functional) is not
  formalized. The frozen task asks only for the existence of a multiplier.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- The normalizing integral `Z = ∫₀¹ exp (v y) dy` (Haar integral over `[0,1]`). -/
noncomputable def massZ_EX01223 (v : ℝ → ℝ) : ℝ :=
  ∫ y in (0:ℝ)..1, Real.exp (v y)

/-- The reversed logarithmic transformation `u x = exp (v x / 2) / √Z`. -/
noncomputable def logReverse_EX01223 (v : ℝ → ℝ) : ℝ → ℝ :=
  fun x => Real.exp (v x / 2) / Real.sqrt (massZ_EX01223 v)

/-- The angular range residual
`R(v,τ) x = D²v x + v x + ½ ((D v x)² − ∫₀¹ (D v)²) + (τ/4) cos (2θ)` with `θ = 2π x`. -/
noncomputable def residual_EX01223 (τ : ℝ) (v : ℝ → ℝ) : ℝ → ℝ :=
  fun x => angD_EX01217 (angD_EX01217 v) x + v x
    + (1 / 2 : ℝ) * (angD_EX01217 v x ^ 2 - ∫ y in (0:ℝ)..1, angD_EX01217 v y ^ 2)
    + (τ / 4) * Real.cos (2 * (2 * Real.pi * x))

/-- Angular derivative commutes with division by a constant. -/
theorem angD_div_const_EX01223 (g : ℝ → ℝ) (c x : ℝ) :
    angD_EX01217 (fun y => g y / c) x = angD_EX01217 g x / c := by
  rw [angD_EX01217_apply, angD_EX01217_apply, deriv_div_const]
  ring

/-- Second angular derivative commutes with division by a constant. -/
theorem angD_angD_div_const_EX01223 (g : ℝ → ℝ) (c x : ℝ) :
    angD_EX01217 (angD_EX01217 (fun y => g y / c)) x = angD_EX01217 (angD_EX01217 g) x / c := by
  have h : angD_EX01217 (fun y => g y / c) = fun y => angD_EX01217 g y / c :=
    funext fun y => angD_div_const_EX01223 g c y
  rw [h, angD_div_const_EX01223]

/-- The normalizing integral is strictly positive for continuous `v`. -/
theorem massZ_pos_EX01223 {v : ℝ → ℝ} (hv : Continuous v) :
    0 < massZ_EX01223 v := by
  unfold massZ_EX01223
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous fun y => Real.exp (v y)).intervalIntegrable _ _
  · intro x _
    exact Real.exp_pos _
  · norm_num

/-- The reversed transformation is smooth for smooth `v`. -/
theorem logReverse_contDiff_EX01223 {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (logReverse_EX01223 v) := by
  unfold logReverse_EX01223
  exact ((hv.div_const 2).exp).div_const _

/-- The reversed transformation is positive for continuous `v`. -/
theorem logReverse_pos_EX01223 {v : ℝ → ℝ} (hv : Continuous v) (x : ℝ) :
    0 < logReverse_EX01223 v x := by
  unfold logReverse_EX01223
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (massZ_pos_EX01223 hv))

/-- The reversed transformation has squared mass one. -/
theorem logReverse_sq_mass_EX01223 {v : ℝ → ℝ} (hv : Continuous v) :
    ∫ x in (0:ℝ)..1, logReverse_EX01223 v x ^ 2 = 1 := by
  have hZ : 0 < massZ_EX01223 v := massZ_pos_EX01223 hv
  have hsq : ∀ x, logReverse_EX01223 v x ^ 2 = Real.exp (v x) / massZ_EX01223 v := by
    intro x
    unfold logReverse_EX01223
    have he : Real.exp (v x / 2) ^ 2 = Real.exp (v x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [div_pow, Real.sq_sqrt hZ.le, he]
  simp only [hsq]
  rw [intervalIntegral.integral_div]
  exact div_self hZ.ne'

/-- The multiplier identity, pointwise, with the explicit multiplier
`λ = 2 log Z - ∫₀¹ (D v)² + τ/2`. -/
theorem ex012_23_reverse_logarithmic_transformation_multiplier {τ : ℝ} {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (hR : ∀ x, residual_EX01223 τ v x = 0) :
    ∀ x, -4 * angD_EX01217 (angD_EX01217 (logReverse_EX01223 v)) x
      + τ * Real.sin (2 * Real.pi * x) ^ 2 * logReverse_EX01223 v x
      - 4 * logReverse_EX01223 v x * Real.log (logReverse_EX01223 v x)
      = (2 * Real.log (massZ_EX01223 v) - (∫ y in (0:ℝ)..1, angD_EX01217 v y ^ 2) + τ / 2)
        * logReverse_EX01223 v x := by
  intro x
  have hZ : 0 < massZ_EX01223 v := massZ_pos_EX01223 hv.continuous
  have hs : 0 < Real.sqrt (massZ_EX01223 v) := Real.sqrt_pos.mpr hZ
  have hfd : ∀ y, HasDerivAt (fun z => Real.exp (v z / 2))
      (Real.exp (v y / 2) * (deriv v y / 2)) y := fun y =>
    (((hv.differentiable (by simp) y).hasDerivAt).div_const 2).exp
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hd : ∀ y, deriv v y = 2 * Real.pi * angD_EX01217 v y := fun y => by
    rw [angD_EX01217_apply, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hAf : angD_EX01217 (fun z => Real.exp (v z / 2))
      = fun z => (1 / 2 : ℝ) * angD_EX01217 v z * Real.exp (v z / 2) := by
    funext y
    rw [angD_EX01217_apply, (hfd y).deriv, angD_EX01217_apply]
    ring
  have hGd : HasDerivAt (fun z => (1 / 2 : ℝ) * angD_EX01217 v z * Real.exp (v z / 2))
      (1 / 2 * (2 * Real.pi * angD_EX01217 (angD_EX01217 v) x) * Real.exp (v x / 2)
        + 1 / 2 * angD_EX01217 v x * (Real.exp (v x / 2) * (deriv v x / 2))) x :=
    ((hasDerivAt_angD_EX01217 hv x).const_mul (1 / 2 : ℝ)).mul (hfd x)
  have hDD : angD_EX01217 (angD_EX01217 (fun z => Real.exp (v z / 2))) x
      = (1 / 2 * angD_EX01217 (angD_EX01217 v) x + 1 / 4 * angD_EX01217 v x ^ 2)
        * Real.exp (v x / 2) := by
    rw [hAf]
    change (2 * Real.pi)⁻¹ * deriv (fun z => (1 / 2 : ℝ) * angD_EX01217 v z
      * Real.exp (v z / 2)) x = _
    rw [hGd.deriv, hd x]
    field_simp
    ring
  have hDDu : angD_EX01217 (angD_EX01217 (logReverse_EX01223 v)) x
      = angD_EX01217 (angD_EX01217 (fun z => Real.exp (v z / 2))) x
        / Real.sqrt (massZ_EX01223 v) :=
    angD_angD_div_const_EX01223 (fun z => Real.exp (v z / 2)) _ x
  have hu : logReverse_EX01223 v x = Real.exp (v x / 2) / Real.sqrt (massZ_EX01223 v) := rfl
  have hD2u : angD_EX01217 (angD_EX01217 (logReverse_EX01223 v)) x
      = (1 / 2 * angD_EX01217 (angD_EX01217 v) x + 1 / 4 * angD_EX01217 v x ^ 2)
        * logReverse_EX01223 v x := by
    rw [hDDu, hDD, hu]
    ring
  have hlog : Real.log (logReverse_EX01223 v x)
      = v x / 2 - Real.log (Real.sqrt (massZ_EX01223 v)) := by
    rw [hu, Real.log_div (Real.exp_pos _).ne' hs.ne', Real.log_exp]
  have hlogZ : Real.log (massZ_EX01223 v) = 2 * Real.log (Real.sqrt (massZ_EX01223 v)) := by
    rw [Real.log_sqrt hZ.le]
    ring
  have hsin : τ * Real.sin (2 * Real.pi * x) ^ 2
      = τ / 2 - τ / 2 * Real.cos (2 * (2 * Real.pi * x)) := by
    rw [Real.cos_two_mul]
    linear_combination τ * Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  have hRx := hR x
  unfold residual_EX01223 at hRx
  linear_combination (-4 : ℝ) * hD2u + (-4 * logReverse_EX01223 v x) * hlog
    + (-2 * logReverse_EX01223 v x) * hlogZ + (-2 * logReverse_EX01223 v x) * hRx
    + logReverse_EX01223 v x * hsin

/-- Reverse the logarithmic transformation: for a smooth one-periodic mean-zero `v` with
`R(v,τ) = 0`, the map `u = exp (v/2) / √(∫₀¹ exp v)` is smooth, positive, has `∫₀¹ u² = 1`,
and satisfies `-4 D²u + τ s₁² u - 4 u log u = λ u` for a real constant `λ`. -/
theorem ex012_23_reverse_logarithmic_transformation {τ : ℝ} {v : ℝ → ℝ}
    (hv : ContDiff ℝ ∞ v) (_hvp : Function.Periodic v 1)
    (_hmean : ∫ x in (0:ℝ)..1, v x = 0)
    (hR : ∀ x, residual_EX01223 τ v x = 0) :
    ContDiff ℝ ∞ (logReverse_EX01223 v) ∧
    (∀ x, 0 < logReverse_EX01223 v x) ∧
    (∫ x in (0:ℝ)..1, logReverse_EX01223 v x ^ 2 = 1) ∧
    ∃ lam : ℝ, ∀ x, -4 * angD_EX01217 (angD_EX01217 (logReverse_EX01223 v)) x
      + τ * Real.sin (2 * Real.pi * x) ^ 2 * logReverse_EX01223 v x
      - 4 * logReverse_EX01223 v x * Real.log (logReverse_EX01223 v x)
      = lam * logReverse_EX01223 v x := by
  exact ⟨logReverse_contDiff_EX01223 hv, logReverse_pos_EX01223 hv.continuous,
    logReverse_sq_mass_EX01223 hv.continuous,
    ⟨2 * Real.log (massZ_EX01223 v) - (∫ y in (0:ℝ)..1, angD_EX01217 v y ^ 2) + τ / 2,
      ex012_23_reverse_logarithmic_transformation_multiplier hv hR⟩⟩

end DGPS.Frontier.EX012
