import Mathlib

/-!
# EX049.37: Smooth exponential average

Task id and title: EX049.37, "Smooth exponential average" (node EX049, frontier unit, leaf
formalization).  For a fixed real `h > 0` let `J_h(u) = ∫_0^1 e^{-h u τ} dτ`.  Then `J_h` is
`C^∞` on `ℝ`, its `k`-th derivative is `∫_0^1 (-h τ)^k e^{-h u τ} dτ` for every `k : ℕ`, and
`1 - e^{-h u} = h u J_h(u)` for every real `u`, including `u = 0`.

## Provides
* `DGPS.Frontier.EX049.ex049_37_smooth_exponential_average` : the main statement, one conjunction
  about `u ↦ ∫ τ in 0..1, exp (-(h * u * τ))`: (1) it is `ContDiff ℝ ∞`; (2) for all `k : ℕ` and
  all `u`, its `k`-th iterated derivative at `u` is `∫ τ in 0..1, (-(h * τ)) ^ k * exp (-(h * u * τ))`;
  (3) for all `u`, `1 - exp (-(h * u)) = h * u * ∫ τ in 0..1, exp (-(h * u * τ))`.
* `DGPS.Frontier.EX049.expAvgDeriv_EX04937` : helper definition, the integral
  `u ↦ ∫ τ in 0..1, (-(h * τ)) ^ k * exp (-(h * u * τ))` of order `k`.
* `DGPS.Frontier.EX049.expAvgDeriv_hasDerivAt_EX04937` : helper; the order-`k` integral has
  derivative the order-`k+1` integral at every point (dominated differentiation under the
  integral sign).
* `DGPS.Frontier.EX049.expAvgDeriv_iteratedDeriv_EX04937` : helper; the `k`-th iterated derivative
  of the order-zero integral is the order-`k` integral.
* `DGPS.Frontier.EX049.one_sub_exp_eq_mul_expAvg_EX04937` : helper; the identity
  `1 - exp (-(h * u)) = h * u * ∫ τ in 0..1, exp (-(h * u * τ))` for every real `u`.

## R5 notes
* The hypothesis `0 < h` is the specification's "fixed real `h > 0`".  It is kept as written and
  is used in the domination estimate (the constant bound `h^(k+1) e^{h(|u|+1)}` uses `h ≥ 0`).
* `J_h` is written inline as the function `fun u => ∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))`
  (oriented interval integral over `[0,1]`, Lebesgue measure), not through a named definition, so
  that the main statement is checkable on sight.  The argument `-(h u τ)` is `-(h * u * τ)`.
* "Smooth on the real line" is read as `ContDiff ℝ ∞`, with `∞` the `ℕ∞`-top smoothness class and
  not the analytic class `ω`.
* "`J_h^{(k)}`" is read as `iteratedDeriv k` of the function, for every `k : ℕ`.  The statement is
  asserted for all `k` and all real `u` as a pointwise equality.
* The identity `1 - e^{-hu} = hu J_h(u)` is stated for all real `u` with no case split; the proof
  uses the fundamental theorem of calculus in `τ` and so needs no division, matching the
  specification's remark that both sides are zero at `u = 0`.
* The proof follows the specification: on the ball `|x - u| < 1` the order-`(k+1)` integrand is
  bounded by the constant `h^(k+1) e^{h(|u|+1)}`, which is integrable on `[0,1]`, and the
  parametric-integral theorem `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  (dominated convergence for the difference quotients) differentiates the integral.  Iterating in
  `k` gives every derivative; differentiability of every iterated derivative then gives `C^∞`.
  Continuity of the derivatives is obtained from their differentiability, which is slightly
  stronger than what the specification states and avoids a separate continuity argument.
* No hypothesis is added beyond the specification's, and no Mathlib declaration is assumed.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- The order-`k` integral `u ↦ ∫_0^1 (-h τ)^k e^{-h u τ} dτ`; order zero is `J_h`. -/
noncomputable def expAvgDeriv_EX04937 (h : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∫ τ in (0:ℝ)..1, (-(h * τ)) ^ k * Real.exp (-(h * u * τ))

/-- The integrand of the order-`k` integral is continuous in `τ`. -/
lemma continuous_integrand_EX04937 (h : ℝ) (k : ℕ) (x : ℝ) :
    Continuous fun τ : ℝ => (-(h * τ)) ^ k * Real.exp (-(h * x * τ)) := by
  fun_prop

/-- Dominated differentiation under the integral sign: the order-`k` integral has derivative the
order-`k+1` integral at every real point. -/
lemma expAvgDeriv_hasDerivAt_EX04937 {h : ℝ} (hh : 0 < h) (k : ℕ) (u : ℝ) :
    HasDerivAt (expAvgDeriv_EX04937 h k) (expAvgDeriv_EX04937 h (k + 1) u) u := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1)
    (F := fun x τ => (-(h * τ)) ^ k * Real.exp (-(h * x * τ)))
    (F' := fun x τ => (-(h * τ)) ^ (k + 1) * Real.exp (-(h * x * τ)))
    (x₀ := u) (s := Metric.ball u 1)
    (bound := fun _ => h ^ (k + 1) * Real.exp (h * (|u| + 1)))
    (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun x => (continuous_integrand_EX04937 h k x).aestronglyMeasurable)
    ((continuous_integrand_EX04937 h k u).intervalIntegrable _ _)
    (continuous_integrand_EX04937 h (k + 1) u).aestronglyMeasurable
    ?_ intervalIntegrable_const ?_
  · exact key.2
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hxu : |x - u| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
    have hx' : |x| ≤ |u| + 1 := by
      calc |x| = |(x - u) + u| := by ring_nf
        _ ≤ |x - u| + |u| := abs_add_le _ _
        _ ≤ |u| + 1 := by linarith
    have ht0 : 0 ≤ t := ht.1.le
    have ht1 : t ≤ 1 := ht.2
    have hht : h * t ≤ h := by nlinarith
    have hht0 : 0 ≤ h * t := by positivity
    have hexp : Real.exp (-(h * x * t)) ≤ Real.exp (h * (|u| + 1)) := by
      apply Real.exp_le_exp.mpr
      have h1 : -x ≤ |x| := neg_le_abs x
      have h2 : -x * t ≤ |x| * t := mul_le_mul_of_nonneg_right h1 ht0
      have h3 : |x| * t ≤ |x| := by nlinarith [abs_nonneg x]
      nlinarith
    rw [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, abs_of_nonneg hht0,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (pow_le_pow_left₀ hht0 hht _) hexp (Real.exp_pos _).le (by positivity)
  · refine Filter.Eventually.of_forall fun t _ x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => -(h * y * t)) (-(h * 1 * t)) x :=
      (((hasDerivAt_id x).const_mul h).mul_const t).neg
    have h2 := (h1.exp).const_mul ((-(h * t)) ^ k)
    convert h2 using 1
    ring

/-- The `k`-th iterated derivative of the order-zero integral `J_h` is the order-`k` integral. -/
lemma expAvgDeriv_iteratedDeriv_EX04937 {h : ℝ} (hh : 0 < h) (k : ℕ) :
    iteratedDeriv k (expAvgDeriv_EX04937 h 0) = expAvgDeriv_EX04937 h k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (expAvgDeriv_hasDerivAt_EX04937 hh k u).deriv

/-- The identity `1 - e^{-hu} = h u J_h(u)` for every real `u`, by the fundamental theorem of
calculus in `τ`; no division by `u` occurs. -/
lemma one_sub_exp_eq_mul_expAvg_EX04937 (h u : ℝ) :
    1 - Real.exp (-(h * u)) = h * u * ∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ)) := by
  have hderiv : ∀ τ ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun τ : ℝ => Real.exp (-(h * u * τ)))
        (Real.exp (-(h * u * τ)) * (-(h * u))) τ := by
    intro τ _
    have h1 : HasDerivAt (fun τ : ℝ => -(h * u * τ)) (-(h * u)) τ :=
      (((hasDerivAt_id τ).const_mul (h * u)).neg).congr_deriv (by ring)
    exact h1.exp
  have hint : IntervalIntegrable (fun τ : ℝ => Real.exp (-(h * u * τ)) * (-(h * u))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_mul_const] at hftc
  simp only [mul_one, mul_zero, neg_zero, Real.exp_zero] at hftc
  linarith

/-- Smooth exponential average.  For every fixed real `h > 0`, the function
`J_h(u) = ∫_0^1 e^{-h u τ} dτ` is `C^∞`, its `k`-th derivative is `∫_0^1 (-h τ)^k e^{-h u τ} dτ`
for every `k : ℕ`, and `1 - e^{-h u} = h u J_h(u)` for every real `u`. -/
theorem ex049_37_smooth_exponential_average (h : ℝ) (hh : 0 < h) :
    ContDiff ℝ ∞ (fun u : ℝ => ∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) ∧
    (∀ (k : ℕ) (u : ℝ),
      iteratedDeriv k (fun u : ℝ => ∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) u =
        ∫ τ in (0:ℝ)..1, (-(h * τ)) ^ k * Real.exp (-(h * u * τ))) ∧
    (∀ u : ℝ, 1 - Real.exp (-(h * u)) = h * u * ∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) := by
  have hJ : (fun u : ℝ => ∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) =
      expAvgDeriv_EX04937 h 0 := by
    funext u
    simp [expAvgDeriv_EX04937]
  refine ⟨?_, ?_, fun u => one_sub_exp_eq_mul_expAvg_EX04937 h u⟩
  · rw [hJ]
    exact contDiff_of_differentiable_iteratedDeriv fun m _ => by
      rw [expAvgDeriv_iteratedDeriv_EX04937 hh m]
      exact fun u => (expAvgDeriv_hasDerivAt_EX04937 hh m u).differentiableAt
  · intro k u
    rw [hJ, expAvgDeriv_iteratedDeriv_EX04937 hh k]
    rfl

end DGPS.Frontier.EX049
