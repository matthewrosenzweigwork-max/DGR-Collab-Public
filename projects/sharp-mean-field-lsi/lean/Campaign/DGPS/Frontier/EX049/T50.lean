import DGPS.Frontier.EX049.T05
import DGPS.Frontier.EX049.T49

/-!
# EX049.50: Positive triangle formula on the open interval

Task id and title: EX049.50, "Positive triangle formula on the open interval" (node EX049, frontier
unit, leaf formalization, verification level V1). For real `h ≥ 2` let `A = 2 / (1 - e^{-2h})`,
`N v = A (1 - e^{-hv}) - v` and `r v = N v / (v (2 - v))`. For `0 < u < 2` the quotient `r u` equals
`A h^2` times the iterated integral of `e^{-h(αu + 2β)}`, first over `β ∈ [0, 1 - α]` and then over
`α ∈ [0, 1]`, and both iterated integrals are finite.

## Provides

* `DGPS.Frontier.EX049.ex049_50_positive_triangle_formula_open_interval`: for real `h` with `2 ≤ h`
  and real `u` with `0 < u < 2`, the identity `N u / (u * (2 - u))` equals `A * h ^ 2` times the
  iterated integral, together with two finiteness conjuncts: (a) for every `α ∈ [0, 1]` the
  `β`-integrand is interval integrable on `[0, 1 - α]`; (b) the outer function
  `α ↦ ∫ β in 0..(1 - α)` is interval integrable on `[0, 1]`.
* Helpers: none. The proof is one declaration whose intermediate facts are local `have` steps.

## R5 notes

* The only hypothesis beyond the variables is `2 ≤ h`, the specification's "every `h ≥ 2`", kept
  verbatim. The proof uses it only to obtain `0 < h`, `0 < 2 * h` and `exp (-(2 * h)) < 1`, which
  make the denominators nonzero. No hypothesis is added or weakened.
* The domain is the open interval `0 < u < 2` (`u ∈ Set.Ioo 0 2`), as the specification states.
  Nothing is claimed at `u = 0` or `u = 2`.
* `r_h(u)` is read as the quotient `N_h(u) / (u (2 - u))` of the specification, with
  `A_h = 2 / (1 - e^{-2h})` and `N_h(v) = A_h (1 - e^{-hv}) - v`. These are the same expressions as
  `A`, `N` and the quotient `Q` of EX049.05, which is cited as the prerequisite that fixes this
  quotient. No EX049.05 theorem is used. The binding of `r_h` to the campaign object `corr` is the
  open task EX049.25 and is not claimed here.
* "The two iterated integrals are finite" is read as two conjuncts: (a) for every `α ∈ [0, 1]` the
  `β`-integrand is interval integrable over `[0, 1 - α]`, so the inner integral is finite; (b) the
  outer function `α ↦ ∫ β in 0..(1 - α)` is interval integrable over `[0, 1]`, so the outer integral
  is finite. Lean's interval integral always returns a real number, so finiteness is expressed as
  integrability.
* For `α ∈ [0, 1]` the inner integral is evaluated by EX049.49
  (`DGPS.Frontier.EX049.ex049_49_inner_exponential_integral`). The specification's continuity remark
  is realised as continuity of that closed form on `[0, 1]`, transferred to the inner integral by
  `ContinuousOn.congr`. The outer integral is computed by the fundamental theorem of calculus with an
  explicit antiderivative. The final identity is rational algebra after unfolding `A`, using
  `1 - e^{-2h} ≠ 0`.
* Integrals are Mathlib oriented interval integrals with respect to Lebesgue measure on `ℝ`. For
  `α ∈ [0, 1]` the upper limit `1 - α` is nonnegative, so these are the specified integrals over
  `[0, 1 - α]`. The outer integrand is defined for every real `α` in Lean, but only its values on
  `[0, 1]` enter the statement, through the interval integral over `0..1`.
* Non-literal reading, algebra only: exponents carry explicit parentheses, `-(h * (α * u + 2 * β))`,
  `-(h * (α * u))`, `h * (α * (2 - u))` and `-(2 * h)`, which denote the same reals as the
  specification. The factor `A_h h^2` is written `A * h ^ 2`.
* No Sobolev, entropy, circle or other campaign definition is used. `u` is an arbitrary real in
  `(0, 2)`, with no further sign or size condition.
-/

namespace DGPS.Frontier.EX049

/-- Positive triangle formula on the open interval. For every real `h ≥ 2` and every `u` with
`0 < u < 2`, with `A = 2 / (1 - e^{-2h})` and `N v = A (1 - e^{-hv}) - v`, the quotient
`N u / (u (2 - u))` equals `A h^2` times the iterated integral of `e^{-h(αu + 2β)}`, the inner
integral over `β ∈ [0, 1 - α]` and the outer integral over `α ∈ [0, 1]`. Both iterated integrals are
finite: the inner integrand is interval integrable for every `α ∈ [0, 1]`, and the inner integral is
interval integrable in `α` over `[0, 1]`. -/
theorem ex049_50_positive_triangle_formula_open_interval (h : ℝ) (hh : 2 ≤ h) (u : ℝ)
    (hu : u ∈ Set.Ioo (0 : ℝ) 2) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun v => A * (1 - Real.exp (-(h * v))) - v
    N u / (u * (2 - u)) =
        A * h ^ 2 * (∫ α in (0 : ℝ)..1, ∫ β in (0 : ℝ)..(1 - α),
          Real.exp (-(h * (α * u + 2 * β)))) ∧
      (∀ α ∈ Set.Icc (0 : ℝ) 1,
        IntervalIntegrable (fun β : ℝ => Real.exp (-(h * (α * u + 2 * β))))
          MeasureTheory.volume 0 (1 - α)) ∧
      IntervalIntegrable
        (fun α : ℝ => ∫ β in (0 : ℝ)..(1 - α), Real.exp (-(h * (α * u + 2 * β))))
        MeasureTheory.volume 0 1 := by
  intro A N
  obtain ⟨hu0, hu2⟩ := hu
  have hhpos : (0 : ℝ) < h := by linarith
  have hh0 : h ≠ 0 := hhpos.ne'
  have hu_ne : u ≠ 0 := hu0.ne'
  have h2u_ne : 2 - u ≠ 0 := (sub_pos.mpr hu2).ne'
  have hlt1 : Real.exp (-(2 * h)) < 1 := by
    have h0 : Real.exp (-(2 * h)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_zero] at h0
  have hC1 : (1 : ℝ) - Real.exp (-(2 * h)) ≠ 0 := (sub_pos.mpr hlt1).ne'
  -- The closed form of the inner integral, from EX049.49, for every α in [0, 1].
  have hinner : ∀ α ∈ Set.Icc (0 : ℝ) 1,
      (∫ β in (0 : ℝ)..(1 - α), Real.exp (-(h * (α * u + 2 * β)))) =
        (Real.exp (-(h * (α * u))) - Real.exp (-(2 * h)) * Real.exp (h * (α * (2 - u)))) /
          (2 * h) :=
    fun α hα => ex049_49_inner_exponential_integral h hh u α hα
  have hgc : Continuous (fun α : ℝ =>
      (Real.exp (-(h * (α * u))) - Real.exp (-(2 * h)) * Real.exp (h * (α * (2 - u)))) /
        (2 * h)) := by
    fun_prop
  have hEq : Set.EqOn (fun α : ℝ => ∫ β in (0 : ℝ)..(1 - α), Real.exp (-(h * (α * u + 2 * β))))
      (fun α : ℝ =>
        (Real.exp (-(h * (α * u))) - Real.exp (-(2 * h)) * Real.exp (h * (α * (2 - u)))) /
          (2 * h))
      (Set.uIcc (0 : ℝ) 1) := by
    intro α hα
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hα
    exact hinner α hα
  have hinner_int : ∀ α ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable (fun β : ℝ => Real.exp (-(h * (α * u + 2 * β))))
        MeasureTheory.volume 0 (1 - α) :=
    fun α _ => Continuous.intervalIntegrable (by fun_prop) _ _
  have houter_int : IntervalIntegrable
      (fun α : ℝ => ∫ β in (0 : ℝ)..(1 - α), Real.exp (-(h * (α * u + 2 * β))))
      MeasureTheory.volume 0 1 :=
    (hgc.continuousOn.congr hEq).intervalIntegrable
  have hint_eq : (∫ α in (0 : ℝ)..1, ∫ β in (0 : ℝ)..(1 - α),
        Real.exp (-(h * (α * u + 2 * β)))) =
      ∫ α in (0 : ℝ)..1,
        (Real.exp (-(h * (α * u))) - Real.exp (-(2 * h)) * Real.exp (h * (α * (2 - u)))) /
          (2 * h) :=
    intervalIntegral.integral_congr hEq
  -- Explicit antiderivative of the closed form on [0, 1].
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun α : ℝ =>
      (-(Real.exp (-(h * (α * u)))) / (h * u) -
        Real.exp (-(2 * h)) * Real.exp (h * (α * (2 - u))) / (h * (2 - u))) / (2 * h))
      ((Real.exp (-(h * (x * u))) - Real.exp (-(2 * h)) * Real.exp (h * (x * (2 - u)))) /
        (2 * h)) x := by
    intro x _
    have hA1 : HasDerivAt (fun α : ℝ => -(h * (α * u))) (-(h * u)) x :=
      (((hasDerivAt_id' x).mul_const u).const_mul h).neg.congr_deriv (by ring)
    have hA2 : HasDerivAt (fun α : ℝ => h * (α * (2 - u))) (h * (2 - u)) x :=
      (((hasDerivAt_id' x).mul_const (2 - u)).const_mul h).congr_deriv (by ring)
    have hp1 := (hA1.exp.neg).div_const (h * u)
    have hp2 := ((hA2.exp.const_mul (Real.exp (-(2 * h)))).div_const (h * (2 - u)))
    have hF := (hp1.sub hp2).div_const (2 * h)
    refine hF.congr_deriv ?_
    field_simp
  -- The two exponentials at the upper endpoint combine to exp (-(h u)).
  have hrel : Real.exp (-(2 * h)) * Real.exp (h * (2 - u)) = Real.exp (-(h * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨?_, hinner_int, houter_int⟩
  rw [hint_eq, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hgc.intervalIntegrable 0 1)]
  simp only [mul_one, one_mul, mul_zero, zero_mul, neg_zero, Real.exp_zero, A, N]
  rw [hrel]
  field_simp
  ring

end DGPS.Frontier.EX049
