import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# EX049.49: Inner exponential integral

Task id and title: EX049.49, "Inner exponential integral" (node EX049, leaf formalization,
verification level V1). For every real `h ≥ 2`, every real `u`, and every `α ∈ [0, 1]`, the
integral over `β ∈ [0, 1 - α]` of `exp (-(h * (α * u + 2 * β)))` equals
`(exp (-(h * (α * u))) - exp (-(2 * h)) * exp (h * (α * (2 - u)))) / (2 * h)`.

## Provides

- `DGPS.Frontier.EX049.ex049_49_inner_exponential_integral`: the identity above, stated as an
  interval integral in `β` from `0` to `1 - α`, for real `h ≥ 2`, real `u`, and `α ∈ Set.Icc 0 1`.
- Helpers: none. The proof is self-contained and declares no auxiliary constants.

## R5 notes

- The hypothesis `2 ≤ h` is the specification's `h ≥ 2`, kept verbatim. The proof uses only the
  consequence `0 < 2 * h`, which makes the factor `2 * h` nonzero. No hypothesis beyond the
  specification is introduced, and none is weakened.
- `α ∈ [0, 1]` is the single hypothesis `α ∈ Set.Icc (0 : ℝ) 1`. The proof does not need the
  upper bound `α ≤ 1`, because the fundamental theorem of calculus holds for any pair of
  endpoints; the bound is kept as written so that the statement matches the specification.
- The integral is Mathlib's interval integral with respect to Lebesgue measure on `ℝ`, with
  the oriented convention. On `α ∈ [0, 1]` the upper endpoint `1 - α` is nonnegative, so this is
  the specified integral over `[0, 1 - α]`.
- `u` is an arbitrary real number. No sign, size or positivity condition is imposed on it.
- Integrability is not assumed. It is derived from continuity of the real exponential and of the
  affine exponent, through `Continuous.intervalIntegrable`, as the specification indicates.
- The proof is the fundamental theorem of calculus with the antiderivative
  `β ↦ -(exp (-(h * (α * u + 2 * β)))) / (2 * h)`. Its derivative is computed by the chain rule
  (`HasDerivAt.exp`, `HasDerivAt.neg`, `HasDerivAt.div_const`), and the derivative value is
  matched with the integrand by `div_eq_iff`.
- Non-literal reading, algebra only: the specification's exponents `-h(αu+2β)`, `-hαu`,
  `hα(2-u)` and `-2h` are written with explicit parentheses as `-(h * (α * u + 2 * β))`,
  `-(h * (α * u))`, `h * (α * (2 - u))` and `-(2 * h)`. They denote the same real numbers.
  The factor `e^{-2h} e^{hα(2-u)}` is `Real.exp (-(2 * h)) * Real.exp (h * (α * (2 - u)))`.
- The specification's remark that both sides vanish at `α = 1` is a consequence of the identity.
  It is not assumed or stated as a separate claim.
- Only real exponentials are used. No Sobolev, entropy, circle or other campaign definition is
  used, so the unit depends on no other campaign module.
-/

namespace DGPS.Frontier.EX049

/-- For real `h ≥ 2`, real `u`, and `α ∈ [0, 1]`, the integral over `β ∈ [0, 1 - α]` of
`exp (-(h * (α * u + 2 * β)))` equals `(exp (-(h * (α * u))) - exp (-(2 * h)) * exp (h * (α * (2 - u)))) / (2 * h)`. -/
theorem ex049_49_inner_exponential_integral (h : ℝ) (hh : 2 ≤ h) (u α : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∫ β in (0 : ℝ)..(1 - α), Real.exp (-(h * (α * u + 2 * β))) =
      (Real.exp (-(h * (α * u))) - Real.exp (-(2 * h)) * Real.exp (h * (α * (2 - u)))) /
        (2 * h) := by
  obtain ⟨-, -⟩ := hα
  have hpos : (0 : ℝ) < 2 * h := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (1 - α),
      HasDerivAt (fun β : ℝ => -(Real.exp (-(h * (α * u + 2 * β)))) / (2 * h))
        (Real.exp (-(h * (α * u + 2 * x)))) x := by
    intro x _
    have hlin : HasDerivAt (fun β : ℝ => α * u + 2 * β) 2 x :=
      (((hasDerivAt_id' x).const_mul (2 : ℝ)).const_add (α * u)).congr_deriv (by ring)
    have hg : HasDerivAt (fun β : ℝ => -(h * (α * u + 2 * β))) (-(h * 2)) x :=
      (hlin.const_mul h).neg
    have he := (hg.exp.neg).div_const (2 * h)
    refine he.congr_deriv ?_
    rw [div_eq_iff hpos.ne']
    ring
  have hint : IntervalIntegrable (fun β : ℝ => Real.exp (-(h * (α * u + 2 * β))))
      MeasureTheory.volume 0 (1 - α) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have e1 : -(h * (α * u + 2 * (1 - α))) = -(2 * h) + h * (α * (2 - u)) := by ring
  have e0 : -(h * (α * u + 2 * (0 : ℝ))) = -(h * (α * u)) := by ring
  simp only [e1, e0, Real.exp_add]
  ring

end DGPS.Frontier.EX049
