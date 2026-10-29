import DGPS.Frontier.EX049.T37

/-!
# EX049.38: Numerator and nonsingular local formulas

Task id and title: EX049.38, "Numerator and nonsingular local formulas" (node EX049, leaf
formalization, prerequisite EX049.37).  For a real `h ≥ 2` let `A = 2 / (1 - e^{-2h})`,
`N u = A (1 - e^{-h u}) - u`, and `J_h(v) = ∫_0^1 e^{-h v τ} dτ`.  Then `2 < A < 3`,
`N 0 = 0`, `N 2 = 0`, and for every `u ≠ 0`, `u ≠ 2`,
`N u / (u (2 - u)) = (A h J_h(u) - 1) / (2 - u)` and
`N u / (u (2 - u)) = (1 - A h e^{-2h} J_h(u - 2)) / u`.

## Provides
* `DGPS.Frontier.EX049.ex049_38_numerator_nonsingular_local_formulas` : the main statement, for
  `h ≥ 2`: the bounds `2 < A < 3`, the zeros `N 0 = 0` and `N 2 = 0`, and the two local
  formulas for `u ≠ 0`, `u ≠ 2`.
* `DGPS.Frontier.EX049.exp_neg_two_mul_lt_third_EX04938` : for `h ≥ 2`, `e^{-2h} < 1/3`.
* `DGPS.Frontier.EX049.A_bounds_EX04938` : for `h ≥ 2`, `2 < 2 / (1 - e^{-2h}) < 3`.
* `DGPS.Frontier.EX049.A_mul_den_EX04938` : for `h ≥ 2`, `A (1 - e^{-2h}) = 2` with `A` the
  quotient `2 / (1 - e^{-2h})`.
* `DGPS.Frontier.EX049.numerator_first_EX04938` : for all reals `A h u`,
  `A (1 - e^{-hu}) - u = u (A h J_h(u) - 1)`.
* `DGPS.Frontier.EX049.numerator_second_EX04938` : for reals `A h u` with
  `A (1 - e^{-2h}) = 2`, `A (1 - e^{-hu}) - u = (2 - u) (1 - A h e^{-2h} J_h(u - 2))`.

## R5 notes
* The only hypothesis of the main statement is `2 ≤ h`, the specification's "every `h ≥ 2`".
  No hypothesis is added, and the statement is not weakened.
* `A_h` and `N_h` are written as `let` bindings in the statement, and `J_h` is written inline as
  the oriented interval integral `∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))`, so that the
  formulas can be checked on sight.  `J_h(u - 2)` is the same integral with `u` replaced by
  `u - 2`, that is, the integrand `Real.exp (-(h * (u - 2) * τ))`.
* `e^{-2h}` is read as `Real.exp (-(2 * h))` and `e^{-hu}` as `Real.exp (-(h * u))`.
* "Away from the indicated zeros" is read as `u ≠ 0` and `u ≠ 2` for both formulas.  Both
  exclusions are needed for the statement to hold under Lean's division convention.  At `u = 0`
  the first right-hand side equals `(A h - 1) / 2`, which is nonzero because `A h ≥ 4`, while the
  left side is `0 / 0 = 0`.  At `u = 2` the second right-hand side equals
  `(1 - A h e^{-2h}) / 2`, which is nonzero for every `h ≥ 2`, while the left side is `0`.
* `2 < A < 3` is derived from `e^4 ≥ 5` (`Real.add_one_le_exp`), which gives
  `e^{-2h} ≤ e^{-4} < 1/3`.  The endpoint zeros `N 0 = 0` and `N 2 = 0` use only `A (1 - e^{-2h}) = 2`.
* The first local formula uses the identity `1 - e^{-hu} = h u J_h(u)` of EX049.37, the helper
  `DGPS.Frontier.EX049.one_sub_exp_eq_mul_expAvg_EX04937`, which holds for every real `u` with no
  division.  Division by `u` and by `2 - u` happens only in the final step of each formula.
* The second local formula uses `e^{-hu} = e^{-2h} e^{-h(u - 2)}` and the same identity at the
  point `u - 2`.  This is the nonsingular form for the endpoint `u = 2`, with no case split.
-/

namespace DGPS.Frontier.EX049

/-- For `h ≥ 2`, `e^{-2h} < 1/3`: indeed `e^{-2h} ≤ e^{-4} = 1 / e^4 ≤ 1/5`. -/
lemma exp_neg_two_mul_lt_third_EX04938 {h : ℝ} (hh : 2 ≤ h) :
    Real.exp (-(2 * h)) < 1 / 3 := by
  have hle : Real.exp (-(2 * h)) ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith)
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hprod : Real.exp (-4) * Real.exp 4 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos : 0 < Real.exp (-4) := Real.exp_pos _
  nlinarith

/-- For `h ≥ 2`, `A = 2 / (1 - e^{-2h})` satisfies `2 < A < 3`. -/
lemma A_bounds_EX04938 {h : ℝ} (hh : 2 ≤ h) :
    2 < 2 / (1 - Real.exp (-(2 * h))) ∧ 2 / (1 - Real.exp (-(2 * h))) < 3 := by
  have hq := exp_neg_two_mul_lt_third_EX04938 hh
  have hq0 : 0 < Real.exp (-(2 * h)) := Real.exp_pos _
  have hden : 0 < 1 - Real.exp (-(2 * h)) := by linarith
  constructor
  · rw [lt_div_iff₀ hden]
    linarith
  · rw [div_lt_iff₀ hden]
    linarith

/-- For `h ≥ 2`, `A (1 - e^{-2h}) = 2` with `A = 2 / (1 - e^{-2h})`. -/
lemma A_mul_den_EX04938 {h : ℝ} (hh : 2 ≤ h) :
    2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(2 * h))) = 2 := by
  have hq := exp_neg_two_mul_lt_third_EX04938 hh
  have hq0 : 0 < Real.exp (-(2 * h)) := Real.exp_pos _
  have hden : 0 < 1 - Real.exp (-(2 * h)) := by linarith
  exact div_mul_cancel₀ 2 hden.ne'

/-- The first numerator formula: `A (1 - e^{-hu}) - u = u (A h J_h(u) - 1)` for all reals. -/
lemma numerator_first_EX04938 (A h u : ℝ) :
    A * (1 - Real.exp (-(h * u))) - u =
      u * (A * h * (∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) - 1) := by
  rw [one_sub_exp_eq_mul_expAvg_EX04937]
  ring

/-- The second numerator formula, given `A (1 - e^{-2h}) = 2`:
`A (1 - e^{-hu}) - u = (2 - u) (1 - A h e^{-2h} J_h(u - 2))` for all reals `u`. -/
lemma numerator_second_EX04938 (A h u : ℝ) (hA : A * (1 - Real.exp (-(2 * h))) = 2) :
    A * (1 - Real.exp (-(h * u))) - u =
      (2 - u) * (1 - A * h * Real.exp (-(2 * h)) *
        (∫ τ in (0:ℝ)..1, Real.exp (-(h * (u - 2) * τ)))) := by
  have e1 : Real.exp (-(h * u)) = Real.exp (-(2 * h)) * Real.exp (-(h * (u - 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 := one_sub_exp_eq_mul_expAvg_EX04937 h (u - 2)
  have e3 : Real.exp (-(h * (u - 2))) =
      1 - h * (u - 2) * (∫ τ in (0:ℝ)..1, Real.exp (-(h * (u - 2) * τ))) := by
    linarith
  rw [e1, e3]
  linear_combination hA

/-- Numerator and nonsingular local formulas.  For every real `h ≥ 2`, with
`A = 2 / (1 - e^{-2h})` and `N u = A (1 - e^{-hu}) - u`, the bounds `2 < A < 3` hold, `N 0 = 0`
and `N 2 = 0`, and for `u ≠ 0`, `u ≠ 2` both local formulas hold, where `J_h(v)` is
`∫_0^1 e^{-h v τ} dτ`. -/
theorem ex049_38_numerator_nonsingular_local_formulas (h : ℝ) (hh : 2 ≤ h) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun u => A * (1 - Real.exp (-(h * u))) - u
    2 < A ∧ A < 3 ∧ N 0 = 0 ∧ N 2 = 0 ∧
      ∀ u : ℝ, u ≠ 0 → u ≠ 2 →
        N u / (u * (2 - u)) =
            (A * h * (∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) - 1) / (2 - u) ∧
        N u / (u * (2 - u)) =
            (1 - A * h * Real.exp (-(2 * h)) *
              (∫ τ in (0:ℝ)..1, Real.exp (-(h * (u - 2) * τ)))) / u := by
  intro A N
  have hNdef : ∀ u : ℝ, N u = A * (1 - Real.exp (-(h * u))) - u := fun u => rfl
  have hAq : A * (1 - Real.exp (-(2 * h))) = 2 := A_mul_den_EX04938 hh
  obtain ⟨hA2, hA3⟩ := A_bounds_EX04938 hh
  refine ⟨hA2, hA3, ?_, ?_, ?_⟩
  · rw [hNdef]
    simp
  · rw [hNdef, show -(h * 2) = -(2 * h) by ring]
    linarith
  · intro u hu0 hu2
    have h2u : (2 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu2)
    have hu2ne : u * (2 - u) ≠ 0 := mul_ne_zero hu0 h2u
    constructor
    · rw [hNdef, numerator_first_EX04938 A h u, div_eq_div_iff hu2ne h2u]
      ring
    · rw [hNdef, numerator_second_EX04938 A h u hAq, div_eq_div_iff hu2ne hu0]
      ring

end DGPS.Frontier.EX049
