import DGPS.Frontier.STR029.T09
import DGPS.Frontier.STR029.T17

/-!
# STR029.18: Exact reduced quartic and square completion

Task id: STR029.18. Title: Exact reduced quartic and square completion. Node STR029.
Prerequisites: STR029.09 (`J4_STR02909`, the polynomial `𝒥₄`) and STR029.17
(`qstarFn_STR02917`, the explicit range jet `q_*`).

Provides:
* `DGPS.Frontier.STR029.str029_18_exact_reduced_quartic_square_completion`: for all real
  `A, B, C, D, E, F`, `𝒥₄ = J_4^red(A, B) + (3/2)((C - C*)² + (D - D*)²) + (15/2)((E - E*)² + (F - F*)²)`,
  where `C*, D*, E*, F*` are the starred coefficients.
* `DGPS.Frontier.STR029.str029_18_exact_reduced_quartic_square_completion_starred_fourier`: the
  starred coefficients are the coefficients of `cos 2t`, `sin 2t`, `cos 4t`, `sin 4t` in `q_*`.
* `R0_STR02918 A B`: the radius `√(A² + B²)`, the nonnegative root.
* `P3_STR02918 A B`: the cubic `A³ - 3AB²`.
* `Jred_STR02918 A B`: the reduced coefficient `R_0⁴/48 - P_3/12 - 9R_0²/20`.
* `R0_sq_STR02918 A B`: `R_0² = A² + B²`.
* `Jred_eq_STR02918 A B`: the reduced coefficient written in `A` and `B` only.
* `Cstar_STR02918 A B`, `Dstar_STR02918 A B`, `Estar_STR02918 A`, `Fstar_STR02918 B`: the
  starred coefficients `A/2 + (B² - A²)/12`, `-B/2 - AB/6`, `-A/10`, `-B/10`.
* `qstarFn_fourier_STR02918 A B t`: the pointwise trigonometric form of `qstarFn_STR02917 A B`.

R5 notes:
1. Radius. `R_0` is read as the nonnegative root `Real.sqrt (A² + B²)`. Only `R_0²` and `R_0⁴`
  occur in the coefficient, so the reduced coefficient is a polynomial in `A` and `B` and no
  sign choice enters.
2. Starred coefficients. The specification writes `C*, D*, E*, F*` only through the displayed
  `q_*` of STR029.17. They are read as the coefficients of `cos 2t, sin 2t, cos 4t, sin 4t` in
  that function. STR029.17 gives `q_*` as a function (`qstarFn_STR02917`) and as an element of
  the carrier `E`, and no Fourier coefficient extraction from the element is formalized here.
  The values are the explicit polynomials in `(A, B)` defined in this file. The public lemma
  `..._starred_fourier` links them to `qstarFn_STR02917`. Uniqueness of the trigonometric
  representation makes these the coefficients of `q_*`.
3. Domain. The identity is read for all real `A, B, C, D, E, F`, with no bounded box, no
  compactness, no smallness of `h`, and no parameter restriction. This is the literal reading of
  "equals".
4. The polynomial. `𝒥₄` is `J4_STR02909` of STR029.09, whose defining expression matches the
  displayed formula of STR029.09 term by term. The factors `3/2`, `15/2`, `1/48`, `-1/12`, `-9/20`
  are as specified. The identity is an equality of real numbers; no rescaling by `a₀ = 4π²` and
  no optimizer-chart, weighted-carrier, AbsoluteDensity, entropy or Fisher convention enters it.
  It inherits the angular normalization of the measure `dt/(2π)` used in STR029.09.
5. Scope. The main theorem is the displayed algebraic identity only. It does not prove that
  `J_4^red` equals the actual reduced functional. The specification assigns that identification to
  STR029.17 and STR029.47, and it is not proved here. The main theorem uses only `J4_STR02909`.
  The link to `qstarFn_STR02917` is needed only for the starred Fourier lemma.
-/

namespace DGPS.Frontier.STR029

/-! ### The reduced coefficient `J_4^red` -/

/-- The radius `R_0 = √(A² + B²)`, the nonnegative root. -/
noncomputable def R0_STR02918 (A B : ℝ) : ℝ := Real.sqrt (A ^ 2 + B ^ 2)

/-- The cubic invariant `P_3 = A³ - 3AB²`. -/
noncomputable def P3_STR02918 (A B : ℝ) : ℝ := A ^ 3 - 3 * A * B ^ 2

/-- The reduced coefficient `J_4^red = R_0⁴/48 - P_3/12 - 9R_0²/20`. -/
noncomputable def Jred_STR02918 (A B : ℝ) : ℝ :=
  R0_STR02918 A B ^ 4 / 48 - P3_STR02918 A B / 12 - 9 * R0_STR02918 A B ^ 2 / 20

/-- The radius squared is `A² + B²`. -/
theorem R0_sq_STR02918 (A B : ℝ) : R0_STR02918 A B ^ 2 = A ^ 2 + B ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The reduced coefficient in `A` and `B` only. -/
theorem Jred_eq_STR02918 (A B : ℝ) :
    Jred_STR02918 A B =
      (A ^ 2 + B ^ 2) ^ 2 / 48 - (A ^ 3 - 3 * A * B ^ 2) / 12 - 9 * (A ^ 2 + B ^ 2) / 20 := by
  have h := R0_sq_STR02918 A B
  have h4 : R0_STR02918 A B ^ 4 = (A ^ 2 + B ^ 2) ^ 2 := by
    rw [← h]
    ring
  unfold Jred_STR02918 P3_STR02918
  rw [h4, h]

/-! ### The starred coefficients of STR029.17 -/

/-- The coefficient of `cos 2t` in `q_*`: `C* = A/2 + (B² - A²)/12`. -/
noncomputable def Cstar_STR02918 (A B : ℝ) : ℝ := A / 2 + (B ^ 2 - A ^ 2) / 12

/-- The coefficient of `sin 2t` in `q_*`: `D* = -B/2 - AB/6`. -/
noncomputable def Dstar_STR02918 (A B : ℝ) : ℝ := -(B / 2) - A * B / 6

/-- The coefficient of `cos 4t` in `q_*`: `E* = -A/10`. -/
noncomputable def Estar_STR02918 (A : ℝ) : ℝ := -(A / 10)

/-- The coefficient of `sin 4t` in `q_*`: `F* = -B/10`. -/
noncomputable def Fstar_STR02918 (B : ℝ) : ℝ := -(B / 10)

/-- The starred coefficients are the trigonometric coefficients of `qstarFn_STR02917`. -/
theorem qstarFn_fourier_STR02918 (A B t : ℝ) :
    qstarFn_STR02917 A B t = Cstar_STR02918 A B * Real.cos (2 * t) +
      Dstar_STR02918 A B * Real.sin (2 * t) + Estar_STR02918 A * Real.cos (4 * t) +
      Fstar_STR02918 B * Real.sin (4 * t) := by
  simp only [qstarFn_STR02917, Cstar_STR02918, Dstar_STR02918, Estar_STR02918, Fstar_STR02918]
  ring

/-! ### The main statement -/

/-- The starred coefficients are the coefficients of `cos 2t`, `sin 2t`, `cos 4t`, `sin 4t`
in the function `q_*` of STR029.17. -/
theorem str029_18_exact_reduced_quartic_square_completion_starred_fourier (A B t : ℝ) :
    qstarFn_STR02917 A B t = Cstar_STR02918 A B * Real.cos (2 * t) +
      Dstar_STR02918 A B * Real.sin (2 * t) + Estar_STR02918 A * Real.cos (4 * t) +
      Fstar_STR02918 B * Real.sin (4 * t) :=
  qstarFn_fourier_STR02918 A B t

/-- STR029.18. For all real `A, B, C, D, E, F`, the polynomial `𝒥₄` of STR029.09 equals the
reduced coefficient `J_4^red(A, B)` plus `(3/2)((C - C*)² + (D - D*)²)` plus
`(15/2)((E - E*)² + (F - F*)²)`, where `C*, D*, E*, F*` are the starred coefficients. -/
theorem str029_18_exact_reduced_quartic_square_completion (A B C D E F : ℝ) :
    J4_STR02909 A B C D E F = Jred_STR02918 A B +
      3 / 2 * ((C - Cstar_STR02918 A B) ^ 2 + (D - Dstar_STR02918 A B) ^ 2) +
      15 / 2 * ((E - Estar_STR02918 A) ^ 2 + (F - Fstar_STR02918 B) ^ 2) := by
  rw [Jred_eq_STR02918]
  unfold J4_STR02909 Cstar_STR02918 Dstar_STR02918 Estar_STR02918 Fstar_STR02918
  ring

end DGPS.Frontier.STR029
