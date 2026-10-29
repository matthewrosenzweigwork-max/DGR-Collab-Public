import DGPS.Frontier.EX012.T28

/-!
# EX012.33: Explicit weighted-polynomial bound

Task id: EX012.33 (node EX012, one-site complementary range equation).
Title: Explicit weighted-polynomial bound.

Provides:
* `DGPS.Frontier.EX012.ex012_33_explicit_weighted_polynomial_bound`: for every `k : ℕ` (the
  instance `k = 2` is the space `PH α 2` of the specification), with the constant
  `C₂ = max 1 (‖c₂‖ / 12 + ‖s₂‖ / 6)`, where `c₂ = cosMode_EX01228 α k 2` and
  `s₂ = sinMode_EX01228 α k 2`, the conjunction `1 ≤ C₂` and, for all real `a b τ`,
  `‖((τ - a² + b²) / 12) • c₂ - ((a * b) / 6) • s₂‖ ≤ C₂ * (|a| + |b| + √|τ|)²`.
* `DGPS.Frontier.EX012.C2_EX01233`: the constant `max 1 (‖c₂‖ / 12 + ‖s₂‖ / 6)` in `PH α k`.
* Helper lemmas (all suffixed `_EX01233`): `abs_sub_sq_le_EX01233` (`|τ - a² + b²| ≤ |τ| + a² + b²`),
  `sum_sq_le_EX01233` (`|τ| + a² + b² ≤ (|a| + |b| + √|τ|)²`), `ab_le_EX01233`
  (`|a| |b| ≤ (|a| + |b| + √|τ|)²`), and `one_le_C2_EX01233`.

R5 notes:
* No hypothesis is added beyond the `[HolderExponent α]` instance of the campaign (the form of
  `0 < α < 1`) that `PH α k` and `cosMode_EX01228`/`sinMode_EX01228` already require. The
  statement has no other hypotheses.
* The specification writes `w₂(a, b, τ)` without fixing a space. It is read as an element of
  `PH α k` for an arbitrary `k`, the same generality as EX012.28. The bound therefore covers
  `PH α 2` as the special case `k = 2`. The norms `‖c₂‖`, `‖s₂‖` are taken in the same `PH α k`.
* `C₂` is the specification's `max(1, ‖c₂‖/12 + ‖s₂‖/6)`, written with `max 1 (…)`. Its
  positivity (`1 ≤ C₂`) is part of the conclusion, as the consuming task EX012.34 needs `C₂ ≥ 1`.
* `r = |a| + |b| + √|τ|` is written out literally; `√|τ|` is `Real.sqrt |τ|`, which is
  nonnegative for every real `τ`, so no sign restriction on `τ` (negative `τ` included) is used.
* The domain of `(a, b, τ)` is all of `ℝ × ℝ × ℝ`; no restriction to small parameters is made.
  The specification's "`|τ| ≤ r²`, `a² + b² ≤ r²`, `|ab| ≤ r²`, `|τ| + a² + b² ≤ r²`" are proved
  as lemmas, with the sharper sum bound used for the main estimate.
* The specification's "triangle inequality" step is `norm_sub_le` and `norm_smul`, with the
  scalar coefficients bounded by absolute values; no operator-norm argument is needed.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section Elementary

theorem abs_sub_sq_le_EX01233 (a b τ : ℝ) : |τ - a ^ 2 + b ^ 2| ≤ |τ| + a ^ 2 + b ^ 2 := by
  have h1 : |τ - a ^ 2 + b ^ 2| ≤ |τ| + |b ^ 2 - a ^ 2| := by
    rw [show τ - a ^ 2 + b ^ 2 = τ + (b ^ 2 - a ^ 2) by ring]
    exact abs_add_le τ (b ^ 2 - a ^ 2)
  have h2 : |b ^ 2 - a ^ 2| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  linarith

theorem sum_sq_le_EX01233 (a b τ : ℝ) :
    |τ| + a ^ 2 + b ^ 2 ≤ (|a| + |b| + Real.sqrt |τ|) ^ 2 := by
  have hs : Real.sqrt |τ| ^ 2 = |τ| := Real.sq_sqrt (abs_nonneg τ)
  have hs0 : 0 ≤ Real.sqrt |τ| := Real.sqrt_nonneg _
  nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b), mul_nonneg (abs_nonneg a) hs0,
    mul_nonneg (abs_nonneg b) hs0, sq_abs a, sq_abs b]

theorem ab_le_EX01233 (a b τ : ℝ) : |a| * |b| ≤ (|a| + |b| + Real.sqrt |τ|) ^ 2 := by
  have hs : Real.sqrt |τ| ^ 2 = |τ| := Real.sq_sqrt (abs_nonneg τ)
  have hs0 : 0 ≤ Real.sqrt |τ| := Real.sqrt_nonneg _
  nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b), mul_nonneg (abs_nonneg a) hs0,
    mul_nonneg (abs_nonneg b) hs0, sq_nonneg (Real.sqrt |τ|), sq_abs a, sq_abs b,
    abs_nonneg τ]

end Elementary

section Main

variable (α : ℝ) [HolderExponent α]

/-- The constant `C₂ = max 1 (‖c₂‖ / 12 + ‖s₂‖ / 6)` of the specification, in `PH α k`. -/
noncomputable def C2_EX01233 (k : ℕ) : ℝ :=
  max 1 (‖cosMode_EX01228 α k 2‖ / 12 + ‖sinMode_EX01228 α k 2‖ / 6)

theorem one_le_C2_EX01233 (k : ℕ) : 1 ≤ C2_EX01233 α k :=
  le_max_left _ _

/-- **EX012.33.** With `C₂ = max 1 (‖c₂‖ / 12 + ‖s₂‖ / 6)` and `r = |a| + |b| + √|τ|`,
`1 ≤ C₂` and `‖w₂(a, b, τ)‖ ≤ C₂ r²`, where
`w₂(a, b, τ) = ((τ - a² + b²) / 12) c₂ - ((a b) / 6) s₂` in `PH α k`. -/
theorem ex012_33_explicit_weighted_polynomial_bound (k : ℕ) :
    1 ≤ C2_EX01233 α k ∧
      ∀ a b τ : ℝ,
        ‖((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α k 2 -
            ((a * b) / 6) • sinMode_EX01228 α k 2‖ ≤
          C2_EX01233 α k * (|a| + |b| + Real.sqrt |τ|) ^ 2 := by
  refine ⟨one_le_C2_EX01233 α k, fun a b τ => ?_⟩
  have hA : |τ - a ^ 2 + b ^ 2| ≤ (|a| + |b| + Real.sqrt |τ|) ^ 2 :=
    (abs_sub_sq_le_EX01233 a b τ).trans (sum_sq_le_EX01233 a b τ)
  have hB : |a| * |b| ≤ (|a| + |b| + Real.sqrt |τ|) ^ 2 := ab_le_EX01233 a b τ
  have hp : |(τ - a ^ 2 + b ^ 2) / 12| ≤ (|a| + |b| + Real.sqrt |τ|) ^ 2 / 12 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    gcongr
  have hq : |(a * b) / 6| ≤ (|a| + |b| + Real.sqrt |τ|) ^ 2 / 6 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_mul]
    gcongr
  have htri : ‖((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α k 2 -
      ((a * b) / 6) • sinMode_EX01228 α k 2‖ ≤
      |(τ - a ^ 2 + b ^ 2) / 12| * ‖cosMode_EX01228 α k 2‖ +
        |(a * b) / 6| * ‖sinMode_EX01228 α k 2‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc ‖((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α k 2 -
          ((a * b) / 6) • sinMode_EX01228 α k 2‖
      ≤ |(τ - a ^ 2 + b ^ 2) / 12| * ‖cosMode_EX01228 α k 2‖ +
          |(a * b) / 6| * ‖sinMode_EX01228 α k 2‖ := htri
    _ ≤ ((|a| + |b| + Real.sqrt |τ|) ^ 2 / 12) * ‖cosMode_EX01228 α k 2‖ +
          ((|a| + |b| + Real.sqrt |τ|) ^ 2 / 6) * ‖sinMode_EX01228 α k 2‖ := by
        gcongr
    _ = (‖cosMode_EX01228 α k 2‖ / 12 + ‖sinMode_EX01228 α k 2‖ / 6) *
          (|a| + |b| + Real.sqrt |τ|) ^ 2 := by ring
    _ ≤ C2_EX01233 α k * (|a| + |b| + Real.sqrt |τ|) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end Main

end DGPS.Frontier.EX012
