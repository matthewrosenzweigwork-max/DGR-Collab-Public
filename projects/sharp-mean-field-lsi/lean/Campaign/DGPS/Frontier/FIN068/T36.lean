import DGPS.Frontier.FIN068.T35

/-!
Task id and title: FIN068.36, Quantitative energy matrix comparison (module
`DGPS.Frontier.FIN068.T36`).

Provides:
* `DGPS.Frontier.FIN068.fin068_36_quantitative_energy_matrix_comparison`: for real `a, b` with
  `sqrt A / 2 ≤ a ≤ 2 * sqrt A` and `|b| ≤ 1` (here `A = quarticA_FIN06803`), the matrix
  `M = [[a, b], [0, 1]]` satisfies, for every `ξ : Fin 2 → ℝ`,
  `|ξ|^2 / (1 + 8 / A) ≤ |Mᵀ ξ|^2 ≤ (4 * A + 2) * |ξ|^2`, where `|·|^2` is the sum of the squares
  of the two coordinates and `Mᵀ ξ` is `Matrix.mulVec` of the transpose.
* `DGPS.Frontier.FIN068.sqnorm_FIN06836`: the squared Euclidean norm of a vector in `Fin 2 → ℝ`
  (helper).
* `DGPS.Frontier.FIN068.transpose_mulVec_FIN06836` (helper): the two coordinates of `Mᵀ ξ`.
* `DGPS.Frontier.FIN068.frobenius_lower_FIN06836` (helper): the polynomial form of the
  inverse-transpose Frobenius bound.

Proof: the coordinates of `Mᵀ ξ` are `a ξ₀` and `b ξ₀ + ξ₁`. The upper bound is Cauchy-Schwarz
with the squared Frobenius norm `a^2 + b^2 + 1 ≤ 4 A + 2`. For the lower bound, `Mᵀ` has inverse
transpose of squared Frobenius norm `(1 + b^2) / a^2 + 1`; clearing denominators this is
`a^2 |ξ|^2 ≤ (a^2 + b^2 + 1) |Mᵀ ξ|^2`, and `a^2 ≥ A / 4`, `b^2 ≤ 1` give
`(1 + b^2) / a^2 + 1 ≤ 8 / A + 1`.

R5 notes:
* No hypothesis is added beyond the listed ones. The positivity `0 < A` used to divide comes from
  FIN068.03 (not an added hypothesis).
* `A` is the campaign constant `quarticA_FIN06803`, as in FIN068.33-.35 where `a = v_x`, `b = v_y`
  satisfy exactly these hypotheses on the fixed patch.
* The vector `ξ ∈ ℝ^2` is read as `ξ : Fin 2 → ℝ` and `|ξ|^2` as `ξ 0 ^ 2 + ξ 1 ^ 2` (the
  Euclidean squared norm); `M` is `!![a, b; 0, 1]` and `Mᵀ ξ` is `Matrix.mulVec` of its transpose.
* Bounds are non-strict, and `|ξ|^2 / (1 + 8 / A)` is written with real division as in the
  specification.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.Frontier.FIN068

/-- The squared Euclidean norm of a vector in `Fin 2 → ℝ`. -/
def sqnorm_FIN06836 (ξ : Fin 2 → ℝ) : ℝ := ξ 0 ^ 2 + ξ 1 ^ 2

/-- The coordinates of `Mᵀ ξ` for `M = [[a, b], [0, 1]]`. -/
lemma transpose_mulVec_FIN06836 (a b : ℝ) (ξ : Fin 2 → ℝ) :
    (Matrix.transpose (Matrix.of ![![a, b], ![0, 1]])).mulVec ξ 0 = a * ξ 0 ∧
    (Matrix.transpose (Matrix.of ![![a, b], ![0, 1]])).mulVec ξ 1 = b * ξ 0 + ξ 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Polynomial form of the inverse-transpose Frobenius bound
`|ξ|^2 ≤ ((1 + b^2) / a^2 + 1) |Mᵀ ξ|^2`, with denominators cleared. -/
lemma frobenius_lower_FIN06836 (a b x y : ℝ) :
    a ^ 2 * (x ^ 2 + y ^ 2) ≤ (a ^ 2 + b ^ 2 + 1) * ((a * x) ^ 2 + (b * x + y) ^ 2) := by
  nlinarith [sq_nonneg (a * (b * x + y) - b * (a * x)), sq_nonneg (a * y),
    sq_nonneg (b * (b * x + y) + a * (a * x)), sq_nonneg (a * (a * x))]

/-- Quantitative energy matrix comparison (FIN068.36). -/
theorem fin068_36_quantitative_energy_matrix_comparison (a b : ℝ)
    (ha₁ : Real.sqrt quarticA_FIN06803 / 2 ≤ a) (ha₂ : a ≤ 2 * Real.sqrt quarticA_FIN06803)
    (hb : |b| ≤ 1) (ξ : Fin 2 → ℝ) :
    sqnorm_FIN06836 ξ / (1 + 8 / quarticA_FIN06803) ≤
        sqnorm_FIN06836 ((Matrix.transpose (Matrix.of ![![a, b], ![0, 1]])).mulVec ξ) ∧
      sqnorm_FIN06836 ((Matrix.transpose (Matrix.of ![![a, b], ![0, 1]])).mulVec ξ) ≤
        (4 * quarticA_FIN06803 + 2) * sqnorm_FIN06836 ξ := by
  obtain ⟨-, -, hA, -⟩ := fin068_03_constants_exact_cancellation
  obtain ⟨h0, h1⟩ := transpose_mulVec_FIN06836 a b ξ
  have hs : 0 < Real.sqrt quarticA_FIN06803 := Real.sqrt_pos.mpr hA
  have hsq : Real.sqrt quarticA_FIN06803 ^ 2 = quarticA_FIN06803 := Real.sq_sqrt hA.le
  have hapos : 0 < a := by linarith
  have ha2 : a ^ 2 ≤ 4 * quarticA_FIN06803 := by
    rw [← hsq]; nlinarith
  have ha3 : quarticA_FIN06803 ≤ 4 * a ^ 2 := by
    rw [← hsq]; nlinarith
  have hb2 : b ^ 2 ≤ 1 := by
    have := sq_abs b
    nlinarith [abs_nonneg b]
  unfold sqnorm_FIN06836
  rw [h0, h1]
  set x := ξ 0
  set y := ξ 1
  constructor
  · have key := frobenius_lower_FIN06836 a b x y
    have hQ : 0 ≤ (a * x) ^ 2 + (b * x + y) ^ 2 := by positivity
    have hN : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have hpos : 0 < 1 + 8 / quarticA_FIN06803 := by positivity
    rw [div_le_iff₀ hpos]
    have h8 : 1 + 8 / quarticA_FIN06803 = (quarticA_FIN06803 + 8) / quarticA_FIN06803 := by
      field_simp
    rw [h8, mul_div_assoc', le_div_iff₀ hA]
    have h3 : quarticA_FIN06803 * (a ^ 2 * (x ^ 2 + y ^ 2)) ≤
        quarticA_FIN06803 * ((a ^ 2 + b ^ 2 + 1) * ((a * x) ^ 2 + (b * x + y) ^ 2)) :=
      mul_le_mul_of_nonneg_left key hA.le
    have h4 : quarticA_FIN06803 * (a ^ 2 + b ^ 2 + 1) ≤ a ^ 2 * (quarticA_FIN06803 + 8) := by
      nlinarith
    have h5 : quarticA_FIN06803 * ((a ^ 2 + b ^ 2 + 1) * ((a * x) ^ 2 + (b * x + y) ^ 2)) ≤
        a ^ 2 * (quarticA_FIN06803 + 8) * ((a * x) ^ 2 + (b * x + y) ^ 2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h4 hQ
    have h6 : a ^ 2 * (quarticA_FIN06803 * (x ^ 2 + y ^ 2)) ≤
        a ^ 2 * ((quarticA_FIN06803 + 8) * ((a * x) ^ 2 + (b * x + y) ^ 2)) := by
      nlinarith
    have h7 := le_of_mul_le_mul_left h6 (by positivity : (0 : ℝ) < a ^ 2)
    linarith
  · nlinarith [sq_nonneg (b * x + y), sq_nonneg x, sq_nonneg y, sq_nonneg (b * y - x),
      mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg x)]

end DGPS.Frontier.FIN068
