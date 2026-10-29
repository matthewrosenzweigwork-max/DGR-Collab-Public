import DGPS.Frontier.STR029.T09

/-!
# STR029.10: Strict trial below the endpoint

Task id: STR029.10. Title: Strict trial below the endpoint.
Prerequisite: STR029.09 (module `DGPS.Frontier.STR029.T09`).

Provides:
* `DGPS.Frontier.STR029.str029_10_strict_trial_below_endpoint`: for the trial function
  `u_h(t) = 2h cos t + h²((2/3) cos 2t - (1/5) cos 4t)` there is `0 < δ ≤ 1/1000` such that every
  real `h` with `0 < |h| < δ` has positive chart entropy `H_h(ρ(h,u_h))` and satisfies
  `I_h(ρ(h,u_h)) / (2 H_h(ρ(h,u_h))) < 1 - h²`.
* `DGPS.Frontier.STR029.trial_fn_eq_STR02910`: the trial function equals `uFun_STR02945` at the
  coefficients `(A, B, C, D, E, F) = (2, 0, 2/3, 0, -1/5, 0)`.
* `DGPS.Frontier.STR029.J4_trial_STR02910`: the fourth-order coefficient `𝒥₄` at those coefficients
  equals `-32/15`.
* `DGPS.Frontier.STR029.trial_bounds_STR02910`: the STR029.09 expansions for the trial function,
  `I - 2H = h⁴ (-32/15) + O(h⁵)` and `H = h² + O(h³)`, with a constant `K` and a step `h0`.

R5 notes:
1. Fisher term. `I_h(ρ(h,u))` is read as `chartFisher_STR02945 h u`, the integral
   `∫ u'² ρ(h,u) dm` that the preamble gives in the logarithmic chart. The angular definition
   `4 ∫ g'² q_h dm` is not formalized here; its identification with the chart integral belongs to
   STR029.01 (the same reading as STR029.09, note 1).
2. Entropy term. `H_h(ρ)` is read as `chartEntropy_STR02945 h u = ∫ g² log(g²) q_h dm` with
   `g² = ρ / q_h`, using `Real.log`. The convention `z log z = 0` at `z = 0` is not needed, because
   the ratio `g²` is positive for every `h` in the range of this statement.
3. Measure and normalization. The probability measure `dm = dt/(2π)` on one period is the
   normalized integral `normInt_STR02933` over `(0, 2π]`, and `ρ(h,u)` is normalized by it.
4. Derivative. `u'` in the Fisher term is Lean's `deriv` of the explicit smooth trial function. It is
   the classical derivative, which is the only derivative needed here; no weak derivative is used.
5. Range of h. The specification's `0 < |h| < δ` is kept literally, so negative `h` is included.
   The constant `δ` depends only on the fixed trial function, not on any parameter.
6. Constants. The constants come from STR029.09 applied with radius `R = 2`, which contains the
   coefficients `2, 0, 2/3, 0, -1/5, 0`. The step is `δ = min (min h0 (1/1000)) (1/(45 (K + 1)))`, where
   `h0` and `K` are existential. The explicit constant `C_tr` of the specification's Taylor route is
   not used; the O-bounds of STR029.09 are used directly, so the route differs from the
   specification while the statement is the same.
7. Coefficients. The values `𝒥₄ = -32/15` and `(A² + B²)/4 = 1` are evaluated from the closed
   formulas of STR029.09. No smoothness in `h` of `J` or `H` is assumed.
8. Quotient. The quotient is the real division `I / (2 H)`. Positivity of `H` is proved first, so the
   division is the intended one and the quotient inequality is proved as `I < (1 - h²) (2 H)`.
9. Clause `δ ≤ 1/1000` is a separate clause of the existential, as the specification's
   `0 < δ ≤ 1/1000` requires.
-/

namespace DGPS.Frontier.STR029

/-- The trial function equals the STR029.45 argument `u = h p + h² q` at the coefficients
`(A, B, C, D, E, F) = (2, 0, 2/3, 0, -1/5, 0)`. -/
theorem trial_fn_eq_STR02910 (h : ℝ) :
    (fun t : ℝ => 2 * h * Real.cos t +
        h ^ 2 * ((2 / 3) * Real.cos (2 * t) - (1 / 5) * Real.cos (4 * t))) =
      uFun_STR02945 2 0 (2 / 3) 0 (-1 / 5) 0 h := by
  funext t
  simp only [uFun_STR02945, pFun_STR02945, qFun_STR02945]
  ring

/-- The fourth-order coefficient `𝒥₄` at the trial coefficients equals `-32/15`. -/
theorem J4_trial_STR02910 : J4_STR02909 2 0 (2 / 3) 0 (-1 / 5) 0 = -32 / 15 := by
  unfold J4_STR02909
  norm_num

/-- The STR029.09 expansions for the trial function: the functional is `h⁴ (-32/15) + O(h⁵)`
and the entropy is `h² + O(h³)`, with one constant `K` for all `|h| ≤ h0`. -/
theorem trial_bounds_STR02910 :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| ≤ h0 →
      |chartFisher_STR02945 h (uFun_STR02945 2 0 (2 / 3) 0 (-1 / 5) 0 h) -
          2 * chartEntropy_STR02945 h (uFun_STR02945 2 0 (2 / 3) 0 (-1 / 5) 0 h) -
          h ^ 4 * (-32 / 15)| ≤ K * |h| ^ 5 ∧
      |chartEntropy_STR02945 h (uFun_STR02945 2 0 (2 / 3) 0 (-1 / 5) 0 h) - h ^ 2| ≤
          K * |h| ^ 3 := by
  obtain ⟨h0, hh0, K, hK, hT9⟩ :=
    str029_09_fourth_order_coefficient_explicit_information_functional 2
  refine ⟨h0, hh0, K, hK, fun h hle => ?_⟩
  obtain ⟨hJ, hH, -⟩ := hT9 2 0 (2 / 3) 0 (-1 / 5) 0 (by norm_num [abs_le])
    (by norm_num [abs_le]) (by norm_num [abs_le]) (by norm_num [abs_le])
    (by norm_num [abs_le]) (by norm_num [abs_le]) h hle
  rw [J4_trial_STR02910] at hJ
  have e2 : ((2 : ℝ) ^ 2 + (0 : ℝ) ^ 2) / 4 = 1 := by norm_num
  rw [e2, mul_one] at hH
  unfold Jzero_STR02909 at hJ
  exact ⟨hJ, hH⟩

/-- STR029.10. There is `0 < δ ≤ 1/1000` such that for `0 < |h| < δ` the trial `u_h` has positive
entropy and the quotient `I_h / (2 H_h)` is below `1 - h²`. -/
theorem str029_10_strict_trial_below_endpoint :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 1000 ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ →
        0 < chartEntropy_STR02945 h (fun t : ℝ => 2 * h * Real.cos t +
            h ^ 2 * ((2 / 3) * Real.cos (2 * t) - (1 / 5) * Real.cos (4 * t))) ∧
        chartFisher_STR02945 h (fun t : ℝ => 2 * h * Real.cos t +
            h ^ 2 * ((2 / 3) * Real.cos (2 * t) - (1 / 5) * Real.cos (4 * t))) /
          (2 * chartEntropy_STR02945 h (fun t : ℝ => 2 * h * Real.cos t +
            h ^ 2 * ((2 / 3) * Real.cos (2 * t) - (1 / 5) * Real.cos (4 * t)))) <
          1 - h ^ 2 := by
  obtain ⟨h0, hh0, K, hK, hB⟩ := trial_bounds_STR02910
  refine ⟨min (min h0 (1 / 1000)) (1 / (45 * (K + 1))),
    lt_min (lt_min hh0 (by norm_num)) (div_pos one_pos (by linarith)),
    le_trans (min_le_left _ _) (min_le_right _ _), ?_⟩
  intro h hpos hlt
  have hle : |h| ≤ h0 := le_trans (le_trans hlt.le (min_le_left _ _)) (min_le_left _ _)
  have hlt2 : |h| < 1 / (45 * (K + 1)) := lt_of_lt_of_le hlt (min_le_right _ _)
  have hK1 : |h| * (45 * (K + 1)) < 1 := (lt_div_iff₀ (by linarith)).mp hlt2
  obtain ⟨hJ, hH⟩ := hB h hle
  rw [trial_fn_eq_STR02910 h]
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have hquart : h ^ 4 = |h| ^ 4 := by
    calc h ^ 4 = (h ^ 2) ^ 2 := by ring
      _ = (|h| ^ 2) ^ 2 := by rw [hsq]
      _ = |h| ^ 4 := by ring
  rw [hquart] at hJ
  rw [hsq] at hH ⊢
  obtain ⟨hJ1, hJ2⟩ := abs_le.mp hJ
  obtain ⟨hH1, hH2⟩ := abs_le.mp hH
  set Ifi := chartFisher_STR02945 h (uFun_STR02945 2 0 (2 / 3) 0 (-1 / 5) 0 h) with hIdef
  set Hent := chartEntropy_STR02945 h (uFun_STR02945 2 0 (2 / 3) 0 (-1 / 5) 0 h) with hHdef
  have hKe : K * |h| < 1 / 45 := by linarith
  have hpow : 0 < |h| ^ 2 * (1 - K * |h|) := mul_pos (pow_pos hpos 2) (by linarith)
  have hHpos : 0 < Hent := by linarith
  refine ⟨hHpos, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  have hprod : Hent * |h| ^ 2 ≤ (|h| ^ 2 + K * |h| ^ 3) * |h| ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hneg : |h| ^ 4 * (3 * K * |h| - 2 / 15) < 0 :=
    mul_neg_of_pos_of_neg (pow_pos hpos 4) (by linarith)
  linarith

end DGPS.Frontier.STR029
