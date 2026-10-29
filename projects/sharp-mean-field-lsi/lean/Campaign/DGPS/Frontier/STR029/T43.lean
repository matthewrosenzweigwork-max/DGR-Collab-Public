import DGPS.Foundations.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Moments.Variance

/-!
# STR029.43: Entropy expansion relative to variance

Task id: STR029.43. Title: Entropy expansion relative to variance (node STR029, size L, leaf formalization).

Provides:
* `DGPS.Frontier.STR029.str029_43_entropy_expansion_relative_variance`: on a probability space `(Ω, μ)`, for a
  measurable `g : Ω → ℝ` with `g ≥ 0` a.e., `∫ g² dμ = 1` and `|g - 1| ≤ ε` a.e. with `ε ≤ 1/4`, the entropy
  `Ent_μ(g²)` and the variance `Var_μ(g)` satisfy `|Ent_μ(g²) - 2 Var_μ(g)| ≤ 4 ε Var_μ(g)`.
  Here `Ent_μ` is `DGPS.homogeneousEntropy` (DEF004) and `Var_μ` is `ProbabilityTheory.variance`.
* `DGPS.Frontier.STR029.log_taylor3_STR02943`: for `|z| ≤ 1/4`, `|log(1+z) - (z - z²/2 + z³/3)| ≤ (4/3)|z|⁴`.
* `DGPS.Frontier.STR029.remainder_bound_STR02943`: for `|z| ≤ 1/4`, `|(1+z)² log((1+z)²) - (2z + 3z²)| ≤ 2|z|³`.
* `DGPS.Frontier.STR029.remainder_bound_g_STR02943`: the bound of the previous line with `1 + z` written as `g`.
* `DGPS.Frontier.STR029.integrable_of_abs_le_STR02943`: a measurable function with `|f| ≤ C` a.e. is integrable
  on a probability space.
* `DGPS.Frontier.STR029.final_real_STR02943`: the closing real inequality from `E = 2M + r`, `|r| ≤ 2εM`,
  `0 ≤ M ≤ ε²` and `0 ≤ ε ≤ 1/4`.

R5 notes:
* Carrier: an arbitrary measurable space `Ω` with a probability measure `μ`, as the spec says ("on any probability
  space"). It is not specialized to the torus, the optimizer chart, the weighted carriers or `AbsoluteDensity` of
  STR029. No library object of the node is used.
* Entropy: `Ent_μ(v) = DGPS.homogeneousEntropy μ v`, the campaign's DEF004, which is `ℝ≥0∞`-valued. The statement
  applies `.toReal`. The value is finite: it equals `∫ g² log g² dμ`, which is integrable, and it is `≥ 0`, which
  the proof derives. So `.toReal` loses no information. At mass one DEF004 is `∫ (v log v - v + 1)`, and this equals
  `∫ v log v` because `∫ v = 1`.
* Variance: `ProbabilityTheory.variance g μ` (Mathlib, `(evariance g μ).toReal`). The proof uses
  `ProbabilityTheory.variance_eq_sub`, which needs `g ∈ L²`; this holds because `g` is essentially bounded.
* Hypotheses: `0 ≤ g` a.e. is listed in the spec. It is used to show `g² ≥ 0` a.e., which DEF004 requires. The
  essential bound `‖g - 1‖∞ ≤ ε` is read as `∀ᵐ x ∂μ, |g x - 1| ≤ ε`. The spec does not say `ε ≥ 0`; the proof
  derives it, because a probability measure is nonzero and the bound holds a.e.
* Measurability: "measurable real function" is read as `Measurable g` (no completion or `AEMeasurable` weakening).
* Taylor step: the spec's "Taylor formula with a bounded third derivative" is not used as a black box. The scalar
  remainder comes from the logarithm series with explicit remainder, `Real.abs_log_sub_add_sum_range_le` at `n = 3`.
  The constant obtained is `2`. The spec's `8/9` is also enough, and the closing inequality tolerates any constant up
  to about `3.8` when `ε ≤ 1/4`.
-/

open MeasureTheory Filter ProbabilityTheory

namespace DGPS.Frontier.STR029

/-- Logarithm series with remainder: for `|z| ≤ 1/4`, `|log(1+z) - (z - z²/2 + z³/3)| ≤ (4/3)|z|⁴`. -/
theorem log_taylor3_STR02943 {z : ℝ} (hz : |z| ≤ 1 / 4) :
    |Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)| ≤ 4 / 3 * |z| ^ 4 := by
  have h1 : |-z| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 3
  have hsum : (∑ i ∈ Finset.range 3, (-z) ^ (i + 1) / ((i : ℝ) + 1))
      = -z + z ^ 2 / 2 - z ^ 3 / 3 := by
    simp [Finset.sum_range_succ]
    ring
  have e : Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)
      = (∑ i ∈ Finset.range 3, (-z) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -z) := by
    rw [hsum, sub_neg_eq_add]
    ring
  rw [e]
  refine h.trans ?_
  have hpos : 0 < 1 - |z| := by linarith [abs_nonneg z]
  have ha : 0 ≤ |z| ^ 4 := by positivity
  rw [abs_neg, div_le_iff₀ hpos]
  nlinarith [mul_nonneg ha (by linarith : (0 : ℝ) ≤ 1 / 4 - |z|)]

/-- Scalar remainder: for `|z| ≤ 1/4`, `|(1+z)² log((1+z)²) - (2z + 3z²)| ≤ 2|z|³`. -/
theorem remainder_bound_STR02943 {z : ℝ} (hz : |z| ≤ 1 / 4) :
    |(1 + z) ^ 2 * Real.log ((1 + z) ^ 2) - (2 * z + 3 * z ^ 2)| ≤ 2 * |z| ^ 3 := by
  have hL := log_taylor3_STR02943 hz
  have hlog2 : Real.log ((1 + z) ^ 2) = 2 * Real.log (1 + z) := by
    rw [Real.log_pow]
    norm_num
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have hsq : (1 + z) ^ 2 ≤ 25 / 16 := by nlinarith
  have hP : |2 / 3 + z / 3 + 2 * z ^ 2 / 3| ≤ 19 / 24 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg z], by nlinarith⟩
  have hR : (1 + z) ^ 2 * Real.log ((1 + z) ^ 2) - (2 * z + 3 * z ^ 2)
      = z ^ 3 * (2 / 3 + z / 3 + 2 * z ^ 2 / 3)
        + 2 * (1 + z) ^ 2 * (Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)) := by
    rw [hlog2]
    ring
  have h3 : 0 ≤ |z| ^ 3 := by positivity
  have h1 : |z ^ 3 * (2 / 3 + z / 3 + 2 * z ^ 2 / 3)| ≤ 19 / 24 * |z| ^ 3 := by
    rw [abs_mul, abs_pow]
    nlinarith [mul_le_mul_of_nonneg_left hP h3]
  have h2 : |2 * (1 + z) ^ 2 * (Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3))|
      ≤ 25 / 6 * |z| ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ 2)]
    have := mul_le_mul (show 2 * (1 + z) ^ 2 ≤ 2 * (25 / 16) by linarith) hL
      (abs_nonneg _) (by norm_num)
    linarith
  have h4 : |z| ^ 4 ≤ 1 / 4 * |z| ^ 3 := by
    have : |z| ^ 4 = |z| ^ 3 * |z| := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hz h3]
  rw [hR]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- The remainder bound in the variable `g = 1 + z`: for `|g - 1| ≤ 1/4`,
`|g² log g² - (2(g-1) + 3(g-1)²)| ≤ 2|g-1|³`. -/
theorem remainder_bound_g_STR02943 {g : ℝ} (hg : |g - 1| ≤ 1 / 4) :
    |g ^ 2 * Real.log (g ^ 2) - (2 * (g - 1) + 3 * (g - 1) ^ 2)| ≤ 2 * |g - 1| ^ 3 := by
  have h := remainder_bound_STR02943 hg
  rw [show 1 + (g - 1) = g by ring] at h
  exact h

/-- A measurable function with `|f| ≤ C` almost everywhere is integrable on a probability space. -/
theorem integrable_of_abs_le_STR02943 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ᵐ x ∂μ, |f x| ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (h.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)

/-- The closing real inequality: from `E = 2M + r` with `|r| ≤ 2εM`, `0 ≤ M ≤ ε²` and `0 ≤ ε ≤ 1/4`,
`E ≥ 0` and `|E - 2(M - M²/4)| ≤ 4ε(M - M²/4)`. -/
theorem final_real_STR02943 {E M r ε : ℝ} (hε0 : 0 ≤ ε) (hε4 : ε ≤ 1 / 4) (hM0 : 0 ≤ M)
    (hMε : M ≤ ε ^ 2) (hr : |r| ≤ 2 * ε * M) (hE : E = 2 * M + r) :
    0 ≤ E ∧ |E - 2 * (M - M ^ 2 / 4)| ≤ 4 * ε * (M - M ^ 2 / 4) := by
  have hr' := abs_le.mp hr
  have hεM : ε * M ≤ ε * ε ^ 2 := mul_le_mul_of_nonneg_left hMε hε0
  have hkey1 : 0 ≤ M * (2 * ε - M / 2 - ε * M) := by
    apply mul_nonneg hM0
    nlinarith
  have hkey2 : 0 ≤ M * (2 * ε + M / 2 - ε * M) := by
    apply mul_nonneg hM0
    nlinarith
  subst hE
  constructor
  · nlinarith [mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ 1 - ε)]
  · rw [abs_le]
    constructor <;> nlinarith [hkey1, hkey2]

/-- Entropy expansion relative to variance (STR029.43). On a probability space, for a measurable `g ≥ 0` a.e.
with `∫ g² = 1` and `|g - 1| ≤ ε ≤ 1/4` a.e., `|Ent(g²) - 2 Var(g)| ≤ 4 ε Var(g)`. -/
theorem str029_43_entropy_expansion_relative_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ) (hgm : Measurable g)
    (hg0 : 0 ≤ᵐ[μ] g) (hnorm : ∫ x, g x ^ 2 ∂μ = 1) {ε : ℝ}
    (hε : ∀ᵐ x ∂μ, |g x - 1| ≤ ε) (hε4 : ε ≤ 1 / 4) :
    |(DGPS.homogeneousEntropy μ (fun x => g x ^ 2)).toReal - 2 * variance g μ|
      ≤ 4 * ε * variance g μ := by
  have hε0 : 0 ≤ ε := by
    obtain ⟨x, hx⟩ := hε.exists
    exact (abs_nonneg _).trans hx
  have hq : ∀ᵐ x ∂μ, |g x - 1| ≤ 1 / 4 := hε.mono fun x hx => hx.trans hε4
  have hsq : ∀ᵐ x ∂μ, |(g x - 1) ^ 2| ≤ ε ^ 2 := hε.mono fun x hx => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
  -- integrable pieces
  have hz1 : Integrable (fun x => g x - 1) μ :=
    integrable_of_abs_le_STR02943 (hgm.sub_const 1) hε
  have hz2 : Integrable (fun x => (g x - 1) ^ 2) μ :=
    integrable_of_abs_le_STR02943 ((hgm.sub_const 1).pow_const 2) hsq
  have hP : Integrable (fun x => 2 * (g x - 1) + 3 * (g x - 1) ^ 2) μ :=
    (hz1.const_mul 2).add (hz2.const_mul 3)
  have hRm : Measurable (fun x => g x ^ 2 * Real.log (g x ^ 2)
      - (2 * (g x - 1) + 3 * (g x - 1) ^ 2)) := by
    fun_prop
  have hRb : Integrable (fun x => 2 * ε * (g x - 1) ^ 2) μ := hz2.const_mul (2 * ε)
  -- pointwise remainder bound, a.e.
  have hRpt : ∀ᵐ x ∂μ, ‖g x ^ 2 * Real.log (g x ^ 2)
      - (2 * (g x - 1) + 3 * (g x - 1) ^ 2)‖ ≤ 2 * ε * (g x - 1) ^ 2 :=
    (hε.and hq).mono fun x hx => by
      obtain ⟨hx1, hx2⟩ := hx
      have hc : |g x - 1| ^ 3 ≤ ε * (g x - 1) ^ 2 := by
        have h2 : |g x - 1| ^ 2 = (g x - 1) ^ 2 := sq_abs _
        calc |g x - 1| ^ 3 = |g x - 1| * (g x - 1) ^ 2 := by rw [← h2]; ring
          _ ≤ ε * (g x - 1) ^ 2 := mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)
      have h := remainder_bound_g_STR02943 hx2
      rw [Real.norm_eq_abs]
      linarith
  have hR : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)
      - (2 * (g x - 1) + 3 * (g x - 1) ^ 2)) μ :=
    Integrable.mono' hRb hRm.aestronglyMeasurable hRpt
  have hphi : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) μ := by
    refine (hP.add hR).congr (Eventually.of_forall fun x => ?_)
    show (2 * (g x - 1) + 3 * (g x - 1) ^ 2)
        + (g x ^ 2 * Real.log (g x ^ 2) - (2 * (g x - 1) + 3 * (g x - 1) ^ 2))
        = g x ^ 2 * Real.log (g x ^ 2)
    ring
  -- moment identities
  have hint_eq : ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂μ
      = (∫ x, (2 * (g x - 1) + 3 * (g x - 1) ^ 2) ∂μ)
        + ∫ x, (g x ^ 2 * Real.log (g x ^ 2) - (2 * (g x - 1) + 3 * (g x - 1) ^ 2)) ∂μ := by
    rw [← integral_add hP hR]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hPint : ∫ x, (2 * (g x - 1) + 3 * (g x - 1) ^ 2) ∂μ
      = 2 * (∫ x, (g x - 1) ∂μ) + 3 * ∫ x, (g x - 1) ^ 2 ∂μ := by
    rw [integral_add (hz1.const_mul 2) (hz2.const_mul 3), integral_const_mul, integral_const_mul]
  have hIM : 2 * (∫ x, (g x - 1) ∂μ) + ∫ x, (g x - 1) ^ 2 ∂μ = 0 := by
    have hA : Integrable (fun x => (2 * (g x - 1) + (g x - 1) ^ 2)) μ :=
      (hz1.const_mul 2).add hz2
    have h1 : ∫ x, g x ^ 2 ∂μ = ∫ x, ((1 : ℝ) + (2 * (g x - 1) + (g x - 1) ^ 2)) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [integral_add (integrable_const (1 : ℝ)) hA, integral_add (hz1.const_mul 2) hz2,
      integral_const_mul, hnorm] at h1
    have hc : ∫ x, (1 : ℝ) ∂μ = 1 := by simp
    linarith
  have hgI : ∫ x, g x ∂μ = 1 + ∫ x, (g x - 1) ∂μ := by
    have h1 : ∫ x, g x ∂μ = ∫ x, ((g x - 1) + 1) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [h1, integral_add hz1 (integrable_const (1 : ℝ))]
    simp [add_comm]
  -- the variance and the entropy in closed form
  have hmem : MemLp g 2 μ := by
    refine MemLp.of_bound hgm.aestronglyMeasurable (5 / 4) (hq.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := abs_le.mp hx
    constructor <;> linarith
  have hvar0 : variance g μ = (∫ x, g x ^ 2 ∂μ) - (∫ x, g x ∂μ) ^ 2 :=
    variance_eq_sub hmem
  have hvar : variance g μ = (∫ x, (g x - 1) ^ 2 ∂μ) - (∫ x, (g x - 1) ^ 2 ∂μ) ^ 2 / 4 := by
    rw [hvar0, hnorm, hgI]
    linear_combination (-1 + (∫ x, (g x - 1) ^ 2 ∂μ) / 4 - (∫ x, (g x - 1) ∂μ) / 2) * hIM
  have hv0 : 0 ≤ᵐ[μ] fun x => g x ^ 2 := hg0.mono fun x hx => pow_nonneg hx 2
  have hvint : Integrable (fun x => g x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mp hmem
  have hEnt : DGPS.homogeneousEntropy μ (fun x => g x ^ 2)
      = ENNReal.ofReal (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂μ) := by
    rw [DGPS.homogeneousEntropy_eq_formula hv0 hvint hphi, hnorm, Real.log_one, mul_zero, sub_zero]
  have hM0 : 0 ≤ ∫ x, (g x - 1) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hMle : ∫ x, (g x - 1) ^ 2 ∂μ ≤ ε ^ 2 := by
    have h := integral_mono_ae hz2 (integrable_const (ε ^ 2))
      (hsq.mono fun x hx => (le_abs_self _).trans hx)
    simpa using h
  have hr : |∫ x, (g x ^ 2 * Real.log (g x ^ 2) - (2 * (g x - 1) + 3 * (g x - 1) ^ 2)) ∂μ|
      ≤ 2 * ε * ∫ x, (g x - 1) ^ 2 ∂μ := by
    have h := norm_integral_le_of_norm_le hRb hRpt
    rw [integral_const_mul, Real.norm_eq_abs] at h
    exact h
  have hEeq : ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂μ
      = 2 * (∫ x, (g x - 1) ^ 2 ∂μ) + ∫ x, (g x ^ 2 * Real.log (g x ^ 2)
        - (2 * (g x - 1) + 3 * (g x - 1) ^ 2)) ∂μ := by
    rw [hint_eq, hPint]
    linarith [hIM]
  obtain ⟨hE0, hfin⟩ := final_real_STR02943 hε0 hε4 hM0 hMle hr hEeq
  rw [hEnt, ENNReal.toReal_ofReal hE0, hvar]
  exact hfin

end DGPS.Frontier.STR029
