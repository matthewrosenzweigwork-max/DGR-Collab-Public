import DGPS.Frontier.LIP051.T27

/-!
## LIP051.28 — Section coefficient as an L² contraction

Provides:

* `DGPS.Frontier.LIP051.lip051_28_section_coefficient_contraction`: for a probability measure
  `μ`, a measurable real `F` on `α × α` with `F ∈ L²(μ ⊗ μ)` and a measurable `e` with
  `∫ e * e dμ = 1`, the section coefficient `g y = ∫ F (x, y) * e x dμ(x)` for `y ∈ A`
  (and `0` off `A`, with `A` the set of LIP051.27) is measurable, lies in `L²(μ)`, satisfies
  `|g y| ^ 2 ≤ a0 y` almost everywhere (`a0` of LIP051.27), and
  `‖g‖_{L²(μ)} ≤ ‖F‖_{L²(μ ⊗ μ)}`.
* `DGPS.Frontier.LIP051.integral_mul_self_LIP05128` (helper): `∫ f * f dμ` is the squared
  `L²` seminorm for `f ∈ L²(μ)`.
* `DGPS.Frontier.LIP051.integral_mul_sq_le_LIP05128` (helper): Cauchy–Schwarz,
  `(∫ f * g dμ) ^ 2 ≤ ‖f‖₂² ‖g‖₂²` for `f, g ∈ L²(μ)`.
* `DGPS.Frontier.LIP051.memLp_of_integral_mul_self_eq_one_LIP05128` (helper): a measurable
  `e` with `∫ e * e dμ = 1` lies in `L²(μ)`.
* `DGPS.Frontier.LIP051.section_integral_sq_le_LIP05128` (helper): the sectionwise
  Cauchy–Schwarz bound `(∫ F (x, y) * e x dμ(x)) ^ 2 ≤ (a y).toReal` for `y` in `A`.

R5 notes (interpretive readings and design choices; the statement is not strengthened beyond
what is listed, and no hypothesis is added):

1. Generality. As in LIP051.27, the theorem is stated for an arbitrary measurable space `α`
   with a probability measure `μ` (`[IsProbabilityMeasure μ]`). No `Spec`, `KData`, `Hw`,
   Wick object or Torus appears. The mode-zero / positive-mode indexing of FD-002 is not
   touched: no index `i` occurs. The function `e` stands for any one of the norm-one measurable
   representatives `f i` of LIP051.25, and the hypothesis used is only the diagonal moment
   `∫ e * e dμ = 1` of that unit, so the result applies to every index `i` (zero or positive).
2. The function `e`. "Norm-one measurable function" is read as `Measurable e` together with
   `∫ x, e x * e x ∂μ = 1`, the exact form of the diagonal moment in LIP051.25. The hypothesis
   `MemLp e 2 μ` that LIP051.25 also supplies is not assumed here: it follows from
   `Integrable (e * e)`, which in turn follows from `∫ e * e dμ = 1 ≠ 0` (a non-integrable
   function has Bochner integral zero). Thus the hypotheses are weaker than the produced data.
3. The kernel `F` and the data `a`, `A`, `a0` are exactly those of LIP051.27: `Measurable F`,
   `MemLp F 2 (μ.prod μ)`, `a y = ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ`, `A = {y | a y < ⊤}`,
   `a0 = A.indicator (fun y => (a y).toReal)`. The section function uses the same set `A`,
   the same measurable exceptional set as LIP051.27, as the specification requires. `F` is an
   everywhere-defined function; no representative is chosen and no diagonal value is altered.
4. The section coefficient is `g = A.indicator (fun y => ∫ x, F (x, y) * e x ∂μ)`, a Bochner
   integral, with `F (x, y) * e x` in the order of the specification (`F e_i`). On `A` the
   integrand is integrable (Hölder with exponents `2, 2`), so the Bochner default value zero is
   not used there.
5. Conclusions. `g_i` measurable is `Measurable g`; `g_i ∈ L²(μ)` is `MemLp g 2 μ`;
   `|g_i(y)|² ≤ a0(y)` almost everywhere is `∀ᵐ y ∂μ, |g y| ^ 2 ≤ a0 y` (it is in fact
   proved for every `y`); `‖g_i‖₂ ≤ ‖F‖₂` is
   `(eLpNorm g 2 μ).toReal ≤ (eLpNorm F 2 (μ.prod μ)).toReal`, the same real-valued `L²`
   seminorm convention as in LIP051.27, note 7.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- For `f ∈ L²(μ)`, `∫ f * f dμ` is the square of the real `L²` seminorm. -/
lemma integral_mul_self_LIP05128 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : ∫ x, f x * f x ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  have h1 : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ x, f x * f x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    simp [sq]
  rw [← h1, real_inner_self_eq_norm_sq, Lp.norm_toLp]

/-- Cauchy–Schwarz for real `L²(μ)` functions. -/
lemma integral_mul_sq_le_LIP05128 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (eLpNorm f 2 μ).toReal ^ 2 * (eLpNorm g 2 μ).toReal ^ 2 := by
  have h1 : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp [mul_comm]
  have h2 := abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [h1, Lp.norm_toLp, Lp.norm_toLp] at h2
  calc (∫ x, f x * g x ∂μ) ^ 2 = |∫ x, f x * g x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ ((eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = _ := mul_pow _ _ _

/-- A measurable `e` with `∫ e * e dμ = 1` lies in `L²(μ)`. -/
lemma memLp_of_integral_mul_self_eq_one_LIP05128 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {e : α → ℝ} (he : Measurable e) (he1 : ∫ x, e x * e x ∂μ = 1) :
    MemLp e 2 μ := by
  have hint : Integrable (fun x => e x * e x) μ := by
    by_contra h
    rw [integral_undef h] at he1
    exact zero_ne_one he1
  refine (memLp_two_iff_integrable_sq he.aestronglyMeasurable).2 ?_
  simpa [sq] using hint

/-- Sectionwise Cauchy–Schwarz: for `y` in `A`, the squared section coefficient is at most
the real part of `a y`. -/
lemma section_integral_sq_le_LIP05128 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α × α → ℝ) (hF : Measurable F) (e : α → ℝ) (he : Measurable e)
    (he1 : ∫ x, e x * e x ∂μ = 1) (y : α)
    (hy : ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤) :
    (∫ x, F (x, y) * e x ∂μ) ^ 2 ≤ (∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ).toReal := by
  have hFy : MemLp (fun x => F (x, y)) 2 μ := memLp_section_LIP05127 μ F hF y hy
  have heL : MemLp e 2 μ := memLp_of_integral_mul_self_eq_one_LIP05128 he he1
  have hcs := integral_mul_sq_le_LIP05128 hFy heL
  rw [integral_mul_self_LIP05128 heL] at he1
  have hsq : (eLpNorm (fun x => F (x, y)) 2 μ).toReal ^ 2
      = (∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ).toReal := by
    have hm : Measurable (fun x => F (x, y)) := hF.comp measurable_prodMk_right
    rw [← ENNReal.toReal_pow]
    exact congrArg ENNReal.toReal (eLpNorm_sq_LIP05127 (f := fun x => F (x, y)) hm.aestronglyMeasurable)
  rw [he1, mul_one, hsq] at hcs
  exact hcs

/-- Section coefficient as an `L²` contraction (LIP051.28). With `a`, `A`, `a0` as in
LIP051.27 and `g y = ∫ F (x, y) * e x dμ(x)` on `A`, `0` off `A`: `g` is measurable, in `L²(μ)`,
`|g y| ^ 2 ≤ a0 y` almost everywhere, and `‖g‖₂ ≤ ‖F‖₂`. See the module docstring, R5 notes. -/
theorem lip051_28_section_coefficient_contraction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α × α → ℝ) (hF : Measurable F) (hL2 : MemLp F 2 (μ.prod μ))
    (e : α → ℝ) (he : Measurable e) (he1 : ∫ x, e x * e x ∂μ = 1) :
    let a : α → ENNReal := fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ
    let A : Set α := {y | a y < ⊤}
    let a0 : α → ℝ := A.indicator (fun y => (a y).toReal)
    let g : α → ℝ := A.indicator (fun y => ∫ x, F (x, y) * e x ∂μ)
    Measurable g ∧ MemLp g 2 μ ∧ (∀ᵐ y ∂μ, |g y| ^ 2 ≤ a0 y) ∧
      (eLpNorm g 2 μ).toReal ≤ (eLpNorm F 2 (μ.prod μ)).toReal := by
  intro a A a0 g
  obtain ⟨ha, hAm, _, _, ha0m, ha0i, ha0nn, ha0int⟩ :=
    lip051_27_square_integrable_sections μ F hF hL2
  have hFe : StronglyMeasurable (fun p : α × α => F p * e p.1) :=
    (hF.mul (he.comp measurable_fst)).stronglyMeasurable
  have hgm : Measurable g :=
    (hFe.integral_prod_left' (μ := μ)).measurable.indicator hAm
  have hpt : ∀ y, |g y| ^ 2 ≤ a0 y := by
    intro y
    by_cases hy : y ∈ A
    · have hy' : ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤ := hy
      have h := section_integral_sq_le_LIP05128 μ F hF e he he1 y hy'
      simp only [g, a0, Set.indicator_of_mem hy, sq_abs]
      exact h
    · simp [g, a0, Set.indicator_of_notMem hy]
  have hsqint : Integrable (fun y => g y * g y) μ := by
    refine Integrable.mono' ha0i (hgm.mul hgm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul_self, ← sq]
    simpa [sq_abs] using hpt y
  have hgL : MemLp g 2 μ := by
    refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2 ?_
    simpa [sq] using hsqint
  refine ⟨hgm, hgL, Filter.Eventually.of_forall hpt, ?_⟩
  have hint_le : ∫ y, g y * g y ∂μ ≤ ∫ y, a0 y ∂μ := by
    refine integral_mono hsqint ha0i fun y => ?_
    simpa [sq_abs, sq] using hpt y
  rw [integral_mul_self_LIP05128 hgL, ha0int] at hint_le
  exact (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero).1 hint_le

end DGPS.Frontier.LIP051
