import Mathlib
import DGPS.Frontier.LIP051.T08

/-!
# LIP051.11: Bounded empirical-average estimate

Task id: LIP051.11 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Bounded empirical-average estimate.

Provides:
* `DGPS.Frontier.LIP051.lip051_11_bounded_empirical_average_estimate`: for a probability measure `μ`
  on a measurable space `E`, a measurable real `g` with `|g| ≤ M` (pointwise, `0 ≤ M`) and `N ≥ 1`,
  under the product law `Q_N = Measure.pi (fun _ : Fin N => μ)` with coordinate maps `X_l x = x l`,
  the expected absolute deviation of the empirical average from `μ(g)` is at most
  `√(Var_μ g) / √N`, and that bound is at most `M / √N`.
* Helper `DGPS.Frontier.LIP051.marginal_integral_LIP05111`: the coordinate `x i` of a product sample
  has the law `μ`, so `∫ h (x i) dQ_N = ∫ h dμ` for measurable `h` with `Integrable h μ`.
* Helper `DGPS.Frontier.LIP051.marginal_integrable_LIP05111`: the same law transfer for integrability.
* Helper `DGPS.Frontier.LIP051.integrable_of_bound_LIP05111`: a bounded measurable real function on a
  finite measure space is integrable.
* Helper `DGPS.Frontier.LIP051.cross_moment_zero_LIP05111`: for distinct labels `l ≠ k`, the centered
  coordinate products have zero mean under `Q_N`. Proved from LIP051.08 clause (2), the factorization
  across disjoint blocks.
* Helper `DGPS.Frontier.LIP051.abs_le_sqrt_integral_sq_LIP05111`: `∫ |A| ≤ √(∫ A²)` for bounded
  measurable `A` on a probability space.

Dependencies: LIP051.08 (`DGPS.Frontier.LIP051.T08`, `lip051_08_finite_product_marginals_e_bookkeeping`,
clause (2), and the coordinate restriction `restrictCoords_LIP05135`).

R5 notes:
* Ambient spaces. `E` is an arbitrary measurable space and `μ` an arbitrary probability measure on it;
  `Torus d` with its Borel structure is one instance. The sample space is `Fin N → E` with the product
  σ-algebra, and `Q_N = Measure.pi (fun _ => μ)`. No object of the campaign (`Spec`, `KData`, `Hw`,
  the Gaussian law, the kernel `K`, the positive modes of LIP051) is used or identified here.
* Hypothesis `|g| ≤ M`. Read literally as the pointwise bound `∀ x, |g x| ≤ M` with `0 ≤ M` and
  `Measurable g`. The bound is not weakened to an almost-everywhere bound.
* Measure of the absolute deviation. "E_{Q_N}|…|" is the Bochner integral `∫ x, |…| ∂Q_N`.
* Average and centering. The empirical average is `(1/N) * ∑ l, g (x l)` with the Lean `N : ℝ` cast,
  and `μ(g)` is `∫ y, g y ∂μ`. Both are displayed literally in the statement.
* Variance. `Var_μ(g)` is Mathlib's `ProbabilityTheory.variance g μ`. The proof uses its identity with
  the centered second moment `∫ (g - μ(g))²` (`variance_eq_integral`); no other variance convention is used.
* The square-root bound. The first conjunct is `E|…| ≤ √(Var g μ) / √N`, and the second conjunct is
  `√(Var g μ) / √N ≤ M / √N`. The spec's intermediate `√(Var g μ)/√N ≤ M/√N` is the second conjunct,
  proved from `Var g μ ≤ μ(g²) ≤ M²` and `0 ≤ M`.
* Range of N. The spec states the estimate for `N ≥ 1`; the statement assumes `1 ≤ N`. For `N = 0` the
  left side is `|μ(g)|` while the right side is zero, so the hypothesis is needed.
* Use of LIP051.08. The vanishing of covariances between distinct labels is taken from LIP051.08
  clause (2) (factorization across disjoint blocks) applied to the one-coordinate blocks `![l]` and
  `![k]`. The spec's phrase "two-coordinate product marginal in .08" is read as this clause. The
  product integrability hypothesis of that clause is discharged by boundedness of the centered
  coordinates, not assumed.
* Mode indexing (FD-002). This unit involves no Gaussian object, no Fourier or Hilbert-basis mode, and
  no mode index. No positive-mode or mode-zero reading is adopted; the issue recorded in FD-002 is not
  touched.
* Mean-square step. The expected absolute deviation is bounded by the square root of the expected square
  through the nonnegativity of the variance of `|A|`; no hypothesis beyond the statement is used.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory ProbabilityTheory

/-- The coordinate `x i` of a product sample under `μ^N` has law `μ`: the integral of a measurable
`h` against the coordinate is the integral of `h` against `μ`. -/
lemma marginal_integral_LIP05111 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {N : ℕ} (i : Fin N) {h : E → ℝ} (hh : Measurable h) :
    ∫ x, h (x i) ∂(Measure.pi fun _ : Fin N => μ) = ∫ y, h y ∂μ := by
  calc ∫ x, h (x i) ∂(Measure.pi fun _ : Fin N => μ)
      = ∫ y, h y ∂(Measure.map (Function.eval i) (Measure.pi fun _ : Fin N => μ)) :=
        (integral_map (measurable_pi_apply i).aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ y, h y ∂μ := by rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]

/-- A bounded measurable real function on a finite measure space is integrable. -/
lemma integrable_of_bound_LIP05111 {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {h : α → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    Integrable h ν :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- The law transfer for integrability: if `h` is `μ`-integrable, then `h (x i)` is `μ^N`-integrable. -/
lemma marginal_integrable_LIP05111 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {N : ℕ} (i : Fin N) {h : E → ℝ} (hh : Integrable h μ) :
    Integrable (fun x : Fin N → E => h (x i)) (Measure.pi fun _ : Fin N => μ) := by
  have hmap : Measure.map (Function.eval i) (Measure.pi fun _ : Fin N => μ) = μ :=
    (measurePreserving_eval (fun _ : Fin N => μ) i).map_eq
  have h' : Integrable h (Measure.map (Function.eval i) (Measure.pi fun _ : Fin N => μ)) := by
    rw [hmap]; exact hh
  exact (integrable_map_measure h'.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h'

/-- Mean absolute value bound: `∫ |A| ≤ √(∫ A²)` for a bounded measurable real `A` on a probability
space. The proof uses the nonnegativity of `Var |A| = ∫ |A|² - (∫ |A|)²`. -/
lemma abs_le_sqrt_integral_sq_LIP05111 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Ω → ℝ} (hA : Measurable A) {C : ℝ}
    (hC : ∀ x, |A x| ≤ C) :
    ∫ x, |A x| ∂P ≤ Real.sqrt (∫ x, A x ^ 2 ∂P) := by
  have habs_meas : Measurable fun x => |A x| := hA.abs
  have habs_bd : ∀ x, |(|A x|)| ≤ C := fun x => by rw [abs_abs]; exact hC x
  have hMem : MemLp (fun x => |A x|) 2 P :=
    MemLp.of_bound habs_meas.aestronglyMeasurable C (ae_of_all _ fun x => by
      simpa [Real.norm_eq_abs] using habs_bd x)
  have hvar := variance_eq_sub hMem
  have hnn := variance_nonneg (fun x => |A x|) P
  have hsq : ∫ x, (|A x|) ^ 2 ∂P = ∫ x, A x ^ 2 ∂P := by
    congr 1; funext x; exact sq_abs (A x)
  have hpow : (fun x => |A x|) ^ 2 = fun x => |A x| ^ 2 := by funext x; rfl
  have hcomb : (∫ x, |A x| ∂P) ^ 2 ≤ ∫ x, A x ^ 2 ∂P := by
    rw [variance_eq_sub hMem, hpow, hsq] at hnn
    linarith [hnn]
  have hI : 0 ≤ ∫ x, |A x| ∂P := integral_nonneg fun x => abs_nonneg (A x)
  have := Real.abs_le_sqrt hcomb
  rwa [abs_of_nonneg hI] at this

/-- Distinct labels: the centered coordinates have zero mixed moment under `Q_N`. This is LIP051.08
clause (2), factorization across the disjoint one-coordinate blocks `![l]` and `![k]`, with the
block factors equal to `∫ (g - m) dμ = 0`. -/
lemma cross_moment_zero_LIP05111 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (g : E → ℝ) (hg : Measurable g) (hgi : Integrable g μ)
    (m : ℝ) (hm : ∫ y, g y ∂μ = m) {N : ℕ} (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, |g x - m| ≤ C) (l k : Fin N) (hlk : l ≠ k) :
    ∫ x, (g (x l) - m) * (g (x k) - m) ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
  have hb₁ : Function.Injective (![l] : Fin 1 → Fin N) := fun i j _ => Subsingleton.elim i j
  have hb₂ : Function.Injective (![k] : Fin 1 → Fin N) := fun i j _ => Subsingleton.elim i j
  have hd : Disjoint (Set.range (![l] : Fin 1 → Fin N)) (Set.range (![k] : Fin 1 → Fin N)) := by
    rw [Set.disjoint_left]
    rintro a ⟨i, rfl⟩ ⟨j, hj⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    have hkl : k = l := by simpa using hj
    exact hlk hkl.symm
  have hfi : Integrable (fun y : Fin 1 → E => g (y 0) - m) (Measure.pi fun _ : Fin 1 => μ) :=
    marginal_integrable_LIP05111 μ 0 (hgi.sub (integrable_const m))
  have hfm : Measurable (fun y : Fin 1 → E => g (y 0) - m) :=
    (hg.comp (measurable_pi_apply 0)).sub measurable_const
  have hI : ∫ y, (g (y 0) - m) ∂(Measure.pi fun _ : Fin 1 => μ) = 0 := by
    have h1 : ∫ y, (g (y 0) - m) ∂(Measure.pi fun _ : Fin 1 => μ)
        = ∫ y, (g y - m) ∂μ :=
      marginal_integral_LIP05111 μ 0 (h := fun y => g y - m) (hg.sub measurable_const)
    rw [h1, integral_sub hgi (integrable_const m), hm]
    simp
  have hprod : Integrable (fun x : Fin N → E =>
      (fun y : Fin 1 → E => g (y 0) - m) (restrictCoords_LIP05135 (![l] : Fin 1 → Fin N) x) *
      (fun y : Fin 1 → E => g (y 0) - m) (restrictCoords_LIP05135 (![k] : Fin 1 → Fin N) x))
      (Measure.pi fun _ : Fin N => μ) := by
    refine integrable_of_bound_LIP05111 ?_ (C := C * C) fun x => ?_
    · exact (hfm.comp (measurable_restrictCoords_LIP05135 _)).mul
        (hfm.comp (measurable_restrictCoords_LIP05135 _))
    · rw [abs_mul]
      exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  have hTT := (lip051_08_finite_product_marginals_e_bookkeeping (𝕜 := ℝ) μ).2.1 1 1 N
    ![l] ![k] hb₁ hb₂ hd _ _ hfi hfi hprod
  rw [hI, zero_mul] at hTT
  exact hTT

/-- **LIP051.11.** Bounded empirical-average estimate. For a probability measure `μ`, a measurable
real `g` with `|g| ≤ M` and `0 ≤ M`, and `N ≥ 1`, under `Q_N = μ^N`:
`E_{Q_N} |(1/N) ∑ g(X_l) - μ(g)| ≤ √(Var_μ g) / √N ≤ M / √N`. -/
theorem lip051_11_bounded_empirical_average_estimate
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (g : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hg : Measurable g) (hbd : ∀ x, |g x| ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ x, |(1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - ∫ y, g y ∂μ|
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ Real.sqrt (variance g μ) / Real.sqrt (N : ℝ) ∧
    Real.sqrt (variance g μ) / Real.sqrt (N : ℝ) ≤ M / Real.sqrt (N : ℝ) := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, ∫ y, g y ∂μ = m := ⟨_, rfl⟩
  rw [hm]
  have hgi : Integrable g μ := integrable_of_bound_LIP05111 hg hbd
  have hmM : |m| ≤ M := by
    rw [← hm]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := M)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hbd x)
    simpa [Real.norm_eq_abs] using h
  have hC0 : 0 ≤ 2 * M := by linarith
  have hC : ∀ x, |g x - m| ≤ 2 * M := fun x => by
    obtain ⟨h1, h2⟩ := abs_le.1 (hbd x)
    obtain ⟨h3, h4⟩ := abs_le.1 hmM
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0' : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hmeasc : ∀ l : Fin N, Measurable (fun x : Fin N → E => g (x l) - m) :=
    fun l => (hg.comp (measurable_pi_apply l)).sub measurable_const
  have hint : ∀ l k : Fin N, Integrable
      (fun x : Fin N → E => (g (x l) - m) * (g (x k) - m)) (Measure.pi fun _ : Fin N => μ) :=
    fun l k => integrable_of_bound_LIP05111 ((hmeasc l).mul (hmeasc k)) (C := 2 * M * (2 * M))
      fun x => by
        rw [abs_mul]
        exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  have hcross : ∀ l k : Fin N, l ≠ k → ∫ x, (g (x l) - m) * (g (x k) - m)
      ∂(Measure.pi fun _ : Fin N => μ) = 0 :=
    fun l k hlk => cross_moment_zero_LIP05111 μ g hg hgi m hm (2 * M) hC0 hC l k hlk
  have hdiag : ∀ l : Fin N, ∫ x, (g (x l) - m) * (g (x l) - m)
      ∂(Measure.pi fun _ : Fin N => μ) = variance g μ := by
    intro l
    have h1 : ∫ x, (g (x l) - m) * (g (x l) - m) ∂(Measure.pi fun _ : Fin N => μ)
        = ∫ y, (g y - m) * (g y - m) ∂μ :=
      marginal_integral_LIP05111 μ l (h := fun y => (g y - m) * (g y - m))
        ((hg.sub measurable_const).mul (hg.sub measurable_const))
    rw [h1, variance_eq_integral hg.aemeasurable, hm]
    congr 1
    funext y
    ring
  have hsumc : ∀ x : Fin N → E, (1 / (N : ℝ)) * (∑ l : Fin N, g (x l)) - m
      = (1 / (N : ℝ)) * ∑ l : Fin N, (g (x l) - m) := by
    intro x
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hexp : ∀ x : Fin N → E, ((1 / (N : ℝ)) * ∑ l : Fin N, (g (x l) - m)) ^ 2
      = (1 / (N : ℝ)) ^ 2 * ∑ l : Fin N, ∑ k : Fin N, (g (x l) - m) * (g (x k) - m) := by
    intro x
    rw [mul_pow, sq (∑ l : Fin N, (g (x l) - m)), Finset.sum_mul_sum]
  have hinner : ∀ l : Fin N, ∫ x, ∑ k : Fin N, (g (x l) - m) * (g (x k) - m)
      ∂(Measure.pi fun _ : Fin N => μ) = variance g μ := by
    intro l
    rw [integral_finsetSum _ (fun k _ => hint l k)]
    rw [Finset.sum_eq_single l (fun k _ hk => hcross l k (Ne.symm hk)) (by simp)]
    exact hdiag l
  have hsq : ∫ x, ((1 / (N : ℝ)) * ∑ l : Fin N, (g (x l) - m)) ^ 2
      ∂(Measure.pi fun _ : Fin N => μ) = variance g μ / N := by
    simp_rw [hexp]
    rw [integral_const_mul, integral_finsetSum _ (fun l _ => integrable_finsetSum _
      (fun k _ => hint l k))]
    rw [Finset.sum_congr rfl (fun l _ => hinner l)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hA_bd : ∀ x : Fin N → E, |(1 / (N : ℝ)) * ∑ l : Fin N, (g (x l) - m)| ≤ 2 * M := by
    intro x
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    have hs : |∑ l : Fin N, (g (x l) - m)| ≤ (N : ℝ) * (2 * M) := by
      calc |∑ l : Fin N, (g (x l) - m)| ≤ ∑ l : Fin N, |g (x l) - m| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l : Fin N, (2 * M) := Finset.sum_le_sum fun l _ => hC _
        _ = (N : ℝ) * (2 * M) := by simp
    calc 1 / (N : ℝ) * |∑ l : Fin N, (g (x l) - m)| ≤ 1 / (N : ℝ) * ((N : ℝ) * (2 * M)) := by
          gcongr
      _ = 2 * M := by field_simp
  have hmeasA : Measurable (fun x : Fin N → E =>
      (1 / (N : ℝ)) * ∑ l : Fin N, (g (x l) - m)) :=
    measurable_const.mul (Finset.measurable_sum _ fun l _ => hmeasc l)
  have hmain := abs_le_sqrt_integral_sq_LIP05111 (P := Measure.pi fun _ : Fin N => μ) hmeasA
    (C := 2 * M) hA_bd
  have hsqb : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => by
    obtain ⟨h1, h2⟩ := abs_le.1 (hbd x)
    nlinarith
  have hVM : variance g μ ≤ M ^ 2 := by
    refine (variance_le_expectation_sq hg.aestronglyMeasurable).trans ?_
    have hint2 : Integrable (fun x => g x ^ 2) μ :=
      integrable_of_bound_LIP05111 (hg.pow_const 2) (C := M ^ 2) fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact hsqb x
    calc ∫ x, g x ^ 2 ∂μ ≤ ∫ _x : E, M ^ 2 ∂μ :=
          integral_mono hint2 (integrable_const (M ^ 2)) hsqb
      _ = M ^ 2 := by simp
  have hsqrtV : Real.sqrt (variance g μ) ≤ M := by
    calc Real.sqrt (variance g μ) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hVM
      _ = M := Real.sqrt_sq hM
  simp only [hsumc]
  constructor
  · calc ∫ x, |(1 / (N : ℝ)) * ∑ l : Fin N, (g (x l) - m)| ∂(Measure.pi fun _ : Fin N => μ)
        ≤ Real.sqrt (∫ x, ((1 / (N : ℝ)) * ∑ l : Fin N, (g (x l) - m)) ^ 2
            ∂(Measure.pi fun _ : Fin N => μ)) := hmain
      _ = Real.sqrt (variance g μ / N) := by rw [hsq]
      _ = Real.sqrt (variance g μ) / Real.sqrt (N : ℝ) :=
          Real.sqrt_div (variance_nonneg g μ) _
  · gcongr

end DGPS.Frontier.LIP051
