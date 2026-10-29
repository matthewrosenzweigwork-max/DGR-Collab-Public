import Mathlib
import DGPS.Frontier.LIP051.T38

/-!
# LIP051.40: One-overlap covariance

Task id: LIP051.40 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: One-overlap covariance.

Provides:
* `DGPS.Frontier.LIP051.lip051_40_one_overlap_covariance`: for a probability measure `μ` on a
  measurable space `E`, a measurable symmetric real kernel `F : E → E → ℝ` with `F ∈ L²(μ ⊗ μ)`
  and `∫ F(x, y) dμ(x) = 0` for almost every `y` (the hypotheses of LIP051.38), and three
  pairwise distinct labels `i, j, k` in `Fin N`, the product `x ↦ F (x i) (x j) * F (x i) (x k)`
  on `Fin N → E` with law `Q_N = Measure.pi (fun _ => μ)` is integrable and has expectation zero.
* `DGPS.Frontier.LIP051.lip051_40_one_overlap_covariance_unordered_pairs`: the same conclusion
  (integrability and zero expectation) for two unordered pairs `{a, b}` and `{c, d}` of distinct
  labels having exactly one common label, written with ordered representatives and the
  symmetric kernel.
* Helpers (all suffixed `_LIP05140`): `triple_LIP05140` (the map `x ↦ (x i, x j, x k)`),
  `measurePreserving_triple_LIP05140` (it pushes `Q_N` to `μ ⊗ (μ ⊗ μ)`),
  `memLp_first_LIP05140` and `memLp_second_LIP05140` (the two pair evaluations are in `L²` of the
  three-fold product), `integrable_prod_LIP05140` (Cauchy-Schwarz integrability on `μ ⊗ (μ ⊗ μ)`),
  `integral_prod_zero_LIP05140` (the integral on `μ ⊗ (μ ⊗ μ)` vanishes),
  `one_overlap_distinct_LIP05140` (the three-label statement in both conclusions).

R5 notes:
* Hypotheses are those of LIP051.38 (`μ` probability, `F` measurable, symmetric, in `L²(μ ⊗ μ)`,
  centered in the first argument for almost every second argument) plus pairwise distinctness of
  the three labels, as the specification says "for three distinct particle labels".
  Measurability `_hF` is retained as a binder and unused, since `MemLp` carries the measurability
  needed, as in LIP051.38.
* Symmetry is used: the centering for `F (x, .)` is obtained from centering of `F (., y)`.
* The Cauchy-Schwarz bound on the absolute expectation is part of the proof in the specification
  but not of its statement; only integrability and vanishing expectation are concluded.
* Unordered pairs. "Two unequal unordered pairs with exactly one common label" is read as ordered
  representatives `(a, b)` and `(c, d)` with `a ≠ b`, `c ≠ d` and
  `({a, b} : Finset (Fin N)) ∩ {c, d}` of cardinality one. Since `F` is symmetric, the value
  `F (x a) (x b)` depends only on the unordered pair. Two equal unordered pairs would have a
  two-element intersection, so unequal pairs are implied by the cardinality condition.
* The product is the pointwise product of the two pair evaluations on `Fin N → E`; integrals are
  Bochner integrals, "integrable" is Mathlib's `Integrable`.
* Mode indexing (FD-002). No mode index occurs in this unit; the statement is abstract in `E`,
  `μ`, `F`, so neither a positive-mode nor a mode-zero reading is adopted.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- The triple of coordinates `x ↦ (x i, x j, x k)`. -/
def triple_LIP05140 {E : Type*} {N : ℕ} (i j k : Fin N) : (Fin N → E) → E × E × E :=
  fun x => (x i, x j, x k)

/-- Three-fold product decomposition of `Fin 3 → E`. -/
lemma measurePreserving_fin3_LIP05140 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : Fin 3 → E => (z 0, z 1, z 2))
      (Measure.pi (fun _ : Fin 3 => μ)) (μ.prod (μ.prod μ)) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0
  have h2 := measurePreserving_finTwoArrow (m := inferInstance) μ
  have h3 := (MeasurePreserving.id μ).prod h2
  exact h3.comp h1

/-- The triple map pushes `Q_N` forward to `μ ⊗ (μ ⊗ μ)` for distinct labels. -/
lemma measurePreserving_triple_LIP05140 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {N : ℕ} {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (triple_LIP05140 (E := E) i j k)
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod (μ.prod μ)) := by
  have hb : Function.Injective (![i, j, k] : Fin 3 → Fin N) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hT := lip051_35_finite_coordinate_restriction_law_measurePreserving μ _ hb
  exact (measurePreserving_fin3_LIP05140 μ).comp hT

/-- The first pair evaluation is in `L²` of the three-fold product. -/
lemma memLp_first_LIP05140 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → E → ℝ)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)) :
    MemLp (fun w : E × E × E => F w.1 w.2.1) 2 (μ.prod (μ.prod μ)) := by
  have h : MeasurePreserving (fun w : E × E × E => (w.1, w.2.1)) (μ.prod (μ.prod μ)) (μ.prod μ) :=
    (MeasurePreserving.id μ).prod measurePreserving_fst
  exact hL2.comp_measurePreserving h

/-- The second pair evaluation is in `L²` of the three-fold product. -/
lemma memLp_second_LIP05140 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → E → ℝ)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)) :
    MemLp (fun w : E × E × E => F w.1 w.2.2) 2 (μ.prod (μ.prod μ)) := by
  have h : MeasurePreserving (fun w : E × E × E => (w.1, w.2.2)) (μ.prod (μ.prod μ)) (μ.prod μ) :=
    (MeasurePreserving.id μ).prod measurePreserving_snd
  exact hL2.comp_measurePreserving h

/-- Cauchy-Schwarz: the product of the two pair evaluations is integrable on `μ ⊗ (μ ⊗ μ)`. -/
lemma integrable_prod_LIP05140 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → E → ℝ)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)) :
    Integrable (fun w : E × E × E => F w.1 w.2.1 * F w.1 w.2.2) (μ.prod (μ.prod μ)) :=
  (memLp_first_LIP05140 μ F hL2).integrable_mul (memLp_second_LIP05140 μ F hL2)

/-- The integral of the product on `μ ⊗ (μ ⊗ μ)` vanishes. -/
lemma integral_prod_zero_LIP05140 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → E → ℝ) (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0) :
    ∫ w : E × E × E, F w.1 w.2.1 * F w.1 w.2.2 ∂(μ.prod (μ.prod μ)) = 0 := by
  rw [integral_prod _ (integrable_prod_LIP05140 μ F hL2)]
  have h : ∀ᵐ x ∂μ, ∫ y : E × E, F x y.1 * F x y.2 ∂(μ.prod μ) = 0 := by
    filter_upwards [hcent] with x hx
    rw [integral_prod_mul (fun y => F x y) (fun y => F x y)]
    have : ∫ y, F x y ∂μ = 0 := by
      simp_rw [hsymm x]
      exact hx
    rw [this, zero_mul]
  rw [integral_congr_ae h]
  simp

/-- The three-label statement: integrability, vanishing expectation and the Cauchy-Schwarz bound. -/
lemma one_overlap_distinct_LIP05140 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → E → ℝ) (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Integrable (fun x : Fin N → E => F (x i) (x j) * F (x i) (x k))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x i) (x j) * F (x i) (x k) ∂(Measure.pi (fun _ : Fin N => μ)) = 0 := by
  have hS := measurePreserving_triple_LIP05140 μ hij hik hjk
  have hint := integrable_prod_LIP05140 μ F hL2
  refine ⟨hS.integrable_comp hint.aestronglyMeasurable |>.mpr hint, ?_⟩
  have h1 : AEStronglyMeasurable (fun w : E × E × E => F w.1 w.2.1 * F w.1 w.2.2)
      (Measure.map (triple_LIP05140 (E := E) i j k) (Measure.pi (fun _ : Fin N => μ))) := by
    rw [hS.map_eq]
    exact hint.aestronglyMeasurable
  have h2 := integral_map hS.measurable.aemeasurable h1
  rw [hS.map_eq] at h2
  exact h2.symm.trans (integral_prod_zero_LIP05140 μ F hsymm hL2 hcent)

/-- **LIP051.40.** Under the hypotheses of LIP051.38, for three pairwise distinct labels
`i, j, k` the product `F (X_i, X_j) * F (X_i, X_k)` is integrable under `Q_N` with expectation
zero. -/
theorem lip051_40_one_overlap_covariance
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → E → ℝ) (_hF : Measurable (fun p : E × E => F p.1 p.2))
    (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Integrable (fun x : Fin N → E => F (x i) (x j) * F (x i) (x k))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x i) (x j) * F (x i) (x k) ∂(Measure.pi (fun _ : Fin N => μ)) = 0 :=
  one_overlap_distinct_LIP05140 μ F hsymm hL2 hcent hij hik hjk

/-- **LIP051.40** for unordered pairs: if `{a, b}` and `{c, d}` are pairs of distinct labels with
exactly one common label, then `F (X_a, X_b) * F (X_c, X_d)` is integrable under `Q_N` with
expectation zero. -/
theorem lip051_40_one_overlap_covariance_unordered_pairs
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → E → ℝ) (_hF : Measurable (fun p : E × E => F p.1 p.2))
    (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} (a b c d : Fin N) (hab : a ≠ b) (hcd : c ≠ d)
    (hone : (({a, b} : Finset (Fin N)) ∩ {c, d}).card = 1) :
    Integrable (fun x : Fin N → E => F (x a) (x b) * F (x c) (x d))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x a) (x b) * F (x c) (x d) ∂(Measure.pi (fun _ : Fin N => μ)) = 0 := by
  have key := fun {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) =>
    one_overlap_distinct_LIP05140 μ F hsymm hL2 hcent hij hik hjk
  have hpair : ∀ (p q : Fin N), p ≠ q → ((({p, q} : Finset (Fin N)) ∩ {p, q}).card = 1 → False) := by
    intro p q hpq h
    rw [Finset.inter_self, Finset.card_pair hpq] at h
    omega
  have hpair' : ∀ (p q : Fin N), p ≠ q → ((({p, q} : Finset (Fin N)) ∩ {q, p}).card = 1 → False) := by
    intro p q hpq h
    rw [Finset.pair_comm q p] at h
    exact hpair p q hpq h
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun h => hpair a b hab (by subst h; exact hone)
    exact key hab hcd hbd
  by_cases had : a = d
  · subst had
    have hbc : b ≠ c := fun h => hpair' a b hab (by subst h; exact hone)
    have := key (i := a) (j := b) (k := c) hab hac hbc
    simpa only [hsymm (_ ) (_), mul_comm] using this
  by_cases hbc : b = c
  · subst hbc
    have had' : a ≠ d := had
    have := key (i := b) (j := a) (k := d) hab.symm hcd had'
    simpa only [hsymm (_ ) (_), mul_comm] using this
  by_cases hbd : b = d
  · subst hbd
    have := key (i := b) (j := a) (k := c) hab.symm hcd.symm hac
    simpa only [hsymm (_ ) (_), mul_comm] using this
  exfalso
  have : (({a, b} : Finset (Fin N)) ∩ {c, d}) = ∅ := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      iff_false]
    rintro ⟨h1 | h1, h2 | h2⟩ <;> subst_vars <;> simp_all
  rw [this] at hone
  simp at hone

end DGPS.Frontier.LIP051
