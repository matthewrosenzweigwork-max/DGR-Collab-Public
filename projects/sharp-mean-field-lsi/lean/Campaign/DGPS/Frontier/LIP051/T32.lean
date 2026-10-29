import DGPS.Frontier.LIP051.T31

/-!
# LIP051.32: Exhaustive rectangular projections

Task id `LIP051.32`, title "Exhaustive rectangular projections" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1). Proved inputs:
`LIP051.30` (`DGPS.Frontier.LIP051.T30`) and `LIP051.31` (`DGPS.Frontier.LIP051.T31`).

## Provides

* `DGPS.Frontier.LIP051.rectIdx_LIP05132`: the rectangular index set `{0,…,R} × {0,…,R}` of
  pairs of natural numbers, as a finite set.
* `DGPS.Frontier.LIP051.rectProj_LIP05132`: the rectangular section projection
  `P_R F = ∑_{0 ≤ i, j ≤ R} ⟪F, P i j⟫ • P i j` of `F` in a real inner product space, for a
  family `P : ℕ → ℕ → E`.
* `DGPS.Frontier.LIP051.lip051_32_exhaustive_rectangular_projections`: for a probability measure
  `μ`, a real Hilbert basis `e` of `L²(μ)`, representatives `f j` of the classes `e j`, and
  `L²(μ ⊗ μ)` classes `P i j` of the products `f i p.1 * f j p.2`, for every `F ∈ L²(μ ⊗ μ)`:
  (i) `‖F - P_R F‖ → 0` as `R → ∞` (so `P_R F → F` in `L²(μ ⊗ μ)`); (ii) Parseval,
  `∑_{i,j ≥ 0} ⟪F, P i j⟫² = ‖F‖²`; (iii) for every `R`, the sum of `⟪F, P i j⟫²` over the
  pairs `(i, j)` outside `{0,…,R}²` equals `‖F - P_R F‖²`.
* `DGPS.Frontier.LIP051.inner_product_LIP05132` (helper): the classes `P i j` have inner products
  `δ_ik δ_jl` in `L²(μ ⊗ μ)`.
* `DGPS.Frontier.LIP051.mem_rectIdx_LIP05132` (helper): membership in the rectangle is
  `q.1 ≤ R ∧ q.2 ≤ R`.
* `DGPS.Frontier.LIP051.rectProj_sum_LIP05132` (helper): `P_R F` written as a sum over the
  rectangle of a Hilbert basis indexed by `ℕ × ℕ`.
* `DGPS.Frontier.LIP051.rect_props_LIP05132` (helper): the three conclusions for an arbitrary
  complete real inner product space with a Hilbert basis `B` indexed by `ℕ × ℕ` such that
  `B (i, j) = P i j`.

## R5 notes

1. Generality. As in LIP051.25 to LIP051.31 the theorem is for an arbitrary probability measure
   `μ` on an arbitrary measurable space and an arbitrary real Hilbert basis
   `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)`. No `Spec`, `KData`, `Hw`, `Torus`, kernel `K` or Wick
   object occurs; the transport to the campaign declaration belongs to LIP051.01.
2. The family. The specification's "complete orthonormal family" `e_i ⊗ e_j` is recorded as in
   LIP051.30 and LIP051.31: representatives `f j` with `f j =ᵐ[μ] e j` and classes
   `P i j : Lp ℝ 2 (μ.prod μ)` with `P i j =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2`. These are
   hypotheses of the theorem. The orthonormality of the family is not a hypothesis: it is
   proved in the body from `e.orthonormal` (through `inner_product_LIP05132`), since the
   specification takes it from LIP051.30.
3. Completeness. The specification's "dense span" is the totality of LIP051.31,
   `(Submodule.span ℝ (Set.range fun q : ℕ × ℕ => P q.1 q.2)).topologicalClosure = ⊤`, which is
   used as a hypothesis-free input of the proof (the second conjunct of `lip051_31_totality_product_family`).
   The orthonormal family is then a Hilbert basis indexed by `ℕ × ℕ`, built with `HilbertBasis.mk`.
4. Coefficients. `b_ij = ⟪F, e_i ⊗ e_j⟫` is `inner ℝ F (P i j)`, with the real inner product of
   `L²(μ ⊗ μ)` in the order written in the specification. The inner product of real Hilbert
   spaces is symmetric, so the order does not change any statement.
5. Indexing (defect FD-002). All indices `i, j` range over every natural number, including `0`,
   exactly as the specification's `i, j ≥ 0`. The hypothesis `e 0 = 1` of LIP051.25 and
   LIP051.30 is not used and is not assumed; dropping it only strengthens the statement, and
   no mode-zero hypothesis is added or removed beyond the frozen statement.
6. Rectangles. `P_R F = ∑_{0 ≤ i, j ≤ R} b_ij P i j` is the double sum over `range (R + 1)` in
   each coordinate, as written. The complement in (iii) is the subtype
   `{q : ℕ × ℕ // ¬ (q.1 ≤ R ∧ q.2 ≤ R)}`, the set of pairs outside `{0,…,R}²`.
7. Convergence. Statement (i) is the convergence `P_R F → F` in the norm of `L²(μ ⊗ μ)`, written
   as `‖F - P_R F‖ → 0`. The proof uses the unconditional summability of the Hilbert basis
   expansion (`HilbertBasis.hasSum_repr`) and the exhaustion of `ℕ × ℕ` by the rectangles,
   rather than a norm estimate on the tail.
8. Proof route. Parseval comes from `HilbertBasis.hasSum_inner_mul_inner`. The remainder identity
   (iii) is obtained by applying Parseval to `F - P_R F`, whose coefficients are the tail
   coefficients: zero on the rectangle and `b_ij` outside it. This is a change of route only;
   the statement is the specification's.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- The rectangular index set `{0,…,R} × {0,…,R}`. -/
def rectIdx_LIP05132 (R : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (R + 1) ×ˢ Finset.range (R + 1)

/-- The rectangular section projection `P_R F = ∑_{0 ≤ i, j ≤ R} ⟪F, P i j⟫ • P i j`. -/
noncomputable def rectProj_LIP05132 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ℕ → ℕ → E) (R : ℕ) (F : E) : E :=
  ∑ i ∈ Finset.range (R + 1), ∑ j ∈ Finset.range (R + 1), inner ℝ F (P i j) • P i j

/-- Membership in the rectangle. -/
lemma mem_rectIdx_LIP05132 (R : ℕ) (q : ℕ × ℕ) :
    q ∈ rectIdx_LIP05132 R ↔ q.1 ≤ R ∧ q.2 ≤ R := by
  simp only [rectIdx_LIP05132, Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff]

/-- The classes `P i j` of the products have inner products `δ_ik δ_jl` in `L²(μ ⊗ μ)`. -/
lemma inner_product_LIP05132 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ}
    (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ)) (P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ))
    (hP : ∀ i j, (P i j : α × α → ℝ) =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2) :
    ∀ i j k l : ℕ, inner ℝ (P i j) (P k l) =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  have hcov : ∀ a b : ℕ, ∫ x, f a x * f b x ∂μ = if a = b then 1 else 0 := by
    intro a b
    rw [← orthonormal_iff_ite.mp e.orthonormal a b, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfe a, hfe b] with x h1 h2
    simp only [← h1, ← h2, RCLike.inner_apply, conj_trivial]
    ring
  intro i j k l
  rw [L2.inner_def]
  calc ∫ p, inner ℝ (P i j p) (P k l p) ∂(μ.prod μ)
      = ∫ p, (f i p.1 * f j p.2) * (f k p.1 * f l p.2) ∂(μ.prod μ) := by
        refine integral_congr_ae ?_
        filter_upwards [hP i j, hP k l] with p h1 h2
        simp only [h1, h2, RCLike.inner_apply, conj_trivial]
        ring
    _ = ∫ z, (fun x => f i x * f k x) z.1 * (fun y => f j y * f l y) z.2 ∂(μ.prod μ) := by
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        show f i p.1 * f j p.2 * (f k p.1 * f l p.2) = f i p.1 * f k p.1 * (f j p.2 * f l p.2)
        ring
    _ = (∫ x, f i x * f k x ∂μ) * (∫ y, f j y * f l y ∂μ) :=
        integral_prod_mul (fun x => f i x * f k x) (fun y => f j y * f l y)
    _ = _ := by rw [hcov i k, hcov j l]

/-- The rectangular projection as a finite sum over the rectangle of a basis indexed by pairs. -/
lemma rectProj_sum_LIP05132 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : HilbertBasis (ℕ × ℕ) ℝ E) (P : ℕ → ℕ → E) (hBP : ∀ q : ℕ × ℕ, B q = P q.1 q.2)
    (F : E) (R : ℕ) :
    rectProj_LIP05132 P R F = ∑ q ∈ rectIdx_LIP05132 R, inner ℝ F (B q) • B q := by
  unfold rectProj_LIP05132 rectIdx_LIP05132
  rw [Finset.sum_product]
  simp only [hBP]

/-- The three conclusions for a Hilbert basis `B` indexed by `ℕ × ℕ` with `B (i, j) = P i j`. -/
lemma rect_props_LIP05132 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (B : HilbertBasis (ℕ × ℕ) ℝ E) (P : ℕ → ℕ → E)
    (hBP : ∀ q : ℕ × ℕ, B q = P q.1 q.2) (F : E) :
    Tendsto (fun R : ℕ => ‖F - rectProj_LIP05132 P R F‖) atTop (𝓝 0) ∧
    HasSum (fun q : ℕ × ℕ => inner ℝ F (P q.1 q.2) ^ 2) (‖F‖ ^ 2) ∧
    ∀ R : ℕ, HasSum (fun q : {q : ℕ × ℕ // ¬ (q.1 ≤ R ∧ q.2 ≤ R)} =>
      inner ℝ F (P q.1.1 q.1.2) ^ 2) (‖F - rectProj_LIP05132 P R F‖ ^ 2) := by
  have hrepr : ∀ q : ℕ × ℕ, B.repr F q = inner ℝ F (B q) := by
    intro q
    rw [HilbertBasis.repr_apply_apply, real_inner_comm]
  have hsumB : HasSum (fun q : ℕ × ℕ => inner ℝ F (B q) • B q) F := by
    have h := B.hasSum_repr F
    simpa only [hrepr] using h
  have horthB : ∀ i j : ℕ × ℕ, inner ℝ (B i) (B j) = if i = j then 1 else 0 :=
    fun i j => orthonormal_iff_ite.mp B.orthonormal i j
  have hrect : Tendsto rectIdx_LIP05132 atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun s => ⟨s.sup fun q => max q.1 q.2, fun R hR => ?_⟩
    show s ⊆ rectIdx_LIP05132 R
    intro q hq
    have hq' : max q.1 q.2 ≤ s.sup fun q => max q.1 q.2 :=
      Finset.le_sup (f := fun q : ℕ × ℕ => max q.1 q.2) hq
    rw [mem_rectIdx_LIP05132]
    exact ⟨(le_max_left _ _).trans (hq'.trans hR), (le_max_right _ _).trans (hq'.trans hR)⟩
  have hconv : Tendsto (fun R : ℕ => rectProj_LIP05132 P R F) atTop (𝓝 F) := by
    have h1 : Tendsto (fun s : Finset (ℕ × ℕ) => ∑ q ∈ s, inner ℝ F (B q) • B q) atTop
        (𝓝 F) := hsumB
    exact (h1.comp hrect).congr fun R => (rectProj_sum_LIP05132 B P hBP F R).symm
  refine ⟨?_, ?_, ?_⟩
  · exact (tendsto_iff_norm_sub_tendsto_zero.mp hconv).congr fun R => norm_sub_rev _ _
  · have key : ∀ q : ℕ × ℕ, inner ℝ F (B q) * inner ℝ (B q) F = inner ℝ F (P q.1 q.2) ^ 2 := by
      intro q
      rw [hBP q, real_inner_comm F, sq]
    have h2 := B.hasSum_inner_mul_inner F F
    simpa only [key, real_inner_self_eq_norm_sq] using h2
  · intro R
    have hproj : ∀ q : ℕ × ℕ, inner ℝ (rectProj_LIP05132 P R F) (B q) =
        if q ∈ rectIdx_LIP05132 R then inner ℝ F (B q) else 0 := by
      intro q
      rw [rectProj_sum_LIP05132 B P hBP F R, sum_inner]
      simp [horthB, real_inner_smul_left]
    have hG : ∀ q : ℕ × ℕ, inner ℝ (F - rectProj_LIP05132 P R F) (B q) =
        if q ∈ rectIdx_LIP05132 R then 0 else inner ℝ F (B q) := by
      intro q
      rw [inner_sub_left, hproj q]
      by_cases hq : q ∈ rectIdx_LIP05132 R <;> simp [hq]
    have hpars : HasSum (fun q : ℕ × ℕ =>
        (if q ∈ rectIdx_LIP05132 R then (0 : ℝ) else inner ℝ F (B q)) ^ 2)
        (‖F - rectProj_LIP05132 P R F‖ ^ 2) := by
      have h := B.hasSum_inner_mul_inner (F - rectProj_LIP05132 P R F)
        (F - rectProj_LIP05132 P R F)
      rw [real_inner_self_eq_norm_sq] at h
      have hfun : (fun q : ℕ × ℕ => (if q ∈ rectIdx_LIP05132 R then (0 : ℝ) else
          inner ℝ F (B q)) ^ 2) = fun q : ℕ × ℕ =>
          inner ℝ (F - rectProj_LIP05132 P R F) (B q) *
            inner ℝ (B q) (F - rectProj_LIP05132 P R F) := by
        funext q
        rw [real_inner_comm (F - rectProj_LIP05132 P R F) (B q), hG q, sq]
      rw [hfun]
      exact h
    have hind : (fun q : ℕ × ℕ => (if q ∈ rectIdx_LIP05132 R then (0 : ℝ) else
        inner ℝ F (B q)) ^ 2) =
        {q : ℕ × ℕ | ¬ (q.1 ≤ R ∧ q.2 ≤ R)}.indicator (fun q => inner ℝ F (B q) ^ 2) := by
      funext q
      rw [Set.indicator_apply]
      by_cases h : q.1 ≤ R ∧ q.2 ≤ R
      · have hS : q ∈ rectIdx_LIP05132 R := (mem_rectIdx_LIP05132 R q).2 h
        simp [hS, h]
      · have hS : q ∉ rectIdx_LIP05132 R := fun hS => h ((mem_rectIdx_LIP05132 R q).1 hS)
        simp [hS, h]
    rw [hind] at hpars
    have hB' : HasSum (fun q : {q : ℕ × ℕ // ¬ (q.1 ≤ R ∧ q.2 ≤ R)} =>
        inner ℝ F (B q.1) ^ 2) (‖F - rectProj_LIP05132 P R F‖ ^ 2) :=
      hasSum_subtype_iff_indicator.mpr hpars
    simpa only [hBP] using hB'

/-- LIP051.32: exhaustive rectangular projections. For a probability measure `μ`, a real Hilbert
basis `e` of `L²(μ)`, representatives `f j` of the classes `e j`, and classes `P i j` of the
products `f i p.1 * f j p.2` in `L²(μ ⊗ μ)`, and every `F ∈ L²(μ ⊗ μ)`: the rectangular
projections `P_R F` converge to `F` in `L²`; Parseval `∑ ⟪F, P i j⟫² = ‖F‖²` holds; and for each
`R` the sum of `⟪F, P i j⟫²` over the pairs outside `{0,…,R}²` equals `‖F - P_R F‖²`. See the
module docstring, R5 notes. -/
theorem lip051_32_exhaustive_rectangular_projections {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (f : ℕ → α → ℝ) (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ))
    (hP : ∀ i j, (P i j : α × α → ℝ) =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2)
    (F : Lp ℝ 2 (μ.prod μ)) :
    Tendsto (fun R : ℕ => ‖F - rectProj_LIP05132 P R F‖) atTop (𝓝 0) ∧
    HasSum (fun q : ℕ × ℕ => inner ℝ F (P q.1 q.2) ^ 2) (‖F‖ ^ 2) ∧
    ∀ R : ℕ, HasSum (fun q : {q : ℕ × ℕ // ¬ (q.1 ≤ R ∧ q.2 ≤ R)} =>
      inner ℝ F (P q.1.1 q.1.2) ^ 2) (‖F - rectProj_LIP05132 P R F‖ ^ 2) := by
  have hortho := inner_product_LIP05132 μ e hfe P hP
  have hv : Orthonormal ℝ (fun q : ℕ × ℕ => P q.1 q.2) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, j⟩ ⟨k, l⟩
    show inner ℝ (P i j) (P k l) = if (i, j) = (k, l) then 1 else 0
    rw [hortho i j k l]
    by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2]
  have htot := (lip051_31_totality_product_family μ e f hfe P hP).2
  obtain ⟨B, hB⟩ : ∃ B : HilbertBasis (ℕ × ℕ) ℝ (Lp ℝ 2 (μ.prod μ)),
      ⇑B = fun q : ℕ × ℕ => P q.1 q.2 :=
    ⟨HilbertBasis.mk hv (le_of_eq htot.symm), HilbertBasis.coe_mk hv (le_of_eq htot.symm)⟩
  exact rect_props_LIP05132 B P (fun q => by rw [hB]) F

end DGPS.Frontier.LIP051
