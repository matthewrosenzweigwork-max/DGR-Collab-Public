import DGPS.Frontier.LIP051.T04
import DGPS.Frontier.LIP051.T25
import DGPS.Frontier.LIP051.T30

/-!
# LIP051.31: Totality of the product family

Task id `LIP051.31`, title "Totality of the product family" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1). Proved inputs:
`LIP051.04` (`DGPS.Frontier.LIP051.T04`), `LIP051.25` (`T25`), `LIP051.27` (`T27`) and
`LIP051.30` (`T30`).

## Provides

* `DGPS.Frontier.LIP051.lip051_31_totality_product_family`: for a probability measure `μ` and a
  real Hilbert basis `e` of `L²(μ)`, for representatives `f j` of the classes `e j`
  and `L²(μ ⊗ μ)` classes `P i j` of the products `f i p.1 * f j p.2`: (i) every
  `F ∈ L²(μ ⊗ μ)` whose inner product with every `P i j` is zero vanishes `μ ⊗ μ`-almost
  everywhere (and is `0` in `L²(μ ⊗ μ)`); (ii) the closure of the real linear span of all the
  `P i j` is the whole space `L²(μ ⊗ μ)`.
* `DGPS.Frontier.LIP051.lip051_31_totality_product_family_exists`: the data `f`, `P` of the
  main theorem exist (so that it is not vacuous).
* `DGPS.Frontier.LIP051.eq_zero_of_inner_basis_LIP05131` (helper): completeness of a Hilbert
  basis, an element orthogonal to every basis vector is zero.
* `DGPS.Frontier.LIP051.ae_zero_of_integral_basis_LIP05131` (helper): an `L²(μ)` function with
  `∫ s * f j dμ = 0` for all `j` is zero almost everywhere.
* `DGPS.Frontier.LIP051.norm_one_rep_LIP05131` (helper): a representative of a basis vector has
  `eLpNorm = 1`.
* `DGPS.Frontier.LIP051.section_coeff_ae_zero_LIP05131` (helper): the section coefficients of an
  `F` orthogonal to all products vanish almost everywhere.
* `DGPS.Frontier.LIP051.ae_zero_of_pairings_zero_LIP05131` (helper): the function-level form of
  the totality statement.

## R5 notes

1. Generality. The specification speaks of the original Hilbert basis of `L²(μ)`. As in
   LIP051.25 to LIP051.30 the theorem is for an arbitrary probability measure `μ` on an
   arbitrary measurable space and an arbitrary basis `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)`. No
   `Spec`, `KData`, `Hw`, `Torus`, kernel `K` or Wick object occurs; the transport to the
   campaign declaration belongs to LIP051.01.
2. Mode indexing (defect FD-002). All indices `i, j` range over every natural number, including
   `0`, exactly as the specification's "every natural pair (i,j)". The totality statement
   contains no Gaussian object, so the positive-mode restriction of the Gaussian limit does not
   apply to it, and the constant mode is kept. The hypothesis `e 0 = 1` of LIP051.25 and
   LIP051.30 is not used and is not assumed; dropping it only strengthens the statement.
3. The family of LIP051.30. The family `e_i ⊗ e_j` is recorded as in LIP051.30:
   representatives `f j` with `f j =ᵐ[μ] e j` and classes `P i j : Lp ℝ 2 (μ.prod μ)` with
   `P i j =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2`. Those are hypotheses of the theorem, so it
   holds for every such choice, in particular for the one produced by LIP051.30. Measurability
   of `f j` is not needed by the proof and is therefore not a hypothesis (dropping it only
   strengthens the statement); the companion `lip051_31_totality_product_family_exists`
   shows that such data exist, with `f j` measurable.
4. `F ∈ L²(μ ⊗ μ)` is an element `F : Lp ℝ 2 (μ.prod μ)` (a class). "Zero inner product with
   `e_i ⊗ e_j`" is `inner ℝ F (P i j) = 0`. "`F = 0` almost everywhere" is
   `(F : α × α → ℝ) =ᵐ[μ.prod μ] 0`; the equality `F = 0` in `Lp` is equivalent.
5. Totality. "The closed linear span of the family is all of `L²(μ ⊗ μ)`" is
   `(Submodule.span ℝ (Set.range fun q : ℕ × ℕ => P q.1 q.2)).topologicalClosure = ⊤`.
6. Proof route. As in the specification: section coefficients via LIP051.04 (applied to a
   measurable representative of `F`), vanishing for each index by completeness of the basis,
   intersection of countably many full-measure sets, vanishing of almost every section by
   completeness again, and integration with LIP051.27. The totality part uses the orthogonal
   complement and `Submodule.topologicalClosure_eq_top_iff`.
7. Lean-exposed specification defects in this unit: none found.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- Completeness of a Hilbert basis: an element orthogonal to every basis vector is zero. -/
lemma eq_zero_of_inner_basis_LIP05131 {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (e : HilbertBasis ι ℝ E) {h : E}
    (H : ∀ j, inner ℝ (e j) h = 0) : h = 0 := by
  have h0 : e.repr h = 0 := by
    ext j
    rw [HilbertBasis.repr_apply_apply]
    simpa using H j
  exact e.repr.map_eq_zero_iff.mp h0

/-- An `L²(μ)` function whose pairing with every basis representative vanishes is zero a.e. -/
lemma ae_zero_of_integral_basis_LIP05131 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ} (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    {s : α → ℝ} (hs : MemLp s 2 μ) (H : ∀ j, ∫ x, s x * f j x ∂μ = 0) :
    s =ᵐ[μ] 0 := by
  have hz : hs.toLp s = 0 := by
    refine eq_zero_of_inner_basis_LIP05131 e fun j => ?_
    rw [L2.inner_def]
    have : ∫ x, inner ℝ ((e j : Lp ℝ 2 μ) x) ((hs.toLp s) x) ∂μ = ∫ x, s x * f j x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hfe j, hs.coeFn_toLp] with x h1 h2
      simp only [h1.symm, h2, RCLike.inner_apply, conj_trivial]
    rw [this]
    exact H j
  have := hs.coeFn_toLp
  rw [hz] at this
  filter_upwards [this, Lp.coeFn_zero ℝ 2 μ] with x h1 h2
  rw [← h1, h2]

/-- A representative of a Hilbert basis vector has `eLpNorm` one. -/
lemma norm_one_rep_LIP05131 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ} (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (j : ℕ) : eLpNorm (f j) 2 μ = 1 := by
  rw [eLpNorm_congr_ae (hfe j)]
  have h1 : ‖e j‖ = 1 := e.orthonormal.1 j
  rw [Lp.norm_def] at h1
  have hne : eLpNorm (e j : α → ℝ) 2 μ ≠ ⊤ := (Lp.memLp (e j)).eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hne, h1]
  simp

/-- Section coefficients of an `F` orthogonal to all products vanish almost everywhere
(on the good set of LIP051.27), for each fixed index. -/
lemma section_coeff_ae_zero_LIP05131 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ}
    (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ)) (F : α × α → ℝ) (hF : Measurable F)
    (hL2 : MemLp F 2 (μ.prod μ))
    (H : ∀ i j, ∫ p, F p * f i p.1 * f j p.2 ∂(μ.prod μ) = 0) (i : ℕ) :
    ∀ᵐ y ∂μ, y ∈ {y | ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤} → ∫ x, F (x, y) * f i x ∂μ = 0 := by
  have hfL : ∀ j, MemLp (f j) 2 μ := fun j => (Lp.memLp (e j)).ae_eq (hfe j).symm
  obtain ⟨-, -, hgL, -, hpair⟩ := lip051_04_l2_section_projections μ F hF hL2 (f i) (hfL i)
    (norm_one_rep_LIP05131 μ e hfe i)
  have hg0 := ae_zero_of_integral_basis_LIP05131 μ e hfe hgL fun j => by
    rw [hpair (f j) (hfL j) (norm_one_rep_LIP05131 μ e hfe j)]
    exact H i j
  filter_upwards [hg0] with y hy hyA
  have hyA' : y ∈ {y | ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤} := hyA
  exact (Set.indicator_of_mem hyA' (fun y => ∫ x, F (x, y) * f i x ∂μ)).symm.trans hy

/-- Function-level totality: a measurable `F ∈ L²(μ ⊗ μ)` whose pairings with all products
`f i ⊗ f j` vanish is zero almost everywhere. -/
lemma ae_zero_of_pairings_zero_LIP05131 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ}
    (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ)) (F : α × α → ℝ) (hF : Measurable F)
    (hL2 : MemLp F 2 (μ.prod μ))
    (H : ∀ i j, ∫ p, F p * f i p.1 * f j p.2 ∂(μ.prod μ) = 0) :
    F =ᵐ[μ.prod μ] 0 := by
  obtain ⟨-, -, -, hsec, ha0⟩ := lip051_27_square_integrable_sections μ F hF hL2
  obtain ⟨-, -, -, hint⟩ := ha0
  have hall : ∀ᵐ y ∂μ, ∀ i, y ∈ {y | ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤} →
      ∫ x, F (x, y) * f i x ∂μ = 0 :=
    ae_all_iff.2 fun i => section_coeff_ae_zero_LIP05131 μ e hfe F hF hL2 H i
  have hzero : ∀ᵐ y ∂μ, ({y | ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤}.indicator
      fun y => (∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ).toReal) y = 0 := by
    filter_upwards [hall] with y hy
    by_cases hyA : y ∈ {y | ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤}
    · rw [Set.indicator_of_mem hyA]
      have hs0 : (fun x => F (x, y)) =ᵐ[μ] 0 :=
        ae_zero_of_integral_basis_LIP05131 μ e hfe (hsec y hyA) fun i => hy i hyA
      have : ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0)]
        · simp
        · filter_upwards [hs0] with x hx
          simp only [hx, Pi.zero_apply, enorm_zero]
          norm_num
      rw [this]
      simp
    · rw [Set.indicator_of_notMem hyA]
  have h0 : ∫ y, ({y | ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤}.indicator
      fun y => (∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ).toReal) y ∂μ = 0 :=
    (integral_congr_ae hzero).trans (integral_zero _ _)
  rw [h0] at hint
  have hn : (eLpNorm F 2 (μ.prod μ)).toReal = 0 := by
    have := hint.symm
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have hn0 : eLpNorm F 2 (μ.prod μ) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hn with h | h
    · exact h
    · exact absurd h hL2.eLpNorm_lt_top.ne
  exact (eLpNorm_eq_zero_iff two_ne_zero).1 hn0

/-- Totality of the product family (LIP051.31). For a probability measure `μ`, a real Hilbert
basis `e` of `L²(μ)`, representatives `f j` of the classes `e j`, and classes
`P i j` of the products `f i p.1 * f j p.2` in `L²(μ ⊗ μ)`: every `F ∈ L²(μ ⊗ μ)` with zero
inner product with every `P i j` vanishes almost everywhere (and equals `0` in `L²`), and the
closed linear span of the family is all of `L²(μ ⊗ μ)`. See the module docstring, R5 notes. -/
theorem lip051_31_totality_product_family {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (f : ℕ → α → ℝ) (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ))
    (hP : ∀ i j, (P i j : α × α → ℝ) =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2) :
    (∀ F : Lp ℝ 2 (μ.prod μ), (∀ i j, inner ℝ F (P i j) = 0) →
      (F : α × α → ℝ) =ᵐ[μ.prod μ] 0 ∧ F = 0) ∧
    (Submodule.span ℝ (Set.range fun q : ℕ × ℕ => P q.1 q.2)).topologicalClosure = ⊤ := by
  have hzero : ∀ F : Lp ℝ 2 (μ.prod μ), (∀ i j, inner ℝ F (P i j) = 0) → F = 0 := by
    intro F hF
    obtain ⟨Fm, hFm, hFae'⟩ := representative_exists_LIP05125 (μ.prod μ) F
    have hFae : (F : α × α → ℝ) =ᵐ[μ.prod μ] Fm := hFae'.symm
    have hFL : MemLp Fm 2 (μ.prod μ) := (Lp.memLp F).ae_eq hFae
    have hint : ∀ i j, ∫ p, Fm p * f i p.1 * f j p.2 ∂(μ.prod μ) = 0 := by
      intro i j
      rw [← hF i j, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hFae, hP i j] with p h1 h2
      simp only [h2, h1, RCLike.inner_apply, conj_trivial]
      ring
    have hm := ae_zero_of_pairings_zero_LIP05131 μ e hfe _ hFm hFL hint
    exact Lp.eq_zero_iff_ae_eq_zero.2 (hFae.trans hm)
  refine ⟨fun F hF => ⟨?_, hzero F hF⟩, ?_⟩
  · rw [hzero F hF]
    exact Lp.coeFn_zero ℝ 2 _
  · rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro F hF
    refine hzero F fun i j => ?_
    exact (Submodule.mem_orthogonal' _ F).1 hF _ (Submodule.subset_span ⟨(i, j), rfl⟩)

/-- Existence of the data of LIP051.31: measurable representatives `f j` of the basis classes
and the product classes `P i j`. -/
theorem lip051_31_totality_product_family_exists {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) :
    ∃ f : ℕ → α → ℝ, (∀ j, Measurable (f j)) ∧ (∀ j, f j =ᵐ[μ] (e j : α → ℝ)) ∧
      ∃ P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ),
        ∀ i j, (P i j : α × α → ℝ) =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2 := by
  choose f hfm hfe using fun j => representative_exists_LIP05125 μ (e j)
  have hmem : ∀ j, MemLp (f j) 2 μ := fun j => (Lp.memLp (e j)).ae_eq (hfe j).symm
  exact ⟨f, hfm, hfe, fun i j => (memLp_product_LIP05130 μ hfm hmem i j).toLp _,
    fun i j => (memLp_product_LIP05130 μ hfm hmem i j).coeFn_toLp⟩

end DGPS.Frontier.LIP051
