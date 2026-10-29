import DGPS.Frontier.LIP051.T30
import DGPS.Frontier.LIP051.T31

/-!
# LIP051.05: Completeness of the product basis

Task id `LIP051.05`, title "Completeness of the product basis" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1). Proved inputs:
`LIP051.30` (`DGPS.Frontier.LIP051.T30`, orthonormality of the product functions) and
`LIP051.31` (`DGPS.Frontier.LIP051.T31`, totality of the product family).

## Provides

* `DGPS.Frontier.LIP051.lip051_05_completeness_product_basis`: for a probability measure `μ`
  on a measurable space `α` and a real Hilbert basis `e` of `L²(μ)` indexed by `ℕ`, there are
  measurable representatives `f j` of the classes `e j`, and `L²(μ ⊗ μ)` classes `P i j` of the
  products `(x, y) ↦ f i x * f j y`, such that (i) the inner products of the `P i j` are the
  Kronecker products `δ_ik δ_jl` (orthonormality over all natural pairs); (ii) every
  `F ∈ L²(μ ⊗ μ)` orthogonal to all `P i j` is zero, both almost everywhere and as an element of
  `L²(μ ⊗ μ)` (the function form of totality); (iii) the closure of the linear span of the
  family is the whole space `L²(μ ⊗ μ)` (the span form of totality).
* `DGPS.Frontier.LIP051.integral_mul_eq_inner_LIP05105` (helper): for representatives `f i` of
  the basis classes, `∫ f i * f j dμ` equals the `L²(μ)` inner product `⟪e i, e j⟫`.

## R5 notes

1. Ambient data. `μ` is an arbitrary probability measure on an arbitrary measurable space `α`.
   No topology, standard Borel hypothesis, torus, `Spec`, `KData`, `Hw`, kernel `K` or Wick
   object occurs. The identification of `μ` with `S.mu`, of `e` with the LIP009 basis, and the
   transport to the campaign declaration belong to LIP051.01, not to this unit.
2. The Hilbert basis. The specification's `e_i` is an arbitrary real Hilbert basis
   `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)`. Completeness and orthonormality of `e` are part of the
   type of `e`; they are the only properties of `e` used.
3. Normalization `e 0 = 1` (deliberate difference from LIP051.30). LIP051.30 takes the
   hypothesis `he0 : e 0 = Lp.const 2 μ 1`, as the node preamble does for the LIP009 basis. This
   unit does not take it: neither the orthonormality clause nor the totality clause uses it, and
   the statement is proved for every basis. This is a strictly stronger reading than the one with
   `he0`, and no hypothesis that the specification does not list is added.
4. Representatives. "The function `e_i(x) e_j(y)`" is read as the class of the product of
   chosen representatives. The representatives are existential: there exist measurable `f j`
   with `f j =ᵐ[μ] e j`. Any other choice of representatives changes the products only on a
   `μ ⊗ μ`-null set, so the conclusions do not depend on the choice.
5. Products as `L²` classes. The class `P i j : Lp ℝ 2 (μ.prod μ)` is the `L²` element with
   `P i j =ᵐ[μ.prod μ]` the product function. It is unique up to `μ ⊗ μ`-a.e. equality, so the
   inner products below do not depend on that choice. Square integrability of every product is
   supplied by LIP051.30 (`memLp_product_LIP05130`) and enters through the existence of `P`.
6. Indexing and mode zero (FD-002). The specification says "indexed by all natural pairs", so
   every index `i, j, k, l` ranges over all of `ℕ`, including `0`, and no positive-mode
   restriction is imposed. FD-002 (`campaign/frontier/DEFECTS.md`) concerns the centered Gaussian
   limit of LIP051, where index `0` is refuted because the zero mode equals `sqrt N`. This unit
   contains no Gaussian object, so FD-002 does not apply to it, and the constant mode is kept as
   the specification writes it. This reading is the same as in LIP051.30 and LIP051.31.
7. Orthonormality. Stated with Kronecker products in `ℝ`:
   `inner ℝ (P i j) (P k l) = (if i = k then 1 else 0) * (if j = l then 1 else 0)`. The real
   inner product is symmetric, so no conjugation or order convention affects it.
8. Completeness of the product family. The equivalence stated in the specification is not used
   as a black box. Both forms are proved: the function form (every `F` orthogonal to all products
   is zero a.e. and equal to `0` in `L²`) and the span form (the topological closure of the
   real linear span of the products is `⊤`). Both are taken from LIP051.31, which proves them for
   any `P` with `P i j =ᵐ[μ ⊗ μ]` the product of representatives of `e`.
9. Proof route. The specification's proof (orthonormality by LIP051.30, totality by LIP051.31,
   then the orthogonal complement argument) is followed in this order. The orthogonal complement
   step is the one inside LIP051.31 (`Submodule.topologicalClosure_eq_top_iff`). Orthonormality
   of the products is obtained from `product_orthonormal_LIP05130` with the covariance identity
   of the representatives, proved here by `integral_mul_eq_inner_LIP05105`, so that the statement
   does not depend on LIP051.25 and its `e 0 = 1` hypothesis.
10. Measurability. "Measurable" is Mathlib's `Measurable`. It is used only for the representatives
   `f j` supplied by `representative_exists_LIP05125`.
11. Lean-exposed specification defects in this unit: none found.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- For representatives `f i` of the classes of a real Hilbert basis `e` of `L²(μ)`, the integral
of the product `f i * f j` is the `L²(μ)` inner product `⟪e i, e j⟫`. -/
lemma integral_mul_eq_inner_LIP05105 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ} (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (i j : ℕ) : ∫ x, f i x * f j x ∂μ = inner ℝ (e i) (e j) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hfe i, hfe j] with x hi hj
  rw [hi, hj]
  simp [mul_comm]

/-- Completeness of the product basis (LIP051.05). For a probability measure `μ` and a real
Hilbert basis `e` of `L²(μ)` indexed by `ℕ`, there are measurable representatives `f j` of the
classes `e j` and classes `P i j` of the products `f i p.1 * f j p.2` in `L²(μ ⊗ μ)` such that
the family `(P i j)` over all natural pairs is orthonormal, every `F ∈ L²(μ ⊗ μ)` orthogonal to
all `P i j` is zero (a.e., and in `L²`), and the closed linear span of the family is all of
`L²(μ ⊗ μ)`. See the module docstring, R5 notes. -/
theorem lip051_05_completeness_product_basis {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) :
    ∃ f : ℕ → α → ℝ, (∀ j, Measurable (f j)) ∧ (∀ j, f j =ᵐ[μ] (e j : α → ℝ)) ∧
      ∃ P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ),
        (∀ i j, (P i j : α × α → ℝ) =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2) ∧
        (∀ i j k l,
          inner ℝ (P i j) (P k l) = (if i = k then 1 else 0) * (if j = l then 1 else 0)) ∧
        (∀ F : Lp ℝ 2 (μ.prod μ), (∀ i j, inner ℝ F (P i j) = 0) →
          (F : α × α → ℝ) =ᵐ[μ.prod μ] 0 ∧ F = 0) ∧
        (Submodule.span ℝ (Set.range fun q : ℕ × ℕ => P q.1 q.2)).topologicalClosure = ⊤ := by
  choose f hfm hfe using fun j => representative_exists_LIP05125 μ (e j)
  have hmem : ∀ j, MemLp (f j) 2 μ := fun j => (Lp.memLp (e j)).ae_eq (hfe j).symm
  have hcov : ∀ i j, ∫ x, f i x * f j x ∂μ = if i = j then 1 else 0 := by
    intro i j
    rw [integral_mul_eq_inner_LIP05105 μ e hfe i j]
    exact orthonormal_iff_ite.mp e.orthonormal i j
  obtain ⟨P, hP, hinner⟩ := product_orthonormal_LIP05130 μ hfm hmem hcov
  obtain ⟨hzero, htot⟩ := lip051_31_totality_product_family μ e f hfe P hP
  exact ⟨f, hfm, hfe, P, hP, hinner, hzero, htot⟩

end DGPS.Frontier.LIP051
