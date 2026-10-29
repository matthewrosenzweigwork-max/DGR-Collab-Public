import DGPS.Frontier.LIP051.T25
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# LIP051.30: Orthonormality of product functions

Task id `LIP051.30`, title "Orthonormality of product functions" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", category leaf formalization, verification
V1). Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.30` statement and
proof. Proved input: `LIP051.25` (`DGPS.Frontier.LIP051.T25`).

## Provides

* `DGPS.Frontier.LIP051.lip051_30_orthonormality_product_functions`: for a probability measure
  `μ` and a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, there are measurable
  representatives `f j` of the classes `e j` (the representatives of `LIP051.25`) such that each
  product `(x, y) ↦ f i x * f j y` is in `L²(μ ⊗ μ)`, and there are `L²(μ ⊗ μ)` classes `P i j`
  of these products whose real inner products are `δ_ik δ_jl`.
* `DGPS.Frontier.LIP051.memLp_product_LIP05130`: helper; the product of two `L²(μ)` functions
  of separate coordinates is in `L²(μ ⊗ μ)`, for measurable functions.
* `DGPS.Frontier.LIP051.product_orthonormal_LIP05130`: helper; for measurable `L²(μ)`
  functions with `∫ f i f j dμ = δ_ij`, the product classes have inner products `δ_ik δ_jl`.

## R5 notes

1. Ambient data. `μ` is an arbitrary probability measure on an arbitrary measurable space `α`
   (the specification's "probability measure on a measurable space"); no topology or standard
   Borel hypothesis is added. The product measure is Mathlib's `μ.prod μ`, i.e. `μ ⊗ μ`.
2. Hilbert basis and `e 0 = 1`. The Hilbert basis `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)` and the
   hypothesis `he0 : e 0 = Lp.const 2 μ 1` are kept exactly as in `LIP051.25`, because the
   statement is "for the representatives in .25". The orthonormality clauses themselves do not
   use `he0`: they follow from the covariance identities of `.25`, which are the only input
   from `.25` used in the proof, and those identities hold for all indices, including `0`.
   Removing `he0` would give a stronger, unrequested statement, so it is not done here.
3. Representatives. "The representatives in `.25`" is read as an existential: there exist
   measurable `f j` with `f j =ᵐ[μ] e j` for which the product clauses hold. The product clauses
   do not depend on the choice of representatives, since changing `f i` or `f j` on a `μ`-null set
   changes `f i x * f j y` only on a `μ ⊗ μ`-null set. The existential is that of `.25`; it is
   not a weakening of the representative-free content.
4. Products as `L²` classes. The specification's `e_i ⊗ e_j` is recorded in two forms. The
   clause `MemLp (fun p => f i p.1 * f j p.2) 2 (μ.prod μ)` is membership in `L²(μ ⊗ μ)`. The
   classes `P i j : Lp ℝ 2 (μ.prod μ)` are the `L²` elements with `P i j =ᵐ[μ.prod μ]` the
   product function, and the inner product of `L²(μ ⊗ μ)` is the specification's `⟨·,·⟩`. The
   class `P i j` is unique up to `μ ⊗ μ`-a.e. equality, so the inner products do not depend on
   its choice.
5. Indexing. All indices `i, j, k, l` range over all of `ℕ`, including `0`, exactly as the
   specification's `(i,j,k,l ∈ ℕ)` states. No positive-mode restriction is imposed. The
   zero-mode issue recorded in `campaign/frontier/DEFECTS.md` (FD-002) concerns the centered
   Gaussian limit of `LIP051` and its binder, where index `0` is refuted for the Gaussian
   coordinates. This orthonormality statement contains no Gaussian object, so FD-002 does not
   apply to it, and index `0` is kept as the specification writes it. Orthonormality of the product family is true including mode zero, since
   `e 0 = 1` is orthonormal to the other modes in `L²(μ)`.
6. Kronecker symbols. `δ_ik δ_jl` is formalized as `(if i = k then 1 else 0) * (if j = l then 1
   else 0)` in `ℝ`. The inner product of real `L²` classes is symmetric, so no conjugation or
   order convention affects the statement.
7. Proof route. The specification proposes Tonelli for the norm and Fubini to factor the
   integral. The Lean proof instead uses `MemLp.integrable_sq` with `Integrable.mul_prod` for
   square-integrability of the product, and `integral_prod_mul` (Fubini for a product of
   functions of separate coordinates, unconditional in Mathlib) for the factorization of the
   inner product. This is a change of route only; the statement is the specification's.
8. Measurability. "Measurable" is Mathlib's `Measurable`, which is stronger than the
   a.e.-measurable class property and is supplied by `LIP051.25`. Only the measurability of
   the product functions (on the product σ-algebra) is used in the proof.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- The product of two `L²(μ)` functions of separate coordinates is in `L²(μ ⊗ μ)`. -/
theorem memLp_product_LIP05130 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : ℕ → α → ℝ} (hm : ∀ j, Measurable (f j))
    (hmem : ∀ j, MemLp (f j) 2 μ) (i j : ℕ) :
    MemLp (fun p : α × α => f i p.1 * f j p.2) 2 (μ.prod μ) := by
  have hmeas : Measurable (fun p : α × α => f i p.1 * f j p.2) :=
    ((hm i).comp measurable_fst).mul ((hm j).comp measurable_snd)
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr ?_
  have hsq : Integrable (fun p : α × α => f i p.1 ^ 2 * f j p.2 ^ 2) (μ.prod μ) :=
    Integrable.mul_prod (hmem i).integrable_sq (hmem j).integrable_sq
  refine hsq.congr (ae_of_all _ fun p => ?_)
  simp only [mul_pow]

/-- Orthonormality of the product classes for measurable `L²(μ)` functions with
`∫ f i f j dμ = δ_ij`. -/
theorem product_orthonormal_LIP05130 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : ℕ → α → ℝ} (hm : ∀ j, Measurable (f j))
    (hmem : ∀ j, MemLp (f j) 2 μ)
    (hcov : ∀ i j, ∫ x, f i x * f j x ∂μ = if i = j then 1 else 0) :
    ∃ P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ),
      (∀ i j, (P i j : α × α → ℝ) =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2) ∧
      ∀ i j k l, inner ℝ (P i j) (P k l) = (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  have hmemP := memLp_product_LIP05130 μ hm hmem
  refine ⟨fun i j => (hmemP i j).toLp (fun p => f i p.1 * f j p.2),
    fun i j => (hmemP i j).coeFn_toLp, ?_⟩
  intro i j k l
  rw [L2.inner_def]
  calc ∫ a, inner ℝ ((hmemP i j).toLp (fun p => f i p.1 * f j p.2) a)
        ((hmemP k l).toLp (fun p => f k p.1 * f l p.2) a) ∂(μ.prod μ)
      = ∫ p, (f i p.1 * f j p.2) * (f k p.1 * f l p.2) ∂(μ.prod μ) := by
        refine integral_congr_ae ?_
        filter_upwards [(hmemP i j).coeFn_toLp, (hmemP k l).coeFn_toLp] with p h1 h2
        simp only [h1, h2, RCLike.inner_apply, conj_trivial]
        ring
    _ = ∫ z, (fun x => f i x * f k x) z.1 * (fun y => f j y * f l y) z.2 ∂(μ.prod μ) := by
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        show f i p.1 * f j p.2 * (f k p.1 * f l p.2) = f i p.1 * f k p.1 * (f j p.2 * f l p.2)
        ring
    _ = (∫ x, f i x * f k x ∂μ) * (∫ y, f j y * f l y ∂μ) :=
        integral_prod_mul (fun x => f i x * f k x) (fun y => f j y * f l y)
    _ = _ := by rw [hcov i k, hcov j l]

/-- LIP051.30: orthonormality of the product functions `e_i(x) e_j(y)` in `L²(μ ⊗ μ)`, for the
measurable representatives of `LIP051.25`. -/
theorem lip051_30_orthonormality_product_functions {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (he0 : e 0 = Lp.const 2 μ (1 : ℝ)) :
    ∃ f : ℕ → α → ℝ, (∀ j, Measurable (f j)) ∧ (∀ j, f j =ᵐ[μ] (e j : α → ℝ)) ∧
      (∀ i j, MemLp (fun p : α × α => f i p.1 * f j p.2) 2 (μ.prod μ)) ∧
      ∃ P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ),
        (∀ i j, (P i j : α × α → ℝ) =ᵐ[μ.prod μ] fun p => f i p.1 * f j p.2) ∧
        ∀ i j k l,
          inner ℝ (P i j) (P k l) = (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  obtain ⟨f, hm, hae, hmem, -, hcov, -⟩ :=
    lip051_25_representative_moments_hilbert_basis μ e he0
  obtain ⟨P, hP, hinner⟩ := product_orthonormal_LIP05130 μ hm hmem hcov
  exact ⟨f, hm, hae, fun i j => memLp_product_LIP05130 μ hm hmem i j, P, hP, hinner⟩

end DGPS.Frontier.LIP051
