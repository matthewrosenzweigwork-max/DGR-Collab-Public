import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# LIP051.25: Representative moments from a Hilbert basis

Task id `LIP051.25`, title "Representative moments from a Hilbert basis" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", category shared infrastructure,
verification V2). Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the
`LIP051.25` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.lip051_25_representative_moments_hilbert_basis`: for a probability
  measure `μ` on a measurable space and a real Hilbert basis `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)`
  with `e 0 = Lp.const 2 μ 1`, there are measurable representatives `f j` of the classes `e j`
  such that every `f j` lies in `L²(μ)`, every product `f i * f j` is integrable with integral
  `if i = j then 1 else 0`, and for `1 ≤ j` the function `f j` is integrable with mean zero.
* `DGPS.Frontier.LIP051.representative_exists_LIP05125`: helper; every real `L²(μ)` class has a
  measurable representative that agrees with it `μ`-almost everywhere.

## R5 notes

1. Abstract statement. The Hilbert basis is a parameter, exactly as the specification says
   ("The abstract task takes the Hilbert basis as a parameter"). The campaign identification of
   `Hw d S.w`, `S.mu`, `S.e` and `S.v` belongs to LIP051.01 (`DGPS.Frontier.LIP051.T01`), which
   this file does not import. Nothing about `Spec`, `Aux`, `KData` or `InteractionData` is used.
2. Probability measure. `[IsProbabilityMeasure μ]` is the specification's "probability on a
   measurable space". It is used for finiteness of `μ` (`Lp.const`, and `L²`-to-`L¹`
   integrability). The measurable space `α` is arbitrary; no standard Borel or topological
   hypothesis is added.
3. Hilbert basis. `HilbertBasis ℕ ℝ (Lp ℝ 2 μ)` is Mathlib's structure, an isometric
   identification of `Lp ℝ 2 μ` with `ℓ²(ℕ, ℝ)`. Only its orthonormality (`e.orthonormal`) is
   used. Completeness is not needed for this unit and is not assumed beyond the type.
4. Basis constant. "`e_0 = 1` as an `L²` class" is read as the Lean equality
   `e 0 = Lp.const 2 μ (1 : ℝ)`. This is the class equality, equivalent to `e 0 =ᵐ[μ] 1`. It is a
   hypothesis of the theorem, not a consequence, because the specification lists it as data.
5. Representatives. The conclusion is existential, so "there are measurable representatives"
   is read literally. "Measurable" is read as Mathlib's `Measurable` (Borel on `ℝ`), which is
   stronger than the a.e.-measurable class property and is obtained from
   `AEStronglyMeasurable.stronglyMeasurable_mk`. The representative `f j` is only fixed up to
   `μ`-a.e. equality, as the specification states; the file does not claim `f 0 x = 1` for every
   `x`.
6. Specification clauses, in the order of the statement:
   `e_j ∈ L²(μ)` is `MemLp (f j) 2 μ` for every `j`; `e_i e_j ∈ L¹(μ)` is
   `Integrable (fun x => f i x * f j x) μ` for all `i j : ℕ`; `∫ e_i e_j dμ = δ_ij` is
   `∫ x, f i x * f j x ∂μ = if i = j then 1 else 0` for all `i j : ℕ`, obtained from
   `L2.inner_def` and orthonormality of `e`.
7. Positive-mode indexing. Index `0` is quantified in the orthonormality and product clauses,
   exactly as the specification does. The mean-zero clause is restricted to `1 ≤ j`, as the
   specification states; the file never claims `∫ f 0 dμ = 0`, which is false (the integral is
   `1`). The positive-mode binder of LIP051 (DEFECTS.md FD-002) concerns the joint Gaussian
   statement over `s : Finset ℕ` in LIP016; this file contains no Gaussian object and does not
   touch that binder.
8. Integrals are Bochner integrals with respect to `μ`. The product `f i * f j` is the pointwise
   product of the chosen representatives; by `μ`-a.e. equality it agrees a.e. with `e i * e j`
   for any other choice, so the statements are representative independent.
9. Lean-exposed specification defects: none found. The statement as written is provable and
   true for every probability measure `μ` and every real Hilbert basis with `e 0 = 1`.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- Every real `L²(μ)` class has a measurable representative, equal `μ`-a.e. to the class. -/
theorem representative_exists_LIP05125 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : Lp ℝ 2 μ) : ∃ f : α → ℝ, Measurable f ∧ f =ᵐ[μ] (g : α → ℝ) :=
  ⟨_, (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.measurable,
    (Lp.aestronglyMeasurable g).ae_eq_mk.symm⟩

/-- Representative moments from a real Hilbert basis of `L²(μ)` with `e 0 = 1`. -/
theorem lip051_25_representative_moments_hilbert_basis
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ)) :
    ∃ f : ℕ → α → ℝ, (∀ j, Measurable (f j)) ∧ (∀ j, f j =ᵐ[μ] (e j : α → ℝ)) ∧
      (∀ j, MemLp (f j) 2 μ) ∧
      (∀ i j, Integrable (fun x => f i x * f j x) μ) ∧
      (∀ i j, ∫ x, f i x * f j x ∂μ = if i = j then 1 else 0) ∧
      (∀ j, 1 ≤ j → Integrable (f j) μ ∧ ∫ x, f j x ∂μ = 0) := by
  have hrep : ∀ j, ∃ f : α → ℝ, Measurable f ∧ f =ᵐ[μ] (e j : α → ℝ) :=
    fun j => representative_exists_LIP05125 μ (e j)
  choose f hfm hfe using hrep
  have hmem : ∀ j, MemLp (f j) 2 μ := fun j => (Lp.memLp (e j)).ae_eq (hfe j).symm
  have hprod : ∀ i j, Integrable (fun x => f i x * f j x) μ := fun i j =>
    (hmem i).integrable_mul (hmem j)
  have hinner : ∀ i j, ∫ x, f i x * f j x ∂μ = inner ℝ (e i) (e j) := by
    intro i j
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfe i, hfe j] with x hi hj
    rw [hi, hj]
    simp [mul_comm]
  have horth : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0 :=
    fun i j => orthonormal_iff_ite.mp e.orthonormal i j
  have he0' : (e 0 : α → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) := by
    rw [he0]
    exact Lp.coeFn_const _ _ _
  have hf0 : f 0 =ᵐ[μ] fun _ => (1 : ℝ) := (hfe 0).trans he0'
  have hmean : ∀ j, j ≠ 0 → ∫ x, f j x ∂μ = 0 := by
    intro j hj
    have h1 : ∫ x, f j x * f 0 x ∂μ = ∫ x, f j x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hf0] with x hx
      simp [hx]
    rw [← h1, hinner j 0, horth j 0]
    simp [hj]
  exact ⟨f, hfm, hfe, hmem, hprod, fun i j => (hinner i j).trans (horth i j),
    fun j hj => ⟨(hmem j).integrable one_le_two, hmean j (by omega)⟩⟩

end DGPS.Frontier.LIP051
