import DGPS.Frontier.LIP051.T25
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# LIP051.46: Moments of a scalar feature projection

Task id `LIP051.46`, title "Moments of a scalar feature projection" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", size M, leaf formalization, verification V1).
Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.46` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.lip051_46_moments_scalar_feature_projection`: for any measurable
  representatives `f j` of the basis classes `e j` of a real Hilbert basis of `L²(μ)` with
  `e 0 = 1` (μ a probability measure), and any `r : ℕ` and `v : Fin r → ℝ`, the projection
  `Y_v = ∑_{j=1}^r v_j e_j` is measurable, lies in `L²(μ)`, has integral zero, has second moment
  `∑_j v_j²`, and vanishes `μ`-almost everywhere when `∑_j v_j² = 0`.

## R5 notes

1. Abstract task. The campaign identification of `Hw d S.w`, `S.mu` and `S.e` belongs to
   LIP051.01 and is not part of this file. The measure is a probability measure on an arbitrary
   measurable space, and the basis is a parameter of type `HilbertBasis ℕ ℝ (Lp ℝ 2 μ)`.
2. Representatives. The specification's `Y_v` depends on `e_j` only through a representative.
   The main declaration is universally quantified over measurable functions `f j` with
   `f j =ᵐ[μ] e j`, so the conclusions hold for every such choice. Measurability of `Y_v` is the
   only clause that depends on the representative, and it is taken from `hfm`. Existence of such
   representatives is LIP051.25 and is used inside the proof.
3. Positive modes. `Y_v` uses the feature indices `1, …, r`: the coordinate `j : Fin r` is paired
   with the basis index `(j : ℕ) + 1`. The constant mode `e 0` enters only through the hypothesis
   `he0 : e 0 = Lp.const 2 μ 1`, which is the data of LIP051.25 and is used there to obtain the
   positive-mode mean zero. No mode-zero or other positive-mode reading beyond the brief is
   adopted; the statement is not used for index zero.
4. Vector space. `v ∈ ℝ^r` is realized as `Fin r → ℝ`. No norm on `ℝ^r` is used; the second
   moment is written as the explicit sum of squares `∑ j, v j ^ 2`.
5. Integrals are Bochner integrals with respect to `μ`. The second moment is the integral of the
   square of the projection, `∫ (Y_v x)^2 dμ`.
6. Degenerate case. The last clause says that the sum of squares being zero forces `Y_v = 0`
   almost everywhere, as stated. It is proved through `integral_eq_zero_iff_of_nonneg` applied to
   the square of `Y_v`, which is integrable by the `L²` clause.
7. Lean-exposed specification defects: none found. The statement is provable as written for every
   probability measure and every real Hilbert basis with `e 0 = 1`.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- Moments of the scalar feature projection `Y_v = ∑_{j=1}^r v_j e_j` (LIP051.46). -/
theorem lip051_46_moments_scalar_feature_projection
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → α → ℝ) (hfm : ∀ j, Measurable (f j)) (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (r : ℕ) (v : Fin r → ℝ) :
    Measurable (fun x => ∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ∧
      MemLp (fun x => ∑ j : Fin r, v j * f ((j : ℕ) + 1) x) 2 μ ∧
      ∫ x, (∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ∂μ = 0 ∧
      ∫ x, (∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ^ 2 ∂μ = ∑ j : Fin r, v j ^ 2 ∧
      (∑ j : Fin r, v j ^ 2 = 0 →
        (fun x => ∑ j : Fin r, v j * f ((j : ℕ) + 1) x) =ᵐ[μ] 0) := by
  obtain ⟨g, -, hge, hgmem, -, hgint, hgmean⟩ :=
    lip051_25_representative_moments_hilbert_basis μ e he0
  have hfg : ∀ j, f j =ᵐ[μ] g j := fun j => (hfe j).trans (hge j).symm
  have hmem : ∀ j, MemLp (f j) 2 μ := fun j => (hgmem j).ae_eq (hfg j).symm
  have hint : ∀ i j, ∫ x, f i x * f j x ∂μ = if i = j then 1 else 0 := by
    intro i j
    rw [← hgint i j]
    refine integral_congr_ae ?_
    filter_upwards [hfg i, hfg j] with x hi hj
    rw [hi, hj]
  have hint' : ∀ i j : Fin r, ∫ x, f ((i : ℕ) + 1) x * f ((j : ℕ) + 1) x ∂μ
      = if i = j then 1 else 0 := by
    intro i j
    rw [hint]
    simp [Fin.ext_iff]
  have hmean : ∀ j, 1 ≤ j → Integrable (f j) μ ∧ ∫ x, f j x ∂μ = 0 := by
    intro j hj
    refine ⟨(hmem j).integrable one_le_two, ?_⟩
    rw [integral_congr_ae (hfg j)]
    exact (hgmean j hj).2
  have hintf : ∀ j : Fin r, Integrable (f ((j : ℕ) + 1)) μ :=
    fun j => (hmean ((j : ℕ) + 1) (by omega)).1
  have hprod : ∀ i j : Fin r, Integrable (fun x => f ((i : ℕ) + 1) x * f ((j : ℕ) + 1) x) μ :=
    fun i j => (hmem _).integrable_mul (hmem _)
  have hterm : ∀ i j : Fin r,
      Integrable (fun x => (v i * v j) * (f ((i : ℕ) + 1) x * f ((j : ℕ) + 1) x)) μ :=
    fun i j => (hprod i j).const_mul _
  have hYmem : MemLp (fun x => ∑ j : Fin r, v j * f ((j : ℕ) + 1) x) 2 μ :=
    memLp_finsetSum _ (fun j _ => (hmem ((j : ℕ) + 1)).const_mul (v j))
  have hYm : Measurable (fun x => ∑ j : Fin r, v j * f ((j : ℕ) + 1) x) := by
    have h := Finset.measurable_sum (Finset.univ : Finset (Fin r))
      (fun j _ => (hfm ((j : ℕ) + 1)).const_mul (v j))
    simpa [Finset.sum_apply] using h
  have hmeanY : ∫ x, (∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ∂μ = 0 := by
    rw [integral_finsetSum _ (fun j _ => (hintf j).const_mul (v j))]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, (hmean ((j : ℕ) + 1) (by omega)).2, mul_zero]
  have hsq : ∀ x, (∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ^ 2
      = ∑ i : Fin r, ∑ j : Fin r, (v i * v j) * (f ((i : ℕ) + 1) x * f ((j : ℕ) + 1) x) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinner : ∀ i : Fin r,
      ∫ x, ∑ j : Fin r, (v i * v j) * (f ((i : ℕ) + 1) x * f ((j : ℕ) + 1) x) ∂μ
        = ∑ j : Fin r, (v i * v j) * (if i = j then 1 else 0) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hterm i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hint' i j]
  have hsecond : ∫ x, (∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ^ 2 ∂μ
      = ∑ j : Fin r, v j ^ 2 := by
    simp only [hsq]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
    refine (Finset.sum_congr rfl fun i _ => hinner i).trans ?_
    simp [mul_ite, sq]
  refine ⟨hYm, hYmem, hmeanY, hsecond, ?_⟩
  intro hzero
  have hsqint : Integrable (fun x => (∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ^ 2) μ :=
    hYmem.integrable_sq
  have hae : (fun x => (∑ j : Fin r, v j * f ((j : ℕ) + 1) x) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsqint).mp (hsecond.trans hzero)
  filter_upwards [hae] with x hx
  simpa using hx

end DGPS.Frontier.LIP051
