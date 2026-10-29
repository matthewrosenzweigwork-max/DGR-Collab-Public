import DGPS.Frontier.LIP051.T02
import DGPS.Frontier.LIP051.T03

/-!
# LIP051.07: Finite diagonal integral

Task id `LIP051.07`, title "Finite diagonal integral" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", leaf formalization, verification V1,
dispatch tier 4). Source: the `LIP051.07` statement and proof in the node document for LIP051.

Let `μ` be a probability measure on the torus and `K` the centered kernel of a bounded continuous
symmetric `W` (LIP051.03), so that `K(x,x)` is integrable and `d_K = ∫ K(x,x) dμ`. Let `e j`
(`j ≥ 1`) be real representatives of an orthonormal family of `L²(μ)`. For positive indices put
`T i j = ∬ K(x,y) e i(x) e j(y) dμ(x) dμ(y)`, `K_R(x,y) = ∑_{i,j=1}^R T i j e i(x) e j(y)` and
`F_R = K - K_R`. For every `R`, the diagonal `x ↦ K_R(x,x)` is integrable with integral
`tr T_R = ∑_{i=1}^R T i i`, and `x ↦ F_R(x,x)` is integrable with integral `d_K - tr T_R`.
No bound uniform in `R` is asserted.

## Provides

* `DGPS.Frontier.LIP051.tIJ_LIP05107`: the coefficient `T i j = ∬ K(x,y) e i(x) e j(y) dμ dμ`
  on the product measure `μ.prod μ`.
* `DGPS.Frontier.LIP051.kernelRankLIP05107`: the finite-rank section
  `K_R(x,y) = ∑_{i,j=1}^R T i j e i(x) e j(y)`, indices `1..R` (empty sums for `R = 0`).
* `DGPS.Frontier.LIP051.finite_diagonal_general_LIP05107`: helper; for any kernel `K` with
  integrable diagonal and any family `e` with the positive-index hypotheses, the four clauses of
  the statement (integrability and integral of the diagonal of `K_R`, integrability and integral
  of the diagonal of `F_R`).
* `DGPS.Frontier.LIP051.lip051_07_finite_diagonal_integral`: main statement; for the centered
  kernel `K = centeredKernelOf_LIP05103 μ W` of a bounded continuous `W` on the torus and a
  family `e` with `MemLp (e j) 2 μ` and `∫ e i e j dμ = δ_ij` for positive `i, j`, every `R`
  satisfies the four clauses above.
* `DGPS.Frontier.LIP051.lip051_07_finite_diagonal_integral_of_basis`: corollary; for any Hilbert
  basis `e` of `L²(μ)` with `e 0 = 1`, LIP051.02 supplies measurable representatives for which
  the main statement holds for every `R`.

## R5 notes

1. Scope of the statement. The statement is for the torus measure `μ : Measure (DGPS.Torus d)`
   with `[IsProbabilityMeasure μ]` and the centered kernel `K = centeredKernelOf_LIP05103 μ W`
   of LIP051.03. The hypotheses are continuity of `Function.uncurry W` and the uniform bound
   `|W x y| ≤ M`, which are exactly what the integrability of the diagonal needs. Symmetry of `W`
   and `0 ≤ M` are not assumed, because the statement does not use them. The general helper
   takes an arbitrary kernel `K` whose diagonal is integrable; that is the only property of `K`
   used.
2. Positive-mode indexing (FD-002 reading). Every sum in the statement runs over positive indices
   `Finset.Icc 1 R`, and the coefficients `T i j` are indexed by positive `i, j`. Mode zero is
   excluded from the section `K_R`, from the trace `tr T_R`, and from the orthonormality and
   integrability hypotheses (`hL2` and `hon` quantify only over `1 ≤ i, j`). The statement makes
   no claim about `e 0`, and `e 0 = 1` is not used. No Gaussian limit is asserted here, so the
   zero-mode refutation recorded in FD-002 does not apply to this unit. `R = 0` gives empty sums,
   so `K_0 = 0`, `tr T_0 = 0` and `F_0 = K`.
3. Feature hypotheses. The family `e : ℕ → Torus d → ℝ` is read as a family of pointwise
   functions, not as `L²` classes. The hypotheses are `MemLp (e j) 2 μ` for `1 ≤ j`, and
   `∫ e i e j dμ = if i = j then 1 else 0` for `1 ≤ i`, `1 ≤ j`. The specification says "Hilbert
   basis"; only the positive part of the orthonormality is used, so the hypothesis is weaker than
   the full basis property, and the theorem is correspondingly stronger. Measurability of `e j` is
   not assumed, because `MemLp` supplies the strong measurability needed for integrability.
   Different a.e.-representatives of `e` change neither the integrals nor the integrability.
4. Pointwise diagonal. `K_R(x,x)` and `F_R(x,x)` are the pointwise values of the displayed
   formulas at the chosen functions `e`. The kernel `K` is used pointwise as given, including on
   the diagonal; no almost-everywhere representative of `K` is taken, in line with the node's
   caution about the original diagonal.
5. Coefficients. The double integral `∬ dμ(x) dμ(y)` is written as the Bochner integral over
   `μ.prod μ` of `(x,y) ↦ K x y * e i x * e j y`. The statement does not prove that this integrand
   is integrable (it is, since `K ∈ L²(μ⊗μ)` by LIP051.03 and `e i ⊗ e j ∈ L²(μ⊗μ)`), and does
   not need it: every identity used is linear in the real numbers `T i j`, and the diagonal
   computation only uses the integrals `∫ e i e j dμ`.
6. Diagonal integrals. "The diagonal `K_R(x,x)` is L1" is read as `Integrable` for the pointwise
   function. Its integral is computed term by term: `∫ T i j e i e j dμ = T i j δ_ij`, with
   `δ_ij` from the orthonormality hypothesis, and the Kronecker sum collapses to `tr T_R`.
7. Diagonal of `F_R`. The statement "`δ_R` is L1 with integral `d_K - tr T_R`" is read as
   `Integrable (fun x => K x x - K_R x x)` together with the equality of Bochner integrals
   `∫ (K x x - K_R x x) = ∫ K x x - tr T_R`. The integrability of `x ↦ K(x,x)` is supplied by
   LIP051.03 (`|K(x,x)| ≤ 4M` and measurability), and `d_K` is that integral.
8. Uniformity. No bound uniform in `R` is stated or used, as the specification requires.
9. "For every fixed `R`" is the quantifier `∀ R : ℕ` placed after the hypotheses in the main
   statement, so that the family `e` and the kernel do not depend on `R`.
10. Representatives in the corollary. LIP051.02's main statement is applied to a Hilbert basis
    `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)` with `e 0 = Lp.const 2 μ 1` and the centered kernel. Its
    existence clause gives measurable, `L²`, orthonormal representatives `f`. The corollary
    concludes existence of such `f` together with the main statement for `f`. The mean-zero
    clause and the replacement clause of LIP051.02 are not used here.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- The coefficient `T i j = ∬ K(x,y) e i(x) e j(y) dμ(x) dμ(y)`, as the integral over the
product measure `μ.prod μ`. -/
noncomputable def tIJ_LIP05107 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (K : α → α → ℝ) (e : ℕ → α → ℝ) (i j : ℕ) : ℝ :=
  ∫ p, K p.1 p.2 * e i p.1 * e j p.2 ∂(μ.prod μ)

/-- The finite-rank section `K_R(x,y) = ∑_{i,j=1}^R T i j e i(x) e j(y)`, indices `1..R`. -/
noncomputable def kernelRankLIP05107 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (K : α → α → ℝ) (e : ℕ → α → ℝ) (R : ℕ) (x y : α) : ℝ :=
  ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R, tIJ_LIP05107 μ K e i j * e i x * e j y

/-- A general finite-rank diagonal integral: for any kernel with integrable diagonal and any
positive-index orthonormal `L²` family, the diagonal of `K_R` is integrable with integral
`∑_{i=1}^R T i i`, and the diagonal of `K - K_R` is integrable with integral
`d_K - ∑_{i=1}^R T i i`. -/
theorem finite_diagonal_general_LIP05107 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (K : α → α → ℝ) (hKd : Integrable (fun x => K x x) μ)
    (e : ℕ → α → ℝ) (hL2 : ∀ j, 1 ≤ j → MemLp (e j) 2 μ)
    (hon : ∀ i j, 1 ≤ i → 1 ≤ j → ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0) (R : ℕ) :
    Integrable (fun x => kernelRankLIP05107 μ K e R x x) μ ∧
    (∫ x, kernelRankLIP05107 μ K e R x x ∂μ) = ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ K e i i ∧
    Integrable (fun x => K x x - kernelRankLIP05107 μ K e R x x) μ ∧
    (∫ x, (K x x - kernelRankLIP05107 μ K e R x x) ∂μ)
      = (∫ x, K x x ∂μ) - ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ K e i i := by
  have hprod : ∀ i j, 1 ≤ i → 1 ≤ j → Integrable (fun x => e i x * e j x) μ :=
    fun i j hi hj => (hL2 i hi).integrable_mul (hL2 j hj)
  have hterm : ∀ i j, 1 ≤ i → 1 ≤ j →
      Integrable (fun x => tIJ_LIP05107 μ K e i j * e i x * e j x) μ := by
    intro i j hi hj
    simpa only [mul_assoc] using (hprod i j hi hj).const_mul (tIJ_LIP05107 μ K e i j)
  have hcol : ∀ i ∈ Finset.Icc 1 R,
      Integrable (fun x => ∑ j ∈ Finset.Icc 1 R, tIJ_LIP05107 μ K e i j * e i x * e j x) μ :=
    fun i hi => integrable_finsetSum _ fun j hj =>
      hterm i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1
  have hint : Integrable (fun x => kernelRankLIP05107 μ K e R x x) μ :=
    integrable_finsetSum _ hcol
  have hterm_int : ∀ i j, 1 ≤ i → 1 ≤ j →
      ∫ x, tIJ_LIP05107 μ K e i j * e i x * e j x ∂μ
        = tIJ_LIP05107 μ K e i j * (if i = j then 1 else 0) := by
    intro i j hi hj
    rw [← hon i j hi hj, ← integral_const_mul]
    congr 1
    funext x
    ring
  have hintegral : (∫ x, kernelRankLIP05107 μ K e R x x ∂μ)
      = ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ K e i i := by
    unfold kernelRankLIP05107
    rw [integral_finsetSum _ hcol]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [integral_finsetSum _ fun j hj =>
      hterm i j hi1 (Finset.mem_Icc.mp hj).1]
    have hsum : ∑ j ∈ Finset.Icc 1 R, (∫ x, tIJ_LIP05107 μ K e i j * e i x * e j x ∂μ)
        = ∑ j ∈ Finset.Icc 1 R, tIJ_LIP05107 μ K e i j * (if i = j then 1 else 0) :=
      Finset.sum_congr rfl fun j hj => hterm_int i j hi1 (Finset.mem_Icc.mp hj).1
    rw [hsum]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hi, ↓reduceIte]
  refine ⟨hint, hintegral, hKd.sub hint, ?_⟩
  rw [integral_sub hKd hint, hintegral]

/-- **LIP051.07.** Finite diagonal integral. For the centered kernel `K` of a bounded continuous
`W` on the torus and a family `e` of real functions with `e j ∈ L²(μ)` and
`∫ e i e j dμ = δ_ij` for positive `i, j`, every `R` satisfies: the diagonal of `K_R` is integrable
with integral `∑_{i=1}^R T i i`, and the diagonal of `F_R = K - K_R` is integrable with integral
`d_K - ∑_{i=1}^R T i i`. -/
theorem lip051_07_finite_diagonal_integral {d : ℕ}
    (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) {M : ℝ} (hWc : Continuous (Function.uncurry W))
    (hb : ∀ x y, |W x y| ≤ M)
    (e : ℕ → DGPS.Torus d → ℝ) (hL2 : ∀ j, 1 ≤ j → MemLp (e j) 2 μ)
    (hon : ∀ i j, 1 ≤ i → 1 ≤ j → ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0) :
    ∀ R : ℕ,
      Integrable (fun x => kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) e R x x) μ ∧
      (∫ x, kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) e R x x ∂μ)
        = ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) e i i ∧
      Integrable (fun x => centeredKernelOf_LIP05103 μ W x x
        - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) e R x x) μ ∧
      (∫ x, (centeredKernelOf_LIP05103 μ W x x
        - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) e R x x) ∂μ)
        = (∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ)
          - ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) e i i := by
  intro R
  exact finite_diagonal_general_LIP05107 μ (centeredKernelOf_LIP05103 μ W)
    (lip051_03_centering_integrability_original_kernel_dK (μ := μ) hWc hb).1 e hL2 hon R

/-- Corollary: for any Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, LIP051.02 gives measurable
`L²` orthonormal representatives `f` for which the main statement holds for every `R`. -/
theorem lip051_07_finite_diagonal_integral_of_basis {d : ℕ}
    (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) {M : ℝ} (hWc : Continuous (Function.uncurry W))
    (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ)) :
    ∃ f : ℕ → DGPS.Torus d → ℝ, (∀ j, MemLp (f j) 2 μ) ∧
      (∀ i j, ∫ x, f i x * f j x ∂μ = if i = j then 1 else 0) ∧
      ∀ R : ℕ,
        Integrable (fun x => kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) f R x x) μ ∧
        (∫ x, kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) f R x x ∂μ)
          = ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) f i i ∧
        Integrable (fun x => centeredKernelOf_LIP05103 μ W x x
          - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) f R x x) μ ∧
        (∫ x, (centeredKernelOf_LIP05103 μ W x x
          - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) f R x x) ∂μ)
          = (∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ)
            - ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) f i i := by
  have hKd : Integrable (fun x => centeredKernelOf_LIP05103 μ W x x) μ :=
    (lip051_03_centering_integrability_original_kernel_dK (μ := μ) hWc hb).1
  obtain ⟨_, f, _, hmem, hon, _, _⟩ :=
    lip051_02_centered_measurable_feature_representatives (β := ℝ) μ e he0
      (centeredKernelOf_LIP05103 μ W) (continuous_kernel_LIP05103 (μ := μ) hWc).measurable
  exact ⟨f, hmem, hon, fun R => finite_diagonal_general_LIP05107 μ _ hKd f
    (fun j _ => hmem j) (fun i j _ _ => hon i j) R⟩

end DGPS.Frontier.LIP051
