import DGPS.Frontier.LIP051.T03
import DGPS.Frontier.LIP051.T25
import DGPS.Frontier.LIP051.T29

/-!
# LIP051.33: Symmetry and the constant row

Task id `LIP051.33`, title "Symmetry and the constant row" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1). Proved inputs:
`LIP051.03` (`DGPS.Frontier.LIP051.T03`), `LIP051.25` (`DGPS.Frontier.LIP051.T25`) and
`LIP051.29` (`DGPS.Frontier.LIP051.T29`).

For the centered kernel `K` of `LIP051.03` and representatives `f j` of the basis classes `e j`,
the coefficients `T i j = ∬ K(x,y) f i(x) f j(y) dμ(x) dμ(y)` satisfy `T i j = T j i`, `T 0 j = 0`
and `T i 0 = 0`.

## Provides

* `DGPS.Frontier.LIP051.lip051_33_symmetry_constant_row`: for a bounded continuous symmetric `W`
  on the torus, a probability measure `μ`, a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, and
  every family `f` of measurable representatives of the classes `e j`: the symmetry
  `T i j = T j i` for all `i j : ℕ`, the zero row `T 0 j = 0` for all `j`, and the zero column
  `T i 0 = 0` for all `i`, where `T` is the integral of `K p.1 p.2 * f i p.1 * f j p.2` over
  `μ ⊗ μ`.
* `DGPS.Frontier.LIP051.swap_coeff_LIP05133`: helper; for a symmetric kernel `K` on a probability
  space, exchanging the two basis factors in the product integral exchanges their roles.
* `DGPS.Frontier.LIP051.zero_row_integral_LIP05133`: helper; for a kernel centered in its first
  variable, the product integral of `K(x,y) g(y)` vanishes whenever it is integrable.

## R5 notes

1. Kernel. `K` is `centeredKernelOf_LIP05103 μ W`, under exactly the hypotheses of `LIP051.03`:
   `Continuous (Function.uncurry W)`, symmetry of `W`, `0 ≤ M` and `|W| ≤ M`. No `Spec`, `KData`,
   `Hw` or Gaussian object occurs. The identification of `S.mu` and `D.K` with `μ` and `K` belongs
   to `LIP051.01` and is not used here.
2. Basis. `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)` with `he0 : e 0 = Lp.const 2 μ 1`, as in `LIP051.25`
   and `LIP051.29`. The normalization `e 0 = 1` is listed as data in the specification, which
   replaces `e 0` by `1` almost everywhere; it is a hypothesis here, not a consequence.
3. Representatives. The specification writes `T i j` with the basis `e`, while the Lean integral
   needs functions. The theorem therefore quantifies over every family `f` of measurable functions
   with `f j =ᵐ[μ] e j`. The conclusion holds for every such choice, so it does not depend on a
   selected representative; the existence of such a family is the content of `LIP051.25`.
4. Coefficient. `T i j` is the Bochner integral `∫ p, K p.1 p.2 * f i p.1 * f j p.2 ∂(μ ⊗ μ)`,
   that is the real inner product `⟨K, e_i ⊗ e_j⟩` written as the iterated kernel integral with
   the product order `K(x,y) e_i(x) e_j(y)`. It is the integral itself, not an `L²` inner product.
5. Integrability. The specification says that the coefficient integrands are absolutely integrable
   by `LIP051.29` applied to `F = K`. The statement does not include integrability as a conjunct.
   Symmetry needs none, because exchanging the variables of a Bochner integral over `μ ⊗ μ` holds
   unconditionally. For the zero row, integrability of `K(x,y) e_0(x) e_j(y)` is taken from
   `pairing_core_LIP05129` of `LIP051.29`, with `u = f 0`, `v = f j` and `∫ u² = 1` derived from
   `f 0 =ᵐ[μ] 1`.
6. Zero row. `T 0 j = 0` uses that `f 0 = 1` almost everywhere (the product-measure a.e. statement
   is obtained from the first-coordinate projection), the Fubini swap of `integral_prod_symm`, and
   that `K` is centered in its first variable (`LIP051.03`). The zero column is the symmetry applied
   to the zero row, not a separate computation.
7. Positive-mode indexing (defect FD-002). Indices range over all of `ℕ`, including `0`, exactly as
   the specification states "for all `i, j ∈ ℕ`". The result is a deterministic identity of
   integrals with no Gaussian object, so mode zero does not enter any limit here, and no positive-mode
   restriction is imposed.
8. Lean-exposed specification defects: none found.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- For a symmetric kernel, exchanging the two basis factors does not change the product integral
`∬ K(x,y) a(x) b(y) dμ dμ`: the coefficient of `(a, b)` equals that of `(b, a)`. -/
theorem swap_coeff_LIP05133 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (K : α → α → ℝ) (hK : ∀ x y, K x y = K y x) (a b : α → ℝ) :
    ∫ p, K p.1 p.2 * a p.1 * b p.2 ∂(μ.prod μ) = ∫ p, K p.1 p.2 * b p.1 * a p.2 ∂(μ.prod μ) := by
  rw [← integral_prod_swap (fun p : α × α => K p.1 p.2 * a p.1 * b p.2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hK p.2 p.1]
  ring

/-- For a kernel centered in its first variable, the product integral of `K(x,y) g(y)` vanishes
whenever the integrand is integrable (Fubini, then the inner integral over `x`). -/
theorem zero_row_integral_LIP05133 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (K : α → α → ℝ) (hK : ∀ y, ∫ x, K x y ∂μ = 0) (g : α → ℝ)
    (hint : Integrable (fun p : α × α => K p.1 p.2 * g p.2) (μ.prod μ)) :
    ∫ p, K p.1 p.2 * g p.2 ∂(μ.prod μ) = 0 := by
  rw [integral_prod_symm (fun p : α × α => K p.1 p.2 * g p.2) hint]
  have hin : ∀ y, ∫ x, K x y * g y ∂μ = 0 := fun y => by
    rw [integral_mul_const, hK y, zero_mul]
  simp only [hin, integral_zero]

/-- LIP051.33: for the centered kernel `K` of `LIP051.03` and every family `f` of measurable
representatives of the classes `e j` of a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`,
the coefficients `T i j = ∬ K(x,y) f i(x) f j(y)` satisfy `T i j = T j i`, `T 0 j = 0` and
`T i 0 = 0`. -/
theorem lip051_33_symmetry_constant_row {d : ℕ} {μ : Measure (DGPS.Torus d)}
    [IsProbabilityMeasure μ] {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ)) :
    (∀ i j : ℕ, ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f i p.1 * f j p.2 ∂(μ.prod μ) =
        ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f j p.1 * f i p.2 ∂(μ.prod μ)) ∧
    (∀ j : ℕ, ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f 0 p.1 * f j p.2 ∂(μ.prod μ) = 0) ∧
    (∀ i : ℕ, ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f i p.1 * f 0 p.2 ∂(μ.prod μ) = 0) := by
  obtain ⟨hKm, hKs, -, hKc, -, -, hKL, -⟩ :=
    lip051_03_centering_integrability_original_kernel (μ := μ) hWc hs hM hb
  have he0' : (e 0 : DGPS.Torus d → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) := by
    rw [he0]
    exact Lp.coeFn_const _ _ _
  have hf0 : f 0 =ᵐ[μ] fun _ => (1 : ℝ) := (hfe 0).trans he0'
  have hf0p : (fun p : DGPS.Torus d × DGPS.Torus d => f 0 p.1) =ᵐ[μ.prod μ]
      fun _ => (1 : ℝ) :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp hf0
  have hrow : ∀ j : ℕ,
      ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f 0 p.1 * f j p.2 ∂(μ.prod μ) = 0 := by
    intro j
    have hu1 : ∫ x, f 0 x * f 0 x ∂μ = 1 := by
      have hsq : (fun x => f 0 x * f 0 x) =ᵐ[μ] fun _ => (1 : ℝ) := by
        filter_upwards [hf0] with x hx
        simp [hx]
      rw [integral_congr_ae hsq]
      simp
    have hvL : MemLp (f j) 2 μ := (Lp.memLp (e j)).ae_eq (hfe j).symm
    have h := pairing_core_LIP05129 μ (Function.uncurry (centeredKernelOf_LIP05103 μ W))
      hKm hKL (f 0) (f j) (hfm 0) (hfm j) hu1 hvL
    have hint : Integrable
        (fun p : DGPS.Torus d × DGPS.Torus d =>
          centeredKernelOf_LIP05103 μ W p.1 p.2 * f 0 p.1 * f j p.2) (μ.prod μ) := h.1
    have hGeq : (fun p : DGPS.Torus d × DGPS.Torus d =>
        centeredKernelOf_LIP05103 μ W p.1 p.2 * f 0 p.1 * f j p.2) =ᵐ[μ.prod μ]
        fun p => centeredKernelOf_LIP05103 μ W p.1 p.2 * f j p.2 := by
      filter_upwards [hf0p] with p hp
      rw [hp, mul_one]
    rw [integral_congr_ae hGeq]
    exact zero_row_integral_LIP05133 μ (centeredKernelOf_LIP05103 μ W) hKc (f j)
      (hint.congr hGeq)
  have hsym : ∀ i j : ℕ,
      ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f i p.1 * f j p.2 ∂(μ.prod μ) =
        ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f j p.1 * f i p.2 ∂(μ.prod μ) :=
    fun i j => swap_coeff_LIP05133 μ (centeredKernelOf_LIP05103 μ W) hKs (f i) (f j)
  refine ⟨hsym, hrow, fun i => ?_⟩
  rw [hsym i 0]
  exact hrow i

end DGPS.Frontier.LIP051
