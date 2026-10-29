import DGPS.Frontier.LIP051.T28
import DGPS.Frontier.LIP051.T30

/-!
# LIP051.29: Pairing the section coefficient

Task id `LIP051.29`, title "Pairing the section coefficient" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1). Source:
`frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.29` statement and proof. Proved
inputs: `LIP051.28` (`DGPS.Frontier.LIP051.T28`) and `LIP051.30` (`DGPS.Frontier.LIP051.T30`).

## Provides

* `DGPS.Frontier.LIP051.lip051_29_pairing_section_coefficient`: for a probability measure `μ`
  and a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, there are measurable representatives
  `f j` of the classes `e j` (the representatives of `LIP051.25` and `LIP051.30`) such that, for
  every measurable `F` on `α × α` with `F ∈ L²(μ ⊗ μ)` and all indices `i j`, the function
  `F (x, y) * f i x * f j y` is integrable on `μ.prod μ`, the function `g y * f j y` is
  integrable on `μ`, where `g` is the section coefficient `g y = ∫ F (x, y) * f i x dμ(x)` on
  `A = {y | ∫⁻ ‖F (x, y)‖ₑ ^ 2 dμ(x) < ⊤}` and `0` off `A` (as in `LIP051.28`), and
  `∫ g y * f j y dμ(y) = ∫ F p * f i p.1 * f j p.2 d(μ ⊗ μ)`.
* `DGPS.Frontier.LIP051.lip051_29_pairing_section_coefficient_iterated`: the same conclusion
  with the right-hand side written as the iterated integral
  `∫ y, ∫ x, F (x, y) * f i x * f j y ∂μ ∂μ` (inner integral in `x`, as `dμ(x) dμ(y)`).
* `DGPS.Frontier.LIP051.pairing_core_LIP05129`: helper; the abstract pairing for measurable
  `f_i, f_j ∈ L²(μ)` with `∫ f_i * f_i dμ = 1`, with no Hilbert basis.

## R5 notes

1. Generality. `μ` is an arbitrary probability measure on an arbitrary measurable space `α`, as
   in `LIP051.25`, `.27`, `.28`, `.30`. No `Spec`, `KData`, `Hw`, `Torus`, Wick object or kernel
   `K` occurs; the transport to the campaign declaration belongs to `LIP051.01`.
2. Mode indexing (defect FD-002). A mode index occurs here: `i` and `j` range over all of `ℕ`,
   including `0`, exactly as the specification's "for every basis index `j`" and "one of the
   norm-one functions in `.25`" state. This is the reading adopted: no positive-mode restriction
   is imposed and none is silently chosen. The statement is true at index `0` as well, since it
   is a deterministic identity of integrals using only `L²` membership and the diagonal moment
   `∫ f i * f i dμ = 1`. No Gaussian object occurs, so the failure of mode zero for the centered
   Gaussian limit does not affect this unit; a consumer needing positive modes may specialise to
   `1 ≤ i`, `1 ≤ j`.
3. Quantifier structure. The representatives `f` of `LIP051.25` are obtained inside the
   theorem and are independent of `F`, `i`, `j`; they are existentially quantified before `F`,
   as in `LIP051.30` (whose conclusion data they are). The hypotheses are those of the Hilbert
   basis (`e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)`, `e 0 = Lp.const 2 μ 1`) as in `LIP051.25`/`.30`,
   and those of `LIP051.27`/`.28` for `F` (`Measurable F`, `MemLp F 2 (μ.prod μ)`). The
   conclusions hold for any representatives satisfying the clauses exported by `.25`; this is
   made explicit by the helper `pairing_core_LIP05129`.
4. The section coefficient `g` is literally the one of `LIP051.28`: with
   `a y = ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ`, `A = {y | a y < ⊤}` and
   `g = A.indicator (fun y => ∫ x, F (x, y) * f i x ∂μ)`, with `F (x, y) * f i x` in that order.
5. Integrals. The product integrand is `F p * f i p.1 * f j p.2` (left-associated, matching
   `F(x,y) e_i(x) e_j(y)`), integrated against `μ.prod μ`; the integrability clause is
   `Integrable _ (μ.prod μ)`. The "double integral" of the specification is read as that product
   integral in the main theorem and as the iterated integral (inner in `x`) in the `_iterated`
   companion; the two agree by Fubini because the integrand is integrable.
6. Integrability of the left integrand `g y * f j y` is stated as `Integrable _ μ`, as the
   specification's proof notes it follows from `LIP051.28` (`g ∈ L²`) and `f j ∈ L²`.
7. Proof route. Absolute integrability is obtained from `MemLp.integrable_mul` (Hölder for
   `L² × L²`) applied to `F` and the product `f i ⊗ f j ∈ L²(μ ⊗ μ)` of `LIP051.30`, instead of
   an explicit Cauchy–Schwarz computation; the bound `‖F‖₂` is not restated. Fubini is
   `integral_prod_symm`; the scalar factor is pulled out with `integral_mul_const`; the null
   complement of `A` is handled by `μ A = 1` from `LIP051.27`.
8. Lean-exposed specification defects: none found.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- Abstract pairing: for measurable `u, v ∈ L²(μ)` with `∫ u * u dμ = 1` and a measurable
`F ∈ L²(μ ⊗ μ)`, the product `F p * u p.1 * v p.2` and `g y * v y` are integrable and the
section coefficient `g` of `LIP051.28` (for `u`) pairs with `v` as the product integral. -/
theorem pairing_core_LIP05129 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α × α → ℝ) (hF : Measurable F)
    (hL2 : MemLp F 2 (μ.prod μ)) (u v : α → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∫ x, u x * u x ∂μ = 1) (hvL : MemLp v 2 μ) :
    let a : α → ENNReal := fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ
    let A : Set α := {y | a y < ⊤}
    let g : α → ℝ := A.indicator (fun y => ∫ x, F (x, y) * u x ∂μ)
    Integrable (fun p : α × α => F p * u p.1 * v p.2) (μ.prod μ) ∧
      Integrable (fun y => g y * v y) μ ∧
      ∫ y, g y * v y ∂μ = ∫ p, F p * u p.1 * v p.2 ∂(μ.prod μ) ∧
      ∫ y, g y * v y ∂μ = ∫ y, ∫ x, F (x, y) * u x * v y ∂μ ∂μ := by
  intro a A g
  have huL : MemLp u 2 μ := memLp_of_integral_mul_self_eq_one_LIP05128 hu hu1
  have hP : MemLp (fun p : α × α => u p.1 * v p.2) 2 (μ.prod μ) := by
    have hmeas : Measurable (fun p : α × α => u p.1 * v p.2) :=
      (hu.comp measurable_fst).mul (hv.comp measurable_snd)
    refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr ?_
    have hsq : Integrable (fun p : α × α => u p.1 ^ 2 * v p.2 ^ 2) (μ.prod μ) :=
      Integrable.mul_prod huL.integrable_sq hvL.integrable_sq
    refine hsq.congr (ae_of_all _ fun p => ?_)
    simp only [mul_pow]
  have hint : Integrable (fun p : α × α => F p * u p.1 * v p.2) (μ.prod μ) := by
    have h := hL2.integrable_mul hP
    refine h.congr (ae_of_all _ fun p => ?_)
    simp only [Pi.mul_apply, mul_assoc]
  obtain ⟨-, hAm, hA1, -⟩ := lip051_27_square_integrable_sections μ F hF hL2
  obtain ⟨-, hgL, -, -⟩ := lip051_28_section_coefficient_contraction μ F hF hL2 u hu hu1
  have hgv : Integrable (fun y => g y * v y) μ := hgL.integrable_mul hvL
  have hae : ∀ᵐ y ∂μ, y ∈ A := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff hAm).2 hA1
  have hiter : ∫ y, g y * v y ∂μ = ∫ y, ∫ x, F (x, y) * u x * v y ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [g, Set.indicator_of_mem hy]
    rw [integral_mul_const]
  exact ⟨hint, hgv, hiter.trans (integral_prod_symm _ hint).symm, hiter⟩

/-- Pairing the section coefficient (LIP051.29), with the right-hand side as a product
integral. For the representatives `f` of `LIP051.25`/`LIP051.30`, every measurable
`F ∈ L²(μ ⊗ μ)` and all indices `i j` (including `0`; see the module docstring, R5 note 2): with
`g` the section coefficient of `LIP051.28`, `F (x, y) * f i x * f j y` is integrable on
`μ.prod μ`, `g * f j` is integrable on `μ`, and `∫ g * f j dμ = ∬ F * f i ⊗ f j`. -/
theorem lip051_29_pairing_section_coefficient {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (he0 : e 0 = Lp.const 2 μ (1 : ℝ)) :
    ∃ f : ℕ → α → ℝ, (∀ j, Measurable (f j)) ∧ (∀ j, f j =ᵐ[μ] (e j : α → ℝ)) ∧
      ∀ F : α × α → ℝ, Measurable F → MemLp F 2 (μ.prod μ) → ∀ i j : ℕ,
        let a : α → ENNReal := fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ
        let A : Set α := {y | a y < ⊤}
        let g : α → ℝ := A.indicator (fun y => ∫ x, F (x, y) * f i x ∂μ)
        Integrable (fun p : α × α => F p * f i p.1 * f j p.2) (μ.prod μ) ∧
          Integrable (fun y => g y * f j y) μ ∧
          ∫ y, g y * f j y ∂μ = ∫ p, F p * f i p.1 * f j p.2 ∂(μ.prod μ) := by
  obtain ⟨f, hm, hae, hmem, -, hcov, -⟩ :=
    lip051_25_representative_moments_hilbert_basis μ e he0
  refine ⟨f, hm, hae, fun F hF hL2 i j => ?_⟩
  have h := pairing_core_LIP05129 μ F hF hL2 (f i) (f j) (hm i) (hm j)
    (by simpa using hcov i i) (hmem j)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Iterated-integral form of LIP051.29: the right-hand side is
`∫ y, ∫ x, F (x, y) * f i x * f j y ∂μ ∂μ`, inner integral in `x`. -/
theorem lip051_29_pairing_section_coefficient_iterated {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (he0 : e 0 = Lp.const 2 μ (1 : ℝ)) :
    ∃ f : ℕ → α → ℝ, (∀ j, Measurable (f j)) ∧ (∀ j, f j =ᵐ[μ] (e j : α → ℝ)) ∧
      ∀ F : α × α → ℝ, Measurable F → MemLp F 2 (μ.prod μ) → ∀ i j : ℕ,
        let a : α → ENNReal := fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ
        let A : Set α := {y | a y < ⊤}
        let g : α → ℝ := A.indicator (fun y => ∫ x, F (x, y) * f i x ∂μ)
        Integrable (fun p : α × α => F p * f i p.1 * f j p.2) (μ.prod μ) ∧
          Integrable (fun y => g y * f j y) μ ∧
          ∫ y, g y * f j y ∂μ = ∫ y, ∫ x, F (x, y) * f i x * f j y ∂μ ∂μ := by
  obtain ⟨f, hm, hae, hmem, -, hcov, -⟩ :=
    lip051_25_representative_moments_hilbert_basis μ e he0
  refine ⟨f, hm, hae, fun F hF hL2 i j => ?_⟩
  have h := pairing_core_LIP05129 μ F hF hL2 (f i) (f j) (hm i) (hm j)
    (by simpa using hcov i i) (hmem j)
  exact ⟨h.1, h.2.1, h.2.2.2⟩

end DGPS.Frontier.LIP051
