import DGPS.Frontier.LIP051.T29

/-!
## LIP051.04 — L2 section projections

Task id `LIP051.04`, title "L2 section projections" (node LIP051, "Joint Gaussian and quadratic
fluctuation limit", category leaf formalization, verification V1). Proved inputs: `LIP051.27`
(`DGPS.Frontier.LIP051.T27`), `LIP051.28` (`DGPS.Frontier.LIP051.T28`) and `LIP051.29`
(`DGPS.Frontier.LIP051.T29`).

## Provides

* `DGPS.Frontier.LIP051.lip051_04_l2_section_projections`: for a probability measure `μ`, a
  measurable real `F` on `α × α` with `F ∈ L²(μ ⊗ μ)`, and a real `L²(μ)` function `e_i` of
  norm one, (i) for almost every `y` the section `F (·, y)` is in `L²(μ)`; (ii) the section
  coefficient `g_i y = ∫ F (x, y) * e_i x dμ(x)` on the good set `A` of LIP051.27 (and `0` off `A`)
  is measurable, lies in `L²(μ)`, and satisfies `‖g_i‖₂ ≤ ‖F‖₂`; (iii) for every norm-one
  `e_j ∈ L²(μ)`, `∫ g_i * e_j dμ = ∫ F (x, y) * e_i x * e_j y d(μ ⊗ μ)`.
* `DGPS.Frontier.LIP051.exists_measurable_rep_LIP05104` (helper): an almost-everywhere strongly
  measurable real function has an everywhere measurable representative.
* `DGPS.Frontier.LIP051.integral_mul_self_one_LIP05104` (helper): a norm-one `f ∈ L²(ν)` has
  `∫ f * f dν = 1`.
* `DGPS.Frontier.LIP051.integral_mul_self_congr_LIP05104` (helper): almost-everywhere equal
  functions have the same diagonal moment `∫ f * f dν`.
* `DGPS.Frontier.LIP051.section_coefficient_congr_LIP05104` (helper): the section integral
  `∫ F (x, y) * e x dμ(x)` does not change when `e` is replaced by an a.e.-equal function.
* `DGPS.Frontier.LIP051.prod_pairing_congr_LIP05104` (helper): the product integral
  `∫ F p * e_i p.1 * e_j p.2 d(μ ⊗ μ)` does not change when `e_i`, `e_j` are replaced by
  a.e.-equal functions.

## R5 notes

1. Generality. The theorem is stated for an arbitrary measurable space `α` with a probability
   measure `μ` (`[IsProbabilityMeasure μ]`), as in LIP051.27 to LIP051.29. No `Spec`, `KData`,
   `Hw`, `Torus`, Wick object, basis, or kernel `K` occurs. The transport to the campaign
   declaration belongs to LIP051.01.
2. Mode indexing (defect FD-002). The specification attaches no index to `e_i` and `e_j`: they are
   arbitrary norm-one `L²(μ)` functions. The theorem therefore covers every such function,
   including the constant function `e_0 = 1` (which has norm one because `μ` is a probability
   measure). No positive-mode restriction is imposed, and no Gaussian object occurs. A consumer
   needing positive modes may specialise to positive-mode functions.
3. Measurability of `F`. "Measurable L² function on the product" is read as `Measurable F` for
   the product σ-algebra together with `MemLp F 2 (μ.prod μ)`, the same binders as LIP051.27 and
   LIP051.28. `F` is an everywhere-defined function; no representative is chosen for it.
4. The norm-one function `e_i`. "Norm-one L² function" is read as `MemLp ei 2 μ` together with
   `eLpNorm ei 2 μ = 1`. No measurability of `ei` is assumed, because the specification does not
   state it; an element of `L²` is a class of almost-everywhere strongly measurable functions. The
   proof passes to a measurable representative internally (helper
   `exists_measurable_rep_LIP05104`). The conclusions do not depend on this choice: for each `y`,
   the integrand `x ↦ F (x, y) * e x` changes only on a `μ`-null set when `e` is changed on one,
   and the product integrand changes only on a `μ ⊗ μ`-null set.
5. The exceptional null set and the zero convention. The specification does not name the
   exceptional null set. It is read as the complement of `A = {y | ∫⁻ ‖F (x, y)‖ₑ ^ 2 dμ(x) < ⊤}`,
   the canonical set on which the section has finite `L²` norm (LIP051.27). `A` is measurable and
   `μ A = 1`, so its complement is null. The section coefficient is `g = A.indicator (…)`, zero off
   `A`, as the specification states. The Bochner integral is used on `A` only, where the integrand
   is integrable by Hölder's inequality.
6. Almost every `y`. The first conclusion is stated as `∀ᵐ y ∂μ, MemLp (fun x => F (x, y)) 2 μ`,
   matching the specification's "for almost every y". It is derived from `y ∈ A` and `μ A = 1`.
7. Norm bound. "Has norm at most `‖F‖₂`" is written
   `(eLpNorm g 2 μ).toReal ≤ (eLpNorm F 2 (μ.prod μ)).toReal`, the real-valued `L²` seminorm
   convention of LIP051.27, note 7.
8. The pairing identity. The specification's double integral `∬ F(x,y) e_i(x) e_j(y) dμ(x) dμ(y)`
   is written as the product-measure integral `∫ p, F p * ei p.1 * ej p.2 ∂(μ.prod μ)`. The
   iterated form, with the inner integral in `x`, equals it by Fubini; that companion is
   `lip051_29_pairing_section_coefficient_iterated` and is not restated here. The left-hand side is
   the integral `∫ y, g y * ej y ∂μ` against `μ`.
9. The quantifier over `e_j`. The specification's "for every norm-one L² function `e_j`" is the
   conclusion `∀ ej, MemLp ej 2 μ → eLpNorm ej 2 μ = 1 → …`, with the same reading as `ei` in
   note 4. Integrability of `g * ej` and of the product integrand is not part of the statement;
   the proof establishes it internally through LIP051.29.
10. Lean-exposed specification defects in this unit: none found.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- An almost-everywhere strongly measurable real function has a measurable representative. -/
lemma exists_measurable_rep_LIP05104 {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {f : β → ℝ} (hf : AEStronglyMeasurable f ν) :
    ∃ f' : β → ℝ, Measurable f' ∧ f =ᵐ[ν] f' :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk⟩

/-- A norm-one function `f ∈ L²(ν)` satisfies `∫ f * f dν = 1`. -/
lemma integral_mul_self_one_LIP05104 {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {f : β → ℝ} (hf : MemLp f 2 ν) (h1 : eLpNorm f 2 ν = 1) :
    ∫ x, f x * f x ∂ν = 1 := by
  rw [integral_mul_self_LIP05128 hf, h1]
  simp

/-- Almost-everywhere equal functions have the same diagonal moment `∫ f * f dν`. -/
lemma integral_mul_self_congr_LIP05104 {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {f f' : β → ℝ} (h : f =ᵐ[ν] f') : ∫ x, f x * f x ∂ν = ∫ x, f' x * f' x ∂ν := by
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The section integral `∫ F (x, y) * e x dμ(x)` is unchanged when `e` is replaced by an
almost-everywhere equal function (for each fixed `y`). -/
lemma section_coefficient_congr_LIP05104 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α × α → ℝ) {e e' : α → ℝ} (h : e =ᵐ[μ] e') (y : α) :
    ∫ x, F (x, y) * e x ∂μ = ∫ x, F (x, y) * e' x ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The product integral `∫ F p * e_i p.1 * e_j p.2 d(μ ⊗ μ)` is unchanged when `e_i` and `e_j`
are replaced by almost-everywhere equal functions. -/
lemma prod_pairing_congr_LIP05104 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α × α → ℝ) {ei ei' ej ej' : α → ℝ}
    (hi : ei =ᵐ[μ] ei') (hj : ej =ᵐ[μ] ej') :
    ∫ p, F p * ei p.1 * ej p.2 ∂(μ.prod μ) = ∫ p, F p * ei' p.1 * ej' p.2 ∂(μ.prod μ) := by
  have hi' : ∀ᵐ p ∂(μ.prod μ), ei p.1 = ei' p.1 :=
    (Measure.quasiMeasurePreserving_fst).ae (p := fun x => ei x = ei' x) hi
  have hj' : ∀ᵐ p ∂(μ.prod μ), ej p.2 = ej' p.2 :=
    (Measure.quasiMeasurePreserving_snd).ae (p := fun x => ej x = ej' x) hj
  refine integral_congr_ae ?_
  filter_upwards [hi', hj'] with p hp hq
  rw [hp, hq]

/-- Section projections (LIP051.04). For a probability measure `μ`, a measurable `F` on `α × α`
with `F ∈ L²(μ ⊗ μ)`, and a norm-one `e_i ∈ L²(μ)`: for almost every `y` the section `F (·, y)` is
in `L²(μ)`; the section coefficient `g y = ∫ F (x, y) * e_i x dμ(x)` on the good set `A` of
LIP051.27, `0` off `A`, is measurable, in `L²(μ)`, with `‖g‖₂ ≤ ‖F‖₂`; and for every norm-one
`e_j ∈ L²(μ)`, `∫ g * e_j dμ = ∬ F (x, y) e_i(x) e_j(y) d(μ ⊗ μ)`. See the module docstring,
R5 notes. -/
theorem lip051_04_l2_section_projections {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α × α → ℝ) (hF : Measurable F) (hL2 : MemLp F 2 (μ.prod μ))
    (ei : α → ℝ) (hei : MemLp ei 2 μ) (hei1 : eLpNorm ei 2 μ = 1) :
    let a : α → ENNReal := fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ
    let A : Set α := {y | a y < ⊤}
    let g : α → ℝ := A.indicator (fun y => ∫ x, F (x, y) * ei x ∂μ)
    (∀ᵐ y ∂μ, MemLp (fun x => F (x, y)) 2 μ) ∧
      Measurable g ∧ MemLp g 2 μ ∧
      (eLpNorm g 2 μ).toReal ≤ (eLpNorm F 2 (μ.prod μ)).toReal ∧
      ∀ ej : α → ℝ, MemLp ej 2 μ → eLpNorm ej 2 μ = 1 →
        ∫ y, g y * ej y ∂μ = ∫ p, F p * ei p.1 * ej p.2 ∂(μ.prod μ) := by
  intro a A g
  obtain ⟨-, hAm, hA1, hsec, -⟩ := lip051_27_square_integrable_sections μ F hF hL2
  obtain ⟨ei', hei'm, hei_ae⟩ := exists_measurable_rep_LIP05104 hei.aestronglyMeasurable
  have hei'1 : ∫ x, ei' x * ei' x ∂μ = 1 := by
    rw [← integral_mul_self_congr_LIP05104 hei_ae]
    exact integral_mul_self_one_LIP05104 hei hei1
  have hgeq : g = A.indicator (fun y => ∫ x, F (x, y) * ei' x ∂μ) := by
    have hfun : (fun y => ∫ x, F (x, y) * ei x ∂μ) = (fun y => ∫ x, F (x, y) * ei' x ∂μ) :=
      funext fun y => section_coefficient_congr_LIP05104 μ F hei_ae y
    show A.indicator (fun y => ∫ x, F (x, y) * ei x ∂μ) = _
    rw [hfun]
  obtain ⟨hgm, hgL, -, hnorm⟩ :=
    lip051_28_section_coefficient_contraction μ F hF hL2 ei' hei'm hei'1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hae : ∀ᵐ y ∂μ, y ∈ A := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hAm).2 hA1
    exact hae.mono fun y hy => hsec y hy
  · rw [hgeq]
    exact hgm
  · rw [hgeq]
    exact hgL
  · rw [hgeq]
    exact hnorm
  · intro ej hej hej1
    obtain ⟨ej', hej'm, hej_ae⟩ := exists_measurable_rep_LIP05104 hej.aestronglyMeasurable
    have hej'1 : ∫ x, ej' x * ej' x ∂μ = 1 := by
      rw [← integral_mul_self_congr_LIP05104 hej_ae]
      exact integral_mul_self_one_LIP05104 hej hej1
    have hej'L : MemLp ej' 2 μ := MemLp.ae_eq hej_ae hej
    have hpair := pairing_core_LIP05129 μ F hF hL2 ei' ej' hei'm hej'm hei'1 hej'L
    have hcoef : ∫ y, g y * ej y ∂μ = ∫ y, g y * ej' y ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hej_ae] with y hy
      rw [hy]
    calc ∫ y, g y * ej y ∂μ = ∫ y, g y * ej' y ∂μ := hcoef
      _ = ∫ p, F p * ei' p.1 * ej' p.2 ∂(μ.prod μ) := by
          rw [hgeq]
          exact hpair.2.2.1
      _ = ∫ p, F p * ei p.1 * ej p.2 ∂(μ.prod μ) :=
          (prod_pairing_congr_LIP05104 μ F hei_ae hej_ae).symm

end DGPS.Frontier.LIP051
