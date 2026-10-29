import Mathlib

/-!
## LIP051.27 — Square-integrable sections

Provides:

* `DGPS.Frontier.LIP051.lip051_27_square_integrable_sections`: for a measurable real `F` on
  `α × α` with `F ∈ L²(μ ⊗ μ)` and a probability measure `μ`, the extended integral
  `a y = ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ` and the set `A = {y | a y < ⊤}` are measurable, `μ A = 1`,
  every section `F (·, y)` with `y ∈ A` is in `L²(μ)`, and the real function `a0`
  (`a` on `A`, zero off `A`) is measurable, integrable, nonnegative, with
  `∫ a0 dμ = ‖F‖²_{L²(μ ⊗ μ)}`.
* `DGPS.Frontier.LIP051.eLpNorm_sq_LIP05127` (helper): `eLpNorm f 2 ν ^ 2 = ∫⁻ ‖f‖ₑ ^ 2 ∂ν`.
* `DGPS.Frontier.LIP051.memLp_section_LIP05127` (helper): a section with finite extended
  integral of `‖·‖ₑ ^ 2` is in `L²`.

R5 notes (interpretive readings and design choices; the frozen statement is the conjunction in
the main theorem, and it is not strengthened or weakened):

1. Generality. The specification speaks of "a probability space". The theorem is stated for an
   arbitrary measurable space `α` with a probability measure `μ` (`[IsProbabilityMeasure μ]`).
   The Torus instantiation (`S.mu` on `Torus d`) is not part of this unit; it is a corollary to
   be obtained by the consumer. No `Spec`, `KData`, `Hw`, basis `e`, Wick object, or kernel `K`
   occurs here. In particular the mode-zero / positive-mode indexing of FD-002 is not touched:
   no index `j` and no mode appears in this unit.
2. Measurability of `F`. "Measurable real function on the product" is read as
   `Measurable F` for the product σ-algebra `MeasurableSpace.prod`, applied to `μ.prod μ`.
   `F` is an everywhere-defined function, not an equivalence class; no representative is chosen
   and no value on any diagonal is altered.
3. The hypothesis `F ∈ L²(μ ⊗ μ)` is `MemLp F 2 (μ.prod μ)`. No further hypothesis is added.
4. The extended integral. `a y` is the Lebesgue integral in `ℝ≥0∞` of `‖F (x, y)‖ₑ ^ 2`, so
   that `a` is `∫⁻ |F(x,y)|² dμ(x) ∈ [0, ∞]` exactly as in the specification. The Bochner
   integral is not used for `a`, so no section is silently assigned the value zero by Lean's
   default for non-integrable functions.
5. The set `A` is `{y | a y < ⊤}`, i.e. `a y ≠ ∞`.
6. The real function `a0` is literally `A.indicator (fun y => (a y).toReal)`. Since
   `ENNReal.toReal ⊤ = 0`, this agrees pointwise with `fun y => (a y).toReal`; the proof uses this
   identity, but the statement keeps the indicator form of the specification.
7. Right-hand side. `‖F‖_{L²(μ⊗μ)}²` is written `(eLpNorm F 2 (μ.prod μ)).toReal ^ 2`, the
   squared L² seminorm as a real number (`eLpNorm` with exponent `2 : ℝ≥0∞`). It is not written
   as `∫ F² ∂(μ ⊗ μ)`, although the two agree; the helper `eLpNorm_sq_LIP05127` links them.
8. Sections. The conclusion "every section is in L²(μ)" is `MemLp (fun x => F (x, y)) 2 μ` for
   `y ∈ A`. At this Mathlib pin `MemLp f p μ` is by definition `eLpNorm f p μ < ∞`, with no
   separate measurability clause. The sections are measurable because `F` is, so the conclusion
   is the genuine L² membership.
9. `μ A = 1` is stated as `μ A = 1` (not as `μ Aᶜ = 0` or an almost-everywhere statement).
   The spec's "A has full measure" is read as this equality, which is available because `μ` is a
   probability measure.
10. Measurability of `A` is stated as `MeasurableSet A`, separately from `Measurable a`, to match
    the specification's "a and A are measurable".
11. Integrability of `a0` is `Integrable a0 μ` (with respect to `μ`, not `μ ⊗ μ`).
12. No almost-everywhere variant or representative is used for the conclusions about `a`, `A`,
    or `a0`: each conclusion is an everywhere statement, except `μ A = 1`, which is the full-measure
    statement of the specification.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

/-- For any real function `f` that is a.e. strongly measurable, the square of its L² seminorm
is the extended integral of `‖f‖ₑ ^ 2`. -/
lemma eLpNorm_sq_LIP05127 {β : Type*} [MeasurableSpace β] {ν : Measure β} {f : β → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- A section `F (·, y)` whose extended integral of `‖·‖ₑ ^ 2` is finite lies in `L²(μ)`. -/
lemma memLp_section_LIP05127 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α × α → ℝ) (hF : Measurable F) (y : α)
    (hy : ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ < ⊤) :
    MemLp (fun x => F (x, y)) 2 μ := by
  have hm : Measurable (fun x => F (x, y)) := hF.comp measurable_prodMk_right
  have hsq := eLpNorm_sq_LIP05127 (ν := μ) (f := fun x => F (x, y)) hm.aestronglyMeasurable
  have h2 : eLpNorm (fun x => F (x, y)) 2 μ ^ 2 ≠ ⊤ := by
    rw [hsq]; exact hy.ne
  exact lt_top_iff_ne_top.2 (fun h => h2 (by simp [h]))

/-- Square-integrable sections (LIP051.27). For a measurable real `F` on `α × α` with
`F ∈ L²(μ ⊗ μ)` and a probability measure `μ`: `a y = ∫⁻ x, |F (x, y)|² dμ(x)` and
`A = {y | a y < ∞}` are measurable, `μ A = 1`, every section `F (·, y)` with `y ∈ A` is in
`L²(μ)`, and the real function `a0` (equal to `a` on `A` and zero off `A`) is measurable,
integrable, nonnegative, with `∫ a0 dμ = ‖F‖²_{L²(μ ⊗ μ)}`. See the module docstring, R5 notes. -/
theorem lip051_27_square_integrable_sections {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α × α → ℝ) (hF : Measurable F) (hL2 : MemLp F 2 (μ.prod μ)) :
    let a : α → ENNReal := fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ 2 ∂μ
    let A : Set α := {y | a y < ⊤}
    Measurable a ∧ MeasurableSet A ∧ μ A = 1 ∧
      (∀ y ∈ A, MemLp (fun x => F (x, y)) 2 μ) ∧
      (let a0 : α → ℝ := A.indicator (fun y => (a y).toReal);
        Measurable a0 ∧ Integrable a0 μ ∧ (∀ y, 0 ≤ a0 y) ∧
          ∫ y, a0 y ∂μ = (eLpNorm F 2 (μ.prod μ)).toReal ^ 2) := by
  intro a A
  have hg : Measurable (fun p : α × α => ‖F p‖ₑ ^ 2) := (hF.enorm).pow_const 2
  have ha : Measurable a := hg.lintegral_prod_left'
  have hAm : MeasurableSet A := measurableSet_lt ha measurable_const
  have hI : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod μ) ≠ ⊤ := by
    rw [← eLpNorm_sq_LIP05127 hL2.aestronglyMeasurable]
    exact ENNReal.pow_ne_top hL2.eLpNorm_lt_top.ne
  have hton : ∫⁻ y, a y ∂μ = ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(μ.prod μ) :=
    (lintegral_prod_symm' (fun p : α × α => ‖F p‖ₑ ^ 2) hg).symm
  have hna : ∫⁻ y, a y ∂μ ≠ ⊤ := by rw [hton]; exact hI
  have hae : ∀ᵐ y ∂μ, a y < ⊤ := ae_lt_top ha hna
  have hA1 : μ A = 1 := (prob_compl_eq_zero_iff hAm).1 (ae_iff.1 hae)
  have ha0 : A.indicator (fun y => (a y).toReal) = fun y => (a y).toReal := by
    funext y
    by_cases hy : y ∈ A
    · simp [Set.indicator_of_mem hy]
    · have h1 : ¬ (a y < ⊤) := hy
      have hy' : a y = ⊤ := by simpa using h1
      simp [Set.indicator_of_notMem hy, hy']
  refine ⟨ha, hAm, hA1, fun y hy => memLp_section_LIP05127 μ F hF y hy, ?_⟩
  rw [ha0]
  refine ⟨ha.ennreal_toReal, integrable_toReal_of_lintegral_ne_top ha.aemeasurable hna,
    fun y => ENNReal.toReal_nonneg, ?_⟩
  rw [integral_toReal ha.aemeasurable hae, hton, ← ENNReal.toReal_pow,
    eLpNorm_sq_LIP05127 hL2.aestronglyMeasurable]

end DGPS.Frontier.LIP051
