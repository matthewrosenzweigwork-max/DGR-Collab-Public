import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# EX049.30: Interval-integral uniqueness

Task id and title: EX049.30, "Interval-integral uniqueness" (node EX049, shared infrastructure).
If `f ∈ L¹(0,L)` and `∫_a^b (f - c) = 0` for every `0 < a < b < L`, then `f = c` almost everywhere
on `(0,L)`.

The proof is the explicit primitive argument of the specification. Fix the base point `L/2`
and let `G` be `f - c` extended by zero outside `(0,L)`. The primitive `y ↦ ∫_{L/2}^y G` vanishes
identically on `(0,L)` by the hypothesis. The Lebesgue differentiation theorem for locally
integrable functions gives, for almost every `x`, that this primitive has derivative `G x` at `x`.
Since the primitive is locally zero on `(0,L)`, uniqueness of derivatives gives `G x = 0` for
almost every `x ∈ (0,L)`, that is `f x = c`.

## Provides
* `DGPS.Frontier.EX049.ex049_30_interval_integral_uniqueness` : if `f` is integrable on
  `Set.Ioo 0 L` and `∫ x in a..b, (f x - c) = 0` for all `0 < a < b < L`, then
  `f =ᵐ[volume.restrict (Set.Ioo 0 L)] fun _ => c`.
* `DGPS.Frontier.EX049.integral_base_eq_zero_EX04930` : helper; for `y ∈ (0,L)` the interval
  integral `∫_{L/2}^y (f - c)` vanishes, as a consequence of the hypothesis.

## R5 notes
* `L : ℝ` with `0 < L` is the length of the ambient interval `(0,L)`; the statement is about
  real-valued `f : ℝ → ℝ`. The values of `f` outside `(0,L)` are irrelevant and unconstrained.
* `f ∈ L¹(0,L)` is read as `IntegrableOn f (Set.Ioo 0 L)` (Lebesgue measure, open interval), as
  in EX049.29. No measurability hypothesis is added beyond what `IntegrableOn` contains.
* The conclusion "`f = c` almost everywhere" is read as `f =ᵐ[volume.restrict (Set.Ioo 0 L)]`
  the constant function `c`. This is equivalent to `∀ᵐ x, x ∈ Ioo 0 L → f x = c`; it does not
  assert anything about `f` outside `(0,L)`.
* The hypothesis `∫_a^b (f - c) = 0` is the oriented interval integral `∫ x in a..b, (f x - c)`
  over `0 < a < b < L`. Since `f` is integrable on `(0,L)`, this integral is a genuine Lebesgue
  integral on `[a,b] ⊂ (0,L)`, not the junk value of a non-integrable function. The hypothesis is
  not weakened: it is quantified over all such `a < b`, with no extra restriction.
* The specification's "distributional separation theorem" is not used. The argument is the
  primitive argument: the Mathlib theorem `LocallyIntegrable.ae_hasDerivAt_integral` (Lebesgue
  differentiation for the primitive, checked by grep at the pinned commit) replaces the countable
  exhaustion of `(0,L)` by intervals, because the primitive is globally zero on `(0,L)` and
  the indicator extension `G` is locally integrable on all of `ℝ`.
* No prerequisite theorem is imported: the proof uses only the hypothesis and Mathlib. The brief
  lists EX049.29 as a dependency, but the statement of EX049.30 does not use any EX049.29 result,
  so this file does not import `DGPS.Frontier.EX049.T29`.
* No hypothesis is added, no statement is changed, and no positivity, normalization or
  bound on `f` is imposed.
-/

open MeasureTheory Set Filter Topology

namespace DGPS.Frontier.EX049

/-- For `y ∈ (0,L)`, the primitive `∫_{L/2}^y (f - c)` vanishes, by the hypothesis applied to
the ordered pair of endpoints `{L/2, y}`. -/
lemma integral_base_eq_zero_EX04930 {L : ℝ} {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ a b : ℝ, 0 < a → a < b → b < L → ∫ x in a..b, (f x - c) = 0) {y : ℝ}
    (hy : y ∈ Ioo 0 L) : ∫ t in (L / 2)..y, (f t - c) = 0 := by
  obtain ⟨hy0, hyL⟩ := hy
  rcases lt_trichotomy y (L / 2) with hlt | heq | hgt
  · have h1 := h y (L / 2) hy0 hlt (by linarith)
    rw [intervalIntegral.integral_symm, h1, neg_zero]
  · rw [heq, intervalIntegral.integral_same]
  · exact h (L / 2) y (by linarith) hgt hyL

/-- Interval-integral uniqueness: an `L¹(0,L)` function whose integral over every interval
`[a,b]` with `0 < a < b < L` equals that of the constant `c` agrees with `c` almost everywhere
on `(0,L)`. -/
theorem ex049_30_interval_integral_uniqueness (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ) (c : ℝ)
    (hf : IntegrableOn f (Ioo 0 L))
    (h : ∀ a b : ℝ, 0 < a → a < b → b < L → ∫ x in a..b, (f x - c) = 0) :
    f =ᵐ[volume.restrict (Ioo 0 L)] fun _ => c := by
  have hgI : IntegrableOn (fun x => f x - c) (Ioo 0 L) :=
    hf.sub (integrableOn_const measure_Ioo_lt_top.ne)
  have hGloc : LocallyIntegrable ((Ioo 0 L).indicator (fun x => f x - c)) volume :=
    (hgI.integrable_indicator measurableSet_Ioo).locallyIntegrable
  show ∀ᵐ x ∂(volume.restrict (Ioo 0 L)), f x = c
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hGloc] with x hx hxI
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) ((Ioo 0 L).indicator (fun x => f x - c) x) x := by
    refine (hx (L / 2)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
    have hcongr : ∫ t in (L / 2)..y, (Ioo 0 L).indicator (fun x => f x - c) t
        = ∫ t in (L / 2)..y, (f t - c) := by
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have htI : t ∈ Ioo 0 L := by
        rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact ⟨by linarith [hy.1, hxI.1], by linarith [hy.2, hxI.2]⟩
      exact indicator_of_mem htI _
    rw [hcongr]
    exact (integral_base_eq_zero_EX04930 h hy).symm
  have hG0 : (Ioo 0 L).indicator (fun x => f x - c) x = 0 :=
    hzero.unique (hasDerivAt_const x (0 : ℝ))
  rw [indicator_of_mem hxI] at hG0
  show f x = c
  linarith

end DGPS.Frontier.EX049
