import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# EX049.27: Primitive of a mean-zero test

Task id and title: EX049.27, "Primitive of a mean-zero test" (node EX049, shared
infrastructure; library input: primitive of a smooth compactly supported function with
zero integral over `[0, L]`). Independent of EX049.26 at the level of declarations.

## Provides
* `DGPS.Frontier.EX049.ex049_27_primitive_mean_zero_test` : the main statement, the conjunction
  of the smoothness, support and derivative conclusions below for `φ x = ∫_0^x η`.
* `DGPS.Frontier.EX049.ex049_27_primitive_mean_zero_test_smooth` : `φ` is `C^∞`.
* `DGPS.Frontier.EX049.ex049_27_primitive_mean_zero_test_compact_support` : `φ` has compact
  support and its closed support lies in the open interval `(0, L)`.
* `DGPS.Frontier.EX049.ex049_27_primitive_mean_zero_test_deriv` : `φ' x = η x` at every real `x`.
* `DGPS.Frontier.EX049.left_plateau_EX04927` : `η` vanishes on some `(-∞, a]` with `a > 0`.
* `DGPS.Frontier.EX049.right_plateau_EX04927` : `η` vanishes on some `[b, ∞)` with `b < L`.
* `DGPS.Frontier.EX049.primitive_zero_left_EX04927` : `φ x = 0` for `x ≤ a` when `η = 0` on `(-∞, a]`,
  `a > 0`.
* `DGPS.Frontier.EX049.primitive_zero_right_EX04927` : `φ x = 0` for `x ≥ b` when `η` is
  continuous, `∫_0^L η = 0`, `η = 0` on `[b, ∞)` and `b < L`.

## R5 notes
* Smoothness is read as `C^∞`, written `ContDiff ℝ ∞` (the `∞` of `ℕ∞`, not the analytic `ω`).
* "Compactly supported in `(0, L)`" is read as `HasCompactSupport f ∧ tsupport f ⊆ Set.Ioo 0 L`,
  for both `η` (hypotheses) and `φ` (conclusion). The closed support is the one required to be
  compact and to lie inside the open interval; `support` alone is not used.
* `∫_0^L η` and `∫_0^x η` are oriented interval integrals `∫ s in (0:ℝ)..·, η s`.
* `L` is an unconstrained real. No `0 < L` is assumed: the hypothesis `tsupport η ⊆ Set.Ioo 0 L`
  is the only constraint on `L`, and the proof derives the needed points from it.
* The specification's auxiliary `0 < a < b < L` containing the support is not a hypothesis. It is
  produced inside the proof from the compact support (`left_plateau_EX04927`,
  `right_plateau_EX04927`), and the conclusion is about `tsupport φ ⊆ [a, b] ⊆ (0, L)`.
* "`φ' = η`" is read as `HasDerivAt φ (η x) x` at every real `x` (two-sided, pointwise), not
  almost everywhere.
* The specification's remark about higher derivatives is not used as a separate step: smoothness
  is obtained from `contDiff_infty_iff_deriv` applied to `φ' = η`, which is smooth.
* No hypothesis beyond the statement's own is assumed. No Mathlib declaration is taken on trust:
  every name used was checked at the pinned commit (`contDiff_infty_iff_deriv`,
  `Continuous.integral_hasStrictDerivAt`, `HasCompactSupport.isCompact`,
  `HasCompactSupport.intro`, `image_eq_zero_of_notMem_tsupport`, `IsCompact.exists_isMinOn`,
  `IsCompact.exists_isMaxOn`, `intervalIntegral.integral_add_adjacent_intervals`,
  `intervalIntegral.integral_congr`, `isMinOn_iff`, `isMaxOn_iff`).
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- A smooth function with support in `(0, L)` vanishes on some left half-line `(-∞, a]`, `a > 0`. -/
lemma left_plateau_EX04927 (L : ℝ) (η : ℝ → ℝ) (hsupp : HasCompactSupport η)
    (hsub : tsupport η ⊆ Set.Ioo 0 L) :
    ∃ a : ℝ, 0 < a ∧ ∀ y, y ≤ a → η y = 0 := by
  rcases (tsupport η).eq_empty_or_nonempty with hK | hK
  · exact ⟨1, one_pos, fun y _ => image_eq_zero_of_notMem_tsupport (by simp [hK])⟩
  · obtain ⟨y0, hy0, hmin⟩ := hsupp.isCompact.exists_isMinOn hK continuous_id.continuousOn
    have hpos : 0 < y0 := (hsub hy0).1
    refine ⟨y0 / 2, by linarith, fun y hy => image_eq_zero_of_notMem_tsupport ?_⟩
    intro hyK
    have h' : y0 ≤ y := isMinOn_iff.mp hmin y hyK
    linarith

/-- A smooth function with support in `(0, L)` vanishes on some right half-line `[b, ∞)`, `b < L`. -/
lemma right_plateau_EX04927 (L : ℝ) (η : ℝ → ℝ) (hsupp : HasCompactSupport η)
    (hsub : tsupport η ⊆ Set.Ioo 0 L) :
    ∃ b : ℝ, b < L ∧ ∀ y, b ≤ y → η y = 0 := by
  rcases (tsupport η).eq_empty_or_nonempty with hK | hK
  · exact ⟨L - 1, by linarith, fun y _ => image_eq_zero_of_notMem_tsupport (by simp [hK])⟩
  · obtain ⟨y1, hy1, hmax⟩ := hsupp.isCompact.exists_isMaxOn hK continuous_id.continuousOn
    have hlt : y1 < L := (hsub hy1).2
    refine ⟨(y1 + L) / 2, by linarith, fun y hy => image_eq_zero_of_notMem_tsupport ?_⟩
    intro hyK
    have h' : y ≤ y1 := isMaxOn_iff.mp hmax y hyK
    linarith

/-- If `η = 0` on `(-∞, a]` with `a > 0`, then `∫_0^x η = 0` for all `x ≤ a`. -/
lemma primitive_zero_left_EX04927 {a : ℝ} (ha : 0 < a) {η : ℝ → ℝ}
    (hz : ∀ y, y ≤ a → η y = 0) {x : ℝ} (hx : x ≤ a) :
    ∫ s in (0:ℝ)..x, η s = 0 := by
  have h : ∫ s in (0:ℝ)..x, η s = ∫ s in (0:ℝ)..x, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.mem_uIcc] at hy
    apply hz
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  rw [h]
  simp

/-- If `η` is continuous, `∫_0^L η = 0`, and `η = 0` on `[b, ∞)` with `b < L`, then
`∫_0^x η = 0` for all `x ≥ b`. -/
lemma primitive_zero_right_EX04927 {L b : ℝ} {η : ℝ → ℝ} (hη : Continuous η)
    (hmean : ∫ s in (0:ℝ)..L, η s = 0) (hbL : b < L) (hz : ∀ y, b ≤ y → η y = 0)
    {x : ℝ} (hx : b ≤ x) :
    ∫ s in (0:ℝ)..x, η s = 0 := by
  have hadj : (∫ s in (0:ℝ)..L, η s) + (∫ s in L..x, η s) = ∫ s in (0:ℝ)..x, η s :=
    intervalIntegral.integral_add_adjacent_intervals
      (hη.intervalIntegrable 0 L) (hη.intervalIntegrable L x)
  have h2 : ∫ s in L..x, η s = 0 := by
    have h : ∫ s in L..x, η s = ∫ s in L..x, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.mem_uIcc] at hy
      apply hz
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    rw [h]
    simp
  rw [← hadj, hmean, h2]
  simp

/-- The primitive `φ x = ∫_0^x η` has derivative `η x` at every real `x`, for continuous `η`. -/
lemma ex049_27_primitive_mean_zero_test_deriv (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) :
    ∀ x, HasDerivAt (fun x => ∫ s in (0:ℝ)..x, η s) (η x) x :=
  fun x => (hη.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma ex049_27_primitive_mean_zero_test_smooth (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (fun x => ∫ s in (0:ℝ)..x, η s) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (ex049_27_primitive_mean_zero_test_deriv η hη x).differentiableAt, ?_⟩
  have hd : deriv (fun x => ∫ s in (0:ℝ)..x, η s) = η :=
    funext fun x => (ex049_27_primitive_mean_zero_test_deriv η hη x).deriv
  rw [hd]
  exact hη

/-- The primitive of a smooth, compactly supported (in `(0, L)`) `η` with `∫_0^L η = 0` is
compactly supported, with closed support inside `(0, L)`. -/
lemma ex049_27_primitive_mean_zero_test_compact_support (L : ℝ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hsupp : HasCompactSupport η) (hsub : tsupport η ⊆ Set.Ioo 0 L)
    (hmean : ∫ s in (0:ℝ)..L, η s = 0) :
    HasCompactSupport (fun x => ∫ s in (0:ℝ)..x, η s) ∧
      tsupport (fun x => ∫ s in (0:ℝ)..x, η s) ⊆ Set.Ioo 0 L := by
  obtain ⟨a, ha, hza⟩ := left_plateau_EX04927 L η hsupp hsub
  obtain ⟨b, hbL, hzb⟩ := right_plateau_EX04927 L η hsupp hsub
  have hzero : ∀ x, x ∉ Set.Icc a b → ∫ s in (0:ℝ)..x, η s = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact primitive_zero_left_EX04927 ha hza hx.le
    · exact primitive_zero_right_EX04927 hη.continuous hmean hbL hzb hx.le
  have hcs : HasCompactSupport (fun x => ∫ s in (0:ℝ)..x, η s) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => hzero x hx)
  have hsubI : Function.support (fun x => ∫ s in (0:ℝ)..x, η s) ⊆ Set.Icc a b := by
    intro x hx
    by_contra hn
    exact Function.mem_support.mp hx (hzero x hn)
  have htsub : tsupport (fun x => ∫ s in (0:ℝ)..x, η s) ⊆ Set.Icc a b :=
    closure_minimal hsubI isClosed_Icc
  exact ⟨hcs, fun z hz => ⟨lt_of_lt_of_le ha (htsub hz).1, lt_of_le_of_lt (htsub hz).2 hbL⟩⟩

/-- Primitive of a mean-zero test: for real smooth `η` with compact support in `(0, L)` and
`∫_0^L η = 0`, the function `φ x = ∫_0^x η` is smooth, compactly supported in `(0, L)`, and
`φ' = η`. -/
theorem ex049_27_primitive_mean_zero_test (L : ℝ) (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η)
    (hsupp : HasCompactSupport η) (hsub : tsupport η ⊆ Set.Ioo 0 L)
    (hmean : ∫ s in (0:ℝ)..L, η s = 0) :
    ContDiff ℝ ∞ (fun x => ∫ s in (0:ℝ)..x, η s) ∧
      (HasCompactSupport (fun x => ∫ s in (0:ℝ)..x, η s) ∧
        tsupport (fun x => ∫ s in (0:ℝ)..x, η s) ⊆ Set.Ioo 0 L) ∧
      ∀ x, HasDerivAt (fun x => ∫ s in (0:ℝ)..x, η s) (η x) x :=
  ⟨ex049_27_primitive_mean_zero_test_smooth η hη,
    ex049_27_primitive_mean_zero_test_compact_support L η hη hsupp hsub hmean,
    ex049_27_primitive_mean_zero_test_deriv η hη⟩

end DGPS.Frontier.EX049
