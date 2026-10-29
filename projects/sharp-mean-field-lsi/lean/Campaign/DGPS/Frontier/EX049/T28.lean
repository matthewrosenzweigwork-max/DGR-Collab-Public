import DGPS.Frontier.EX049.T26
import DGPS.Frontier.EX049.T27
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact

/-!
# EX049.28: The weak hypothesis determines all test integrals

Task id and title: EX049.28, "The weak hypothesis determines all test integrals" (node EX049,
shared infrastructure). Hypotheses of EX049.01: `0 < L`, `f` integrable on `(0, L)`, and
`∫_0^L f φ' = 0` for every smooth test `φ` compactly supported in `(0, L)`. Uses the normalized
bump of EX049.26 and the primitive of a mean-zero test of EX049.27.

## Provides
* `DGPS.Frontier.EX049.ex049_28_weak_hypothesis_determines_test_integrals` : the main statement.
  For every smooth `β` supported in `[a, b]` with `0 < a < b < L` and `∫ β = 1`, every smooth
  `ψ` compactly supported in `(0, L)` satisfies
  `∫_0^L f ψ = (∫_0^L f β) * ∫_0^L ψ`.
* `DGPS.Frontier.EX049.ex049_28_weak_hypothesis_determines_test_integrals_bump` : the same
  conclusion for some `β` supported in `[L/4, 3L/4]` with `∫ β = 1`, namely the bump supplied by
  EX049.26 (`ex049_26_smooth_step_normalized_test_bump_bump`), together with the existence of that
  `β` as a conjunct.

## R5 notes
* Smoothness is read as `C^∞`, written `ContDiff ℝ ∞` (the `∞` of `ℕ∞`, not the analytic `ω`).
* `f ∈ L^1(0,L)` is read as `IntegrableOn f (Set.Ioo 0 L)` (Lebesgue measure). The integrals
  `∫_0^L` are oriented interval integrals `∫ x in (0:ℝ)..L, ·`; since `0 < L` they equal the
  integrals over `Ioc 0 L`, and `f` is interval integrable (`intervalIntegrable_iff_integrableOn_Ioo_of_le`).
* The test class of the weak hypothesis is read as in EX049.27: `HasCompactSupport φ` together
  with `tsupport φ ⊆ Set.Ioo 0 L`. The derivative `φ'` is `deriv φ`. The same reading is used for
  the conclusion's test functions `ψ`.
* `β` is taken as a parameter with the properties of the EX049.26 bump that the proof uses:
  `ContDiff ℝ ∞ β`, `Function.support β ⊆ Set.Icc a b`, `0 < a`, `a < b`, `b < L`, and
  `∫ β = 1`. The normalization is essential, since the identity has the coefficient `∫ f β`.
  The EX049.26 bump is also nonnegative, but that is not used and is not assumed.
  The hypothesis `a < b` is part of the EX049.26 setting but is not needed by the argument; it
  is kept under the name `_hab` so that the statement is the specification's, without an
  unused-variable warning.
* The main statement is therefore stronger than the specification's literal "choose β from
  EX049.26": it holds for every such `β`. The corollary instantiates it with the EX049.26 bump
  and `a = L/4`, `b = 3L/4`, which discharges the "choose β from .26" reading.
* "Products are integrable" is proved, not assumed: `f` times a continuous function is
  interval integrable on `[0, L]` (`IntervalIntegrable.mul_continuousOn`).
* The compact support of `η = ψ - (∫ψ) β` is shown through the compact set
  `tsupport ψ ∪ Set.Icc a b`, which lies in `Set.Ioo 0 L`. Its primitive is supplied by
  `ex049_27_primitive_mean_zero_test` (EX049.27). Its derivative is `η` pointwise, so the
  weak hypothesis applies to it via `deriv` after `HasDerivAt.deriv`.
* No hypothesis beyond the specification's (and the .26 normalization above) is assumed. Every
  Mathlib declaration used was checked by grep at the pinned commit (the interval integral API,
  `setIntegral_eq_integral_of_forall_compl_eq_zero`, `IsCompact.of_isClosed_subset`,
  `isClosed_tsupport`, `closure_minimal`, `image_eq_zero_of_notMem_tsupport`).
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- EX049.28: the weak identity against `f` determines every test integral. The function `β` is
any smooth bump supported in `[a, b]` with `0 < a < b < L` and `∫ β = 1` (the EX049.26 normalization). -/
theorem ex049_28_weak_hypothesis_determines_test_integrals (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioo 0 L))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Set.Ioo 0 L →
      ∫ x in (0:ℝ)..L, f x * deriv φ x = 0)
    (β : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (_hab : a < b) (hbL : b < L)
    (hβ : ContDiff ℝ ∞ β) (hβsupp : Function.support β ⊆ Set.Icc a b)
    (hβint : ∫ x, β x = 1) :
    ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 L →
      ∫ x in (0:ℝ)..L, f x * ψ x = (∫ x in (0:ℝ)..L, f x * β x) * ∫ x in (0:ℝ)..L, ψ x := by
  intro ψ hψ hψc hψsub
  have hfi : IntervalIntegrable f MeasureTheory.volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mpr hf
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ x in (0:ℝ)..L, ψ x := ⟨_, rfl⟩
  have hKc : IsCompact (tsupport ψ ∪ Set.Icc a b) := hψc.isCompact.union isCompact_Icc
  have hKsub : tsupport ψ ∪ Set.Icc a b ⊆ Set.Ioo 0 L := by
    apply Set.union_subset hψsub
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ → ℝ, η = fun x => ψ x - I * β x := ⟨_, rfl⟩
  have hηs : ContDiff ℝ ∞ η := by
    rw [hη_def]
    exact hψ.sub (contDiff_const.mul hβ)
  have hsupp_η : Function.support η ⊆ tsupport ψ ∪ Set.Icc a b := by
    intro x hx
    by_contra hn
    have hψ0 : ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn (Set.mem_union_left _ h))
    have hβ0 : β x = 0 := by
      by_contra h
      exact hn (Set.mem_union_right _ (hβsupp (Function.mem_support.mpr h)))
    apply Function.mem_support.mp hx
    rw [hη_def]
    simp [hψ0, hβ0]
  have hηc : HasCompactSupport η :=
    IsCompact.of_isClosed_subset hKc (isClosed_tsupport η)
      (closure_minimal hsupp_η hKc.isClosed)
  have htsub : tsupport η ⊆ Set.Ioo 0 L :=
    fun x hx => hKsub (closure_minimal hsupp_η hKc.isClosed hx)
  have hβL : ∫ x in (0:ℝ)..L, β x = 1 := by
    have hzero : ∀ x, x ∉ Set.Ioc 0 L → β x = 0 := by
      intro x hx
      by_contra h
      have hxs := Set.mem_Icc.mp (hβsupp (Function.mem_support.mpr h))
      exact hx (Set.mem_Ioc.mpr ⟨by linarith [hxs.1], by linarith [hxs.2]⟩)
    rw [intervalIntegral.integral_of_le hL.le,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hβint]
  have hmean : ∫ s in (0:ℝ)..L, η s = 0 := by
    have hint1 : IntervalIntegrable ψ MeasureTheory.volume 0 L :=
      hψ.continuous.intervalIntegrable 0 L
    have hint2 : IntervalIntegrable (fun s => I * β s) MeasureTheory.volume 0 L :=
      (continuous_const.mul hβ.continuous).intervalIntegrable 0 L
    have hsplit : ∫ s in (0:ℝ)..L, η s
        = (∫ s in (0:ℝ)..L, ψ s) - I * ∫ s in (0:ℝ)..L, β s := by
      simp only [hη_def]
      rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul]
    rw [hsplit, hβL, ← hI]
    ring
  obtain ⟨hΦs, ⟨hΦc, hΦsub⟩, hd⟩ :=
    ex049_27_primitive_mean_zero_test L η hηs hηc htsub hmean
  have hcongr : ∫ x in (0:ℝ)..L, f x * η x
      = ∫ x in (0:ℝ)..L, f x * deriv (fun x => ∫ s in (0:ℝ)..x, η s) x := by
    apply intervalIntegral.integral_congr
    intro x _
    show f x * η x = f x * deriv (fun x => ∫ s in (0:ℝ)..x, η s) x
    rw [(hd x).deriv]
  have h0 := hweak (fun x => ∫ s in (0:ℝ)..x, η s) hΦs hΦc hΦsub
  have hfη : ∫ x in (0:ℝ)..L, f x * η x = 0 := hcongr.trans h0
  have hfψ : IntervalIntegrable (fun x => f x * ψ x) MeasureTheory.volume 0 L :=
    hfi.mul_continuousOn hψ.continuous.continuousOn
  have hfβ : IntervalIntegrable (fun x => f x * β x) MeasureTheory.volume 0 L :=
    hfi.mul_continuousOn hβ.continuous.continuousOn
  have hsplit2 : ∫ x in (0:ℝ)..L, f x * η x
      = (∫ x in (0:ℝ)..L, f x * ψ x) - I * ∫ x in (0:ℝ)..L, f x * β x := by
    have heq : (fun x => f x * η x) = fun x => f x * ψ x - I * (f x * β x) := by
      funext x
      simp only [hη_def]
      ring
    rw [heq, intervalIntegral.integral_sub hfψ (hfβ.const_mul I),
      intervalIntegral.integral_const_mul]
  rw [hsplit2] at hfη
  rw [← hI]
  linear_combination hfη

/-- EX049.28 with the EX049.26 bump: for `0 < L`, `f` and the weak hypothesis of EX049.01, there is
a smooth `β` supported in `[L/4, 3L/4]` with `∫ β = 1` such that every smooth test `ψ` compactly
supported in `(0, L)` satisfies `∫_0^L f ψ = (∫_0^L f β) ∫_0^L ψ`. -/
theorem ex049_28_weak_hypothesis_determines_test_integrals_bump (L : ℝ) (hL : 0 < L)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo 0 L))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Set.Ioo 0 L →
      ∫ x in (0:ℝ)..L, f x * deriv φ x = 0) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ Function.support β ⊆ Set.Icc (L / 4) (3 * L / 4) ∧
      ∫ x, β x = 1 ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 L →
        ∫ x in (0:ℝ)..L, f x * ψ x = (∫ x in (0:ℝ)..L, f x * β x) * ∫ x in (0:ℝ)..L, ψ x := by
  obtain ⟨β, hβ, -, hsupp, hint⟩ :=
    ex049_26_smooth_step_normalized_test_bump_bump (L / 4) (3 * L / 4) L
      (by linarith) (by linarith) (by linarith)
  exact ⟨β, hβ, hsupp, hint,
    ex049_28_weak_hypothesis_determines_test_integrals L hL f hf hweak β (L / 4) (3 * L / 4)
      (by linarith) (by linarith) (by linarith) hβ hsupp hint⟩

end DGPS.Frontier.EX049
