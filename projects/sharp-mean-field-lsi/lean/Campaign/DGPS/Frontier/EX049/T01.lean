import DGPS.Frontier.EX049.T28
import DGPS.Frontier.EX049.T29
import DGPS.Frontier.EX049.T30

/-!
# EX049.01: Zero weak derivative implies constancy

Task id and title: EX049.01, "Zero weak derivative implies constancy" (node EX049, shared
infrastructure, frontier assembly theorem). For `L > 0` and `f ∈ L¹(0,L)`, if `∫_0^L f φ' = 0`
for every real smooth test function `φ` compactly supported in `(0,L)`, then `f` agrees almost
everywhere on `(0,L)` with a real constant.

## Provides
* `DGPS.Frontier.EX049.ex049_01_zero_weak_derivative_implies_constancy` : the main statement. For
  `L > 0`, `f` integrable on `(0,L)` and satisfying the weak identity against every test function,
  there is `c : ℝ` with `f =ᵐ[volume.restrict (Set.Ioo 0 L)] fun _ => c`.
* `DGPS.Frontier.EX049.interval_integrable_EX04901` : helper; `f` is interval integrable on
  `[a, b]` whenever `f` is integrable on `(0,L)`, `0 < a < b < L`.

## R5 notes
* Smoothness is read as `C^∞`, written `ContDiff ℝ ∞` (the `∞` of `ℕ∞`, not the analytic `ω`).
* `f ∈ L¹(0,L)` is read as `IntegrableOn f (Set.Ioo 0 L)` (Lebesgue measure on the open interval).
  Values of `f` outside `(0,L)` are unconstrained and do not enter the conclusion.
* The test class is read as in EX049.27 and EX049.28: `ContDiff ℝ ∞ φ`, `HasCompactSupport φ` and
  `tsupport φ ⊆ Set.Ioo 0 L`. The derivative `φ'` is `deriv φ`. "Compactly supported in `(0,L)`" is
  therefore read for the closed support, not for the open support alone.
* The weak identity `∫_0^L f φ' = 0` uses the oriented interval integral `∫ x in (0:ℝ)..L`, which
  for `0 < L` is the Lebesgue integral over `(0,L]`. This matches the EX049.28 hypothesis verbatim.
* The conclusion "`f = c` almost everywhere" is read as `f =ᵐ[volume.restrict (Set.Ioo 0 L)]`
  the constant `c`, the same reading as EX049.30. It is a statement on `(0,L)` only.
* The constant is `c = ∫_0^L f β`, with `β` the smooth normalized bump of EX049.26 supported in
  `[L/4, 3L/4]`. The bump is obtained from `ex049_28_weak_hypothesis_determines_test_integrals_bump`
  (the specification's "choose the normalized test function from EX049.26"). The bump's `∫ β = 1` is
  used through EX049.28 and EX049.29; the nonnegativity of `β` is not used.
* The interval-by-interval identity `∫_a^b f = c (b - a)` is taken from the general EX049.29 theorem,
  instantiated at `a₀ = L/4`, `b₀ = 3L/4`, rather than from its `_bump` corollary, so that the constant
  `c` is fixed in advance. The interval `(a,b)` ranges over all `0 < a < b < L`.
* The integrability needed for `∫ (f - c) = ∫ f - c (b - a)` is proved (`interval_integrable_EX04901`
  from `IntegrableOn f (Ioo 0 L)`), not assumed.
* No hypothesis is added beyond the specification's. No positivity, normalization or bound on `f` is
  imposed. No Mathlib declaration is assumed beyond those used by the imported EX049.28–EX049.30.
-/

open MeasureTheory Set
open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- `f` integrable on `(0,L)` is interval integrable on any `[a, b]` with `0 < a < b < L`. -/
lemma interval_integrable_EX04901 {L : ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo 0 L))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbL : b < L) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
    (hf.mono_set fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)

/-- Zero weak derivative implies constancy: an `L¹(0,L)` function whose weak derivative vanishes
(tested against every smooth, compactly supported `φ` in `(0,L)`) is almost everywhere equal to a
real constant on `(0,L)`. -/
theorem ex049_01_zero_weak_derivative_implies_constancy (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioo 0 L))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 L →
      ∫ x in (0:ℝ)..L, f x * deriv φ x = 0) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (Ioo 0 L)] fun _ => c := by
  obtain ⟨β, hβ, hsupp, hint, -⟩ :=
    ex049_28_weak_hypothesis_determines_test_integrals_bump L hL f hf hweak
  have hrec := ex049_29_recover_interior_interval_integral L hL f hf hweak β (L / 4) (3 * L / 4)
    (by linarith) (by linarith) (by linarith) hβ hsupp hint
  refine ⟨∫ x in (0:ℝ)..L, f x * β x, ex049_30_interval_integral_uniqueness L hL f _ hf ?_⟩
  intro a b ha hab hbL
  rw [intervalIntegral.integral_sub (interval_integrable_EX04901 hf ha hab hbL)
    intervalIntegrable_const, hrec a b ha hab hbL, intervalIntegral.integral_const, smul_eq_mul]
  ring

end DGPS.Frontier.EX049
