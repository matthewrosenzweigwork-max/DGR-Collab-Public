import DGPS.Frontier.STR029.T36

/-!
# STR029.05: Poincaré bound sufficient for attainment

Task id: STR029.05. Title: Poincaré bound sufficient for attainment (node STR029, size S).

Provides:
* `DGPS.Frontier.STR029.str029_05_poincare_bound_sufficient_attainment`: for every real `h` with `|h| ≤ 1/1000` and
  every periodic `H¹` function `f` with weak derivative `g` (`IsPeriodicWeakDerivative_STR02933 f g`),
  `∫ g² q_h dm ≥ (1 - h²) Var_{q_h m}(f)`, where `Var_{q_h m}(f) = varQ_STR02935 h (f - ∫ f dm)`.

R5 notes:
* Hypotheses. The only hypothesis is `|h| ≤ 1/1000`, as in the specification. No hypothesis on `f` is added. The
  function `f` ranges over periodic `H¹` functions in the sense of STR029.33 (`IsPeriodicWeakDerivative_STR02933`:
  periodic `L²` with a periodic `L²` weak derivative against smooth periodic tests). The case `h = 0` is included.
* Reading of `∫ f'² q_h dm`. The derivative `f'` is the weak derivative of `f`, carried by the second argument `g`
  of the predicate. The statement quantifies over all pairs `(f, g)` with `IsPeriodicWeakDerivative_STR02933 f g`.
  Existence of a weak derivative for a periodic `H¹` function is not proved here, and it is not needed for the
  inequality. The a.e.-uniqueness of `g` is not used.
* Derivative variable. The derivative is taken in the angular variable `t = 2πx`, not in the physical variable `x`.
  This is the reading under which the constant is `1 - h²`, the Wirtinger constant on the angular circle. In the
  physical variable the same inequality would have the factor `a0 = 4π²` on the right-hand side. That form is not
  the specified statement and is not proved here.
* Measure. `dm = dt/(2π)` on `(0, 2π]`, realized by `normInt_STR02933` as `(2π)⁻¹` times the Lebesgue integral.
  The specification writes `[0, 2π)`; the endpoint is a null set.
* Weight. `q_h = qT_STR02904 h = e^{h cos 3t} / ∫ e^{h cos 3s} dm`, the reference density of STR029.04. It is
  normalized (`normInt_qT_STR02935` in STR029.35), so `Var_{q_h m}` is the variance under the probability `q_h m`.
* Variance. `Var_{q_h m}(f)` is written as `varQ_STR02935 h (f - ∫ f dm)`, with the Haar mean subtracted first as
  in the specification. `varQ_STR02935 h F` is the second moment minus the squared first moment under `q_h m`.
* Integrability. The Bochner convention gives value `0` to non-integrable integrands. Every integrand in this
  statement is integrable, because `f` and `g` are `L²` and `q_h` is bounded. That is established in STR029.35
  and STR029.36 and is not restated here.
* Not used by this unit. The common optimizer-chart predicate, the `AbsoluteDensity` domain, the entropy, Fisher and
  deficit conventions, the angular-to-physical rate normalization and the Euler range map. This unit uses only the
  weighted carrier `q_h m` and the periodic `H¹` class.
* Proof route. The main statement is the second conjunct of `str029_36_numerical_absorption_cross_form_estimate`,
  which applies the first-harmonic estimate of STR029.35 together with the numerical facts of STR029.36. The
  substance is therefore proved in those prerequisite modules. This module re-exports that conjunct under the
  STR029.05 name, with the statement written in the carriers of the specification.
-/

namespace DGPS.Frontier.STR029

/-- STR029.05: for `|h| ≤ 1/1000` and every periodic `H¹` function `f` with weak derivative `g`,
`∫ g² q_h dm ≥ (1 - h²) Var_{q_h m}(f)`. -/
theorem str029_05_poincare_bound_sufficient_attainment :
    ∀ h : ℝ, |h| ≤ 1 / 1000 → ∀ f g : ℝ → ℝ, IsPeriodicWeakDerivative_STR02933 f g →
      normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t)
        ≥ (1 - h ^ 2) * varQ_STR02935 h (fun t => f t - normInt_STR02933 f) :=
  fun h hh f g hfg =>
    (str029_36_numerical_absorption_cross_form_estimate).2 h hh f g hfg

end DGPS.Frontier.STR029
