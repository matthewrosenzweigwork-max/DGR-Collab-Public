import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import DGPS.Frontier.EX049.T34

/-!
# EX049.36: Integration by parts with explicit endpoint values

Task id: EX049.36 (node EX049, shared infrastructure, prerequisite EX049.34).

For absolutely continuous `u`, `v` on the interval with endpoints `a`, `b`,
`∫_a^b (u' v + u v') = u(b) v(b) - u(a) v(a)`. The square-weighted form
`∫_a^b a₁ (v²)' = [a₁ v²]_a^b - ∫_a^b a₁' v²` follows for a `C¹` function `a₁`, and the boundary
term vanishes when the endpoint products (or the endpoint values of the two factors) agree.

## Provides

- `DGPS.Frontier.EX049.ex049_36_integration_parts_explicit_endpoint_values`: for absolutely
  continuous `u`, `v` on `[a, b]`, `∫_a^b (u' v + u v') = u(b) v(b) - u(a) v(a)` (the main
  identity; the orientation of `[a, b]` is that of the oriented integral `∫ x in a..b`).
- `DGPS.Frontier.EX049.ex049_36_integration_parts_explicit_endpoint_values_square_weight`: for a
  `C¹` function `a₁` and an absolutely continuous `v` on `[a, b]`, the integrand `a₁ (v²)'` is
  interval integrable and `∫_a^b a₁ (v²)' = a₁(b) v(b)² - a₁(a) v(a)² - ∫_a^b a₁' v²`.
- `DGPS.Frontier.EX049.ex049_36_integration_parts_explicit_endpoint_values_periodic_product`: if
  `u(b) v(b) = u(a) v(a)` (matching endpoint products) then `∫_a^b (u' v + u v') = 0`.
- `DGPS.Frontier.EX049.ex049_36_integration_parts_explicit_endpoint_values_periodic_factors`: if
  `u(a) = u(b)` and `v(a) = v(b)` (matching endpoint traces of the factors) then
  `∫_a^b (u' v + u v') = 0`.

## R5 notes

- Absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval f a b` (epsilon-delta condition
  on `uIcc a b`). No hypothesis `a ≤ b` is added: the oriented integral `∫ x in a..b` and the
  endpoint values make the identities valid for both orientations.
- `deriv` is Mathlib's total derivative. For absolutely continuous functions it is the a.e.
  derivative, and it is interval integrable on `a..b` (Mathlib's
  `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`). The product terms `u' v` and `u v'`
  are therefore integrable without an extra hypothesis.
- Non-literal reading 1 (bounded): the specification's hypothesis "bounded AC functions" is not
  assumed separately. An absolutely continuous function on the compact interval `uIcc a b` is
  bounded there (Mathlib's `AbsolutelyContinuousOnInterval.exists_bound`), so the boundedness
  hypothesis is implied. The statements are therefore at least as strong as the specification.
- Non-literal reading 2 (integrability): the specification's hypothesis "integrable product
  derivative terms" is not assumed. It holds automatically for absolutely continuous factors, since
  `deriv` of an absolutely continuous function is interval integrable (see the note above), so it
  is not needed.
- Non-literal reading 3 (H¹ representative): the square-weight lemma takes an absolutely
  continuous `v` on `[a, b]`, not an `H¹` function with `L²` derivative. The `L²` condition on
  `deriv v` is not used: an `H¹` interval representative is absolutely continuous, and the identity
  needs only absolute continuity, so the lemma covers the `H¹` case with no `L²` hypothesis.
- The `C¹` hypothesis on `a₁` is kept global, `ContDiff ℝ 1 a₁`, as written in the specification.
- The square-weight identity is stated with `deriv (fun y => v y ^ 2)` (the derivative of `v²`),
  not with `2 v v'`. The integrability of `a₁ (v²)'` is part of the conclusion, because the
  Bochner integral alone would not record it.
- The periodic assertion is stated in two forms, the endpoint-product form from the proof text
  and the endpoint-factor form from the phrase "matching periodic traces". Neither assumes
  periodicity of the functions on `ℝ`; they are conditions on the endpoint values only.
- The proof of the main identity is Mathlib's
  `AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub`, the AC form of the product rule
  integrated by the fundamental theorem of calculus. The EX049.34 product lemmas are imported but
  not used by this proof.
-/

open MeasureTheory Set

namespace DGPS.Frontier.EX049

theorem ex049_36_integration_parts_explicit_endpoint_values {u v : ℝ → ℝ} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b) :
    ∫ x in a..b, (deriv u x * v x + u x * deriv v x) = u b * v b - u a * v a :=
  hu.integral_deriv_mul_eq_sub hv

theorem ex049_36_integration_parts_explicit_endpoint_values_square_weight
    {v a₁ : ℝ → ℝ} {a b : ℝ}
    (ha₁ : ContDiff ℝ 1 a₁) (hv : AbsolutelyContinuousOnInterval v a b) :
    IntervalIntegrable (fun x => a₁ x * deriv (fun y => v y ^ 2) x) volume a b ∧
    ∫ x in a..b, a₁ x * deriv (fun y => v y ^ 2) x =
      a₁ b * v b ^ 2 - a₁ a * v a ^ 2 - ∫ x in a..b, deriv a₁ x * v x ^ 2 := by
  have ha₁AC : AbsolutelyContinuousOnInterval a₁ a b :=
    (ha₁.contDiffOn.mono (subset_univ _)).absolutelyContinuousOnInterval
  have hsq : AbsolutelyContinuousOnInterval (fun y => v y ^ 2) a b := by
    have e : (fun y => v y ^ 2) = fun y => v y * v y := funext fun y => sq (v y)
    rw [e]
    exact hv.fun_mul hv
  have hFTC : ∫ x in a..b, (deriv a₁ x * v x ^ 2 + a₁ x * deriv (fun y => v y ^ 2) x) =
      a₁ b * v b ^ 2 - a₁ a * v a ^ 2 :=
    ha₁AC.integral_deriv_mul_eq_sub hsq
  have hc : ContinuousOn (fun x => deriv a₁ x * v x ^ 2) (uIcc a b) :=
    ((ContDiff.continuous_deriv_one ha₁).continuousOn).mul (hv.continuousOn.pow 2)
  have hi1 : IntervalIntegrable (fun x => deriv a₁ x * v x ^ 2) volume a b :=
    hc.intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => a₁ x * deriv (fun y => v y ^ 2) x) volume a b :=
    hsq.intervalIntegrable_deriv.continuousOn_mul ha₁AC.continuousOn
  have hsplit := intervalIntegral.integral_add hi1 hi2
  refine ⟨hi2, ?_⟩
  linarith

theorem ex049_36_integration_parts_explicit_endpoint_values_periodic_product
    {u v : ℝ → ℝ} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b)
    (hper : u b * v b = u a * v a) :
    ∫ x in a..b, (deriv u x * v x + u x * deriv v x) = 0 := by
  rw [ex049_36_integration_parts_explicit_endpoint_values hu hv, hper, sub_self]

theorem ex049_36_integration_parts_explicit_endpoint_values_periodic_factors
    {u v : ℝ → ℝ} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b)
    (hu_per : u a = u b) (hv_per : v a = v b) :
    ∫ x in a..b, (deriv u x * v x + u x * deriv v x) = 0 := by
  apply ex049_36_integration_parts_explicit_endpoint_values_periodic_product hu hv
  rw [hu_per, hv_per]

end DGPS.Frontier.EX049
