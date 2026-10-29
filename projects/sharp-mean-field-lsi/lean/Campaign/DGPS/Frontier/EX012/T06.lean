import DGPS.Frontier.EX012.T31
import DGPS.Frontier.EX012.T37

/-!
# EX012.06: Supplied inverse

Task id: EX012.06 (node EX012, one-site complementary range equation).
Title: Supplied inverse.

Provides:
* `DGPS.Frontier.EX012.ex012_06_supplied_inverse`: there is a continuous linear equivalence
  `L : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0` (that is, `W ≃ Y`) with `L u = ell u` for every
  `u ∈ W`, where `ell = D² + 1` is the angular elliptic operator of EX012.37 (`D = (2π)⁻¹ ∂ₓ`),
  and, for all `A₂ B₂ : ℝ`, `L⁻¹ (A₂ c₂ + B₂ s₂) = -(A₂/3) c₂ - (B₂/3) s₂` as an equality in `W`.
* `DGPS.Frontier.EX012.ex012_06_supplied_inverse_of_equiv`: the inverse identity for an arbitrary
  continuous linear equivalence `L : W ≃L[ℝ] Y` with `L u = ell u` on `W`; the inverse does not
  depend on the choice of `L`.

Helpers: none. The proof assembles EX012.31 (`ex012_31_inverse_second_harmonics`,
`ex012_31_inverse_second_harmonics_fou018`), with the elements `A₂ c₂ + B₂ s₂ ∈ Y` and
`-(A₂/3) c₂ - (B₂/3) s₂ ∈ W` given by `yLhs_EX01231` and `wRhs_EX01231`.

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No hypothesis
  is added beyond the specification.
* The equivalence `L` of the first conjunct is the one supplied by FOU018, through
  `complementary_circle_elliptic_inverse` (read in EX012.31). It is stated as an existential
  `∃ L`, as in the specification ("there is a continuous linear equivalence"). The second
  declaration `ex012_06_supplied_inverse_of_equiv` shows that the inverse identity holds for any
  such `L`, so the statement does not depend on which equivalence is chosen.
* "Agreeing with `D²+1`" is read as `L u = ell u` for `u ∈ W`, where `ell` is the operator
  `ComplementaryElliptic.ell` with `ell f = (2π)⁻² f'' + f` (EX012.37, `_angular`, which gives
  `D (D f) + f` with `D = (2π)⁻¹ ∂ₓ`). The specification's `f''` is read as the second derivative in
  the unit-period variable `x`; the factor `(2π)⁻²` converts it to the angular variable.
* The specification's `u = A₂ c₂ + B₂ s₂` is an element of `Y = PH.orthSub α 0` (the target of `L`),
  and `L⁻¹ u` is `L.symm` applied to it; the displayed proposed inverse is an element of `W`.
  The conclusion is an equality of elements of the subtype `W = PH.orthSub α 2`, i.e. of underlying
  functions, not an identity of Fourier coefficients.
* `c₂ = cosMode_EX01228 α k 2`, `s₂ = sinMode_EX01228 α k 2` with `k = 0` for the element of `Y`
  and `k = 2` for the element of `W`; their membership in the orthogonal subspaces is proved in
  EX012.31 from the coefficient integrals of EX012.28, not assumed.
* The identity `L c₂ = -3 c₂`, `L s₂ = -3 s₂` (from `D² c₂ = -4 c₂`) and the conclusion via
  injectivity of `L` (`ContinuousLinearEquiv.symm_apply_eq`) are those of EX012.31. No Fourier
  uniqueness theorem is used, as the specification requires.
* The specification's frozen statement mentions the inverse only through the displayed formula.
  No other part of the range equation (the projection `Q`, the Euler equation `R`) is used here.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

/-- **EX012.06 (supplied inverse).**  There is a continuous linear equivalence `L : W ≃ Y`, with
`W = PH.orthSub α 2` and `Y = PH.orthSub α 0`, agreeing with `D² + 1` (`L u = ell u`), and for
all `A₂ B₂` the inverse of `A₂ c₂ + B₂ s₂` is `-(A₂/3) c₂ - (B₂/3) s₂`. -/
theorem ex012_06_supplied_inverse {α : ℝ} [HolderExponent α] :
    ∃ L : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0,
      (∀ u : PH.orthSub α 2, (L u : PH α 0) = ell (u : PH α 2)) ∧
      ∀ A B : ℝ, L.symm (yLhs_EX01231 α A B) = wRhs_EX01231 α A B :=
  ex012_31_inverse_second_harmonics_fou018

/-- The inverse identity for an arbitrary continuous linear equivalence `L : W ≃ Y` agreeing with
`ell` on `W`: `L⁻¹ (A₂ c₂ + B₂ s₂) = -(A₂/3) c₂ - (B₂/3) s₂` for all `A₂ B₂`. -/
theorem ex012_06_supplied_inverse_of_equiv {α : ℝ} [HolderExponent α]
    (L : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0)
    (hL : ∀ u : PH.orthSub α 2, (L u : PH α 0) = ell (u : PH α 2)) (A B : ℝ) :
    L.symm (yLhs_EX01231 α A B) = wRhs_EX01231 α A B :=
  ex012_31_inverse_second_harmonics L hL A B

end DGPS.Frontier.EX012
