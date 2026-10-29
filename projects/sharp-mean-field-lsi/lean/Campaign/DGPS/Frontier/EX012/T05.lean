import DGPS.Frontier.EX012.T29
import DGPS.Frontier.EX012.T30

/-!
# EX012.05: Polynomial map and derivative

Task id: EX012.05 (node EX012, one-site complementary range equation).
Title: Polynomial map and derivative.

Provides:
* `DGPS.Frontier.EX012.ex012_05_polynomial_map_derivative`: the main statement. For
  `α` with `[HolderExponent α]`, the map `F(p, w) = L w + Q [ (1/2) (D f_p + D w)^2 + (τ/4) c₂ ]`
  (`p = (a, b, τ)`, `f_p = a c₁ + b s₁`), written as `rangeMap_EX01229 α : (ℝ × ℝ × ℝ) × W → Y`
  with `W = PH.orthSub α 2` and `Y = PH.orthSub α 0`, satisfies
  (i) `F` is real analytic on all of its domain (`AnalyticOnNhd ℝ F Set.univ`);
  (ii) `F 0 = 0`, i.e. `F (0, 0) = 0`;
  (iii) the derivative in the unknown variable at the origin is the continuous linear map `L`,
  in the form `fderiv ℝ F 0 ∘L inr = L`;
  (iv) the derivative of the section `w ↦ F ((0, 0, 0), w)` at `0` is `L`;
  (v) for all real `a b τ` and all `w : W`,
  `F ((a, b, τ), w) = Q₀ (R (a c₁ + b s₁ + w, τ))`, with `Q₀ = proj_EX01226 α 0`.
  Here `L = ellEquiv` (FOU018), and `R = residual_EX01230 α` is the frozen residual.
  The proof is the assembly of EX012.29 (parts i to iv) and EX012.30 (part v).

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No further
  hypothesis is added, and no statement of the specification is weakened.
* The assembly adds no mathematics: every conjunct is the corresponding conjunct of
  `ex012_29_polynomial_regularity_partial_derivative` (EX012.29) or
  `ex012_30_equality_projected_residual` (EX012.30), both proved in their own files.
* "Real analytic" is read as `AnalyticOnNhd ℝ F Set.univ` (analytic at every point of the
  domain). The index `ω` form `ContDiff ℝ ω F` is not repeated here; it is available as
  `ex012_29_polynomial_regularity_partial_derivative_contDiff`.
* The specification's "power series is its displayed polynomial, with no terms of degree greater
  than two" is a proof route, not a statement; it is not formalized. Analyticity is obtained
  instead from the decomposition `F = linear part + quadratic part` of EX012.29, where the
  quadratic part is the diagonal of a continuous bilinear map composed with a continuous linear
  map.
* "`ℝ³ × W`" is read as `(ℝ × ℝ × ℝ) × PH.orthSub α 2` with the product norm, with `p = (a, b, τ)`
  as the first factor, as in EX012.29.
* "`F(0, 0) = 0`" is read as `F 0 = 0` in the product space, where `0 = ((0, 0, 0), 0)`.
* "The derivative in `w` at `(0, 0)` is `L`" is stated in two forms: the IFT-compatible form
  `fderiv ℝ F 0 ∘L inr = L` (the partial derivative in the unknown variable, as required by
  `ContDiffAt.implicitFunction`) and the derivative of the section `w ↦ F ((0,0,0), w)`. Both are
  the same identity; `L` is the underlying continuous linear map of `ellEquiv`.
* The identity `F(p, w) = Q R(f_p + w, τ)` is read with `f_p = harmInj_EX01228 α 2 (a, b)`
  (`= a c₁ + b s₁`), `w` included into `PH α 2` through the subtype coercion, and `R` the frozen
  residual `residual_EX01230` of EX012.30, in which the Haar integral is `∫ x in 0..1` and the
  constant `∫(Dv)^2` is the element `(∫ …) • 1` of `PH α 0`. The residual's `v''` is `D²v`, since
  the specification's prime is `D = (2π)^{-1} ∂` (EX012.24 and EX012.25).
* `c₂ = cosMode_EX01228 α 0 2`, `D = angDeriv_EX01224`, the square is the diagonal of
  `ex012_27_bounded_multiplication`, and `Q₀ = proj_EX01226 α 0`; these are the definitions of
  EX012.24 to EX012.28 and are not restated here.
* The statement is not a definition: no new function is introduced, so the displayed `F` is the
  literal `rangeMap_EX01229 α` of EX012.29.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

variable (α : ℝ) [HolderExponent α]

/-- **EX012.05.**  The map `F(p, w) = L w + Q [ (1/2) (D f_p + D w)^2 + (τ/4) c₂ ]` from
`ℝ³ × W` to `Y` is real analytic, `F (0, 0) = 0`, its derivative in the unknown variable at
`(0, 0)` is `L`, and `F(p, w) = Q R(f_p + w, τ)` for all `p = (a, b, τ)` and `w ∈ W`. -/
theorem ex012_05_polynomial_map_derivative :
    AnalyticOnNhd ℝ (rangeMap_EX01229 α) Set.univ ∧
    rangeMap_EX01229 α 0 = 0 ∧
    fderiv ℝ (rangeMap_EX01229 α) 0 ∘L
        ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (PH.orthSub α 2) =
      ((ellEquiv (α := α)) : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0) ∧
    fderiv ℝ (fun w : PH.orthSub α 2 =>
        rangeMap_EX01229 α (((0 : ℝ), (0 : ℝ), (0 : ℝ)), w)) 0 =
      ((ellEquiv (α := α)) : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0) ∧
    ∀ (a b τ : ℝ) (w : PH.orthSub α 2),
      rangeMap_EX01229 α ((a, b, τ), w) =
        proj_EX01226 α 0
          (residual_EX01230 α (harmInj_EX01228 α 2 (a, b) + (w : PH α 2)) τ) := by
  obtain ⟨h1, h2, h3, h4⟩ := ex012_29_polynomial_regularity_partial_derivative α
  exact ⟨h1, h2, h3, h4, fun a b τ w => ex012_30_equality_projected_residual α a b τ w⟩

end DGPS.Frontier.EX012
