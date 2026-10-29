import DGPS.Frontier.EX012.T21
import DGPS.Frontier.EX012.T22
import DGPS.Frontier.EX012.T23

/-!
# EX012.03: Remove the Euler constant

Task id: EX012.03 (node EX012, one-site complementary range equation, assembly).
Title: Remove the Euler constant.

Forward: for an admissible `u` (smooth, one-periodic, positive, `∫₀¹ u² = 1`) that minimizes
`E_h(u²)` among admissible densities (Task 02), the mean-zero logarithm
`v = 2 log u - ∫₀¹ 2 log u` (Task 01 with `r = u²`) is smooth, one-periodic, mean-zero, and
satisfies the Euler residual `R(v, h²) = D²v + v + ½((Dv)² - ∫₀¹(Dv)²) + (h²/4) cos(2π·2·x) = 0`.

Converse: every smooth mean-zero `v` with `R(v, h²) = 0` gives the normalized positive
`u = exp(v/2) / √(∫₀¹ exp v)`, which satisfies the Euler equation
`-4 D²u + h² sin²(2πx) u - 4 u log u = λ u` for some real `λ`. This is stationarity only.

## Provides

* `DGPS.Frontier.EX012.ex012_03_remove_euler_constant`: main statement (for every `h : ℝ`), the
  conjunction of the forward direction and the converse direction, with `τ = h²`.
* `DGPS.Frontier.EX012.ex012_03_remove_euler_constant_forward`: the forward direction, from an
  admissible minimizer `u` of `E_h(u²)`, to the residual identity `R(v, h²) = 0` for
  `v = centeredLog2_EX01221 u`.
* `DGPS.Frontier.EX012.ex012_03_remove_euler_constant_converse`: the converse direction, from a
  smooth mean-zero `v` with `R(v, h²) = 0`, to a smooth positive normalized `u` solving the Euler
  equation for some real `λ`.
* Helpers (suffix `_EX01203`): `centeredLog2_contDiff_EX01203` (smoothness of `v`),
  `centeredLog2_periodic_EX01203` (one-periodicity of `v`), `centeredLog2_mean_EX01203` (`∫₀¹ v = 0`),
  and `residual_eq_eulerR_EX01203` (the residual of EX012.23 agrees with that of EX012.22; they
  differ only in the spelling `cos (2 · (2π x))` versus `cos (2π · 2 · x)`).

## R5 notes

* Forward hypotheses: `IsAdmSmooth_EX01236 u` and minimality
  `groundE_EX01236 h u ≤ groundE_EX01236 h w` for every admissible `w`. Task 02 says "minimizing the
  displayed ground functional" without naming the competitor class. It is read here as minimality
  among admissible densities, the class used by EX012.20 and EX012.21. Minimality over all
  `AbsoluteDensity 1` (the `ex010_ground` variant) would be a stronger hypothesis, so it is not
  assumed. The hypothesis is the one of EX012.21's main statement, so the forward theorem is
  exactly the composition of EX012.21, EX012.22 and the smoothness, periodicity and mean-zero facts.
* `groundE_EX01236 h u` is the displayed expression `E_h(u²)` (EX012.36). It is not identified with
  `ex010_ground`; that link is EX012.36's `ground_smoothDensity_EX01236`, which this file does not
  need.
* Task 01 is read as the centered logarithm `v = log r - ∫ log r` with `r = u²`, which equals
  `2 log u - ∫ 2 log u = centeredLog2_EX01221 u`. Its smoothness, one-periodicity and mean-zero
  property are proved, not assumed.
* Stationary point versus minimizer. The forward direction uses minimality only through EX012.21,
  which uses EX012.20(ii) to turn it into the pointwise Euler identity. The Euler equation of Task 02
  is a stationarity equation. The converse gives only that `u` solves the Euler equation for some
  `λ`. It does not state, and the proof does not use, that `u` minimizes `E_h(u²)`.
* The constant `λ` is existentially quantified in the converse. It is not identified with
  `E_h(u²)`; that optional identification is not part of this statement.
* Converse hypotheses: `v` is smooth (`ContDiff ℝ ∞`), `∫₀¹ v = 0`, and `R(v, h²) = 0` pointwise.
  Periodicity of `v` is not assumed. EX012.23 lists it, but its proof never uses it, so it is
  omitted here, which gives a stronger converse. For the same reason the conclusion does not claim
  `IsAdmSmooth_EX01236 u`; it claims smoothness, positivity and `∫₀¹ u² = 1`.
* `_hmean` in the converse is the spec's mean-zero hypothesis. The proof does not use it, so it
  carries the underscore name, as in EX012.23.
* `τ = h²` is the node preamble's identification. The converse's Euler equation uses `h ^ 2`
  for `τ`, and `h : ℝ` is arbitrary.
* `D = (2π)⁻¹ ∂ₓ` is `angD_EX01217`. `c₂(x) = cos(2π · 2 · x)` as in EX012.22, `s₁(x) = sin(2π x)`.
  `∫₀¹` is the interval integral over the period cell, and the domain is `ℝ`, not a quotient circle.
* The specification's `R(v, τ)` is `eulerR_EX01222`, which is used for the forward conclusion and
  the converse hypothesis. The Euler equation in the converse is written out in the form of the
  EX012.02 displayed equation with `τ = h²`.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- The centered logarithm `v = 2 log u - ∫₀¹ 2 log u` of an admissible density is smooth. -/
theorem centeredLog2_contDiff_EX01203 {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) :
    ContDiff ℝ ∞ (centeredLog2_EX01221 u) := by
  have hlog : ContDiff ℝ ∞ fun x => Real.log (u x) := hu.smooth.log fun x => (hu.pos x).ne'
  unfold centeredLog2_EX01221
  exact (contDiff_const.mul hlog).sub contDiff_const

/-- The centered logarithm of an admissible density is one-periodic. -/
theorem centeredLog2_periodic_EX01203 {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) :
    Function.Periodic (centeredLog2_EX01221 u) 1 := by
  intro x
  unfold centeredLog2_EX01221
  rw [hu.periodic x]

/-- The centered logarithm of an admissible density has zero interval integral over `[0,1]`. -/
theorem centeredLog2_mean_EX01203 {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) :
    ∫ t in (0:ℝ)..1, centeredLog2_EX01221 u t = 0 := by
  have hcont : Continuous fun t => 2 * Real.log (u t) :=
    (hu.smooth.continuous.log fun x => (hu.pos x).ne').const_mul 2
  have hint : IntervalIntegrable (fun t => 2 * Real.log (u t)) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable _ _
  unfold centeredLog2_EX01221
  rw [intervalIntegral.integral_sub hint (continuous_const.intervalIntegrable _ _)]
  simp

/-- The residual of EX012.23 and the residual of EX012.22 coincide pointwise. -/
theorem residual_eq_eulerR_EX01203 {τ : ℝ} {v : ℝ → ℝ} (x : ℝ) :
    residual_EX01223 τ v x = eulerR_EX01222 τ v x := by
  have e : 2 * Real.pi * 2 * x = 2 * (2 * Real.pi * x) := by ring
  unfold residual_EX01223 eulerR_EX01222
  rw [e]

/-- Forward direction of EX012.03: an admissible minimizer `u` of `E_h(u²)` (Task 02) gives the
mean-zero, smooth, one-periodic `v = 2 log u - ∫ 2 log u` (Task 01) with `R(v, h²) = 0`. -/
theorem ex012_03_remove_euler_constant_forward (h : ℝ) {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u)
    (hmin : ∀ w : ℝ → ℝ, IsAdmSmooth_EX01236 w → groundE_EX01236 h u ≤ groundE_EX01236 h w) :
    ContDiff ℝ ∞ (centeredLog2_EX01221 u) ∧ Function.Periodic (centeredLog2_EX01221 u) 1 ∧
      (∫ t in (0:ℝ)..1, centeredLog2_EX01221 u t) = 0 ∧
      ∀ x, eulerR_EX01222 (h ^ 2) (centeredLog2_EX01221 u) x = 0 := by
  have hv := centeredLog2_contDiff_EX01203 hu
  have hp := centeredLog2_periodic_EX01203 hu
  have hm := centeredLog2_mean_EX01203 hu
  obtain ⟨_, _, hex⟩ := ex012_21_logarithmic_derivative_identities h hu hmin
  exact ⟨hv, hp, hm, ex012_22_determine_constant_integration_exists (h ^ 2) hv hp hm hex⟩

/-- Converse direction of EX012.03: a smooth mean-zero `v` with `R(v, h²) = 0` gives the normalized
positive `u = exp(v/2)/√(∫₀¹ exp v)` that solves the Euler equation for some real `λ`.
This is stationarity only; no minimality is asserted. -/
theorem ex012_03_remove_euler_constant_converse (h : ℝ) {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v)
    (_hmean : ∫ t in (0:ℝ)..1, v t = 0) (hR : ∀ x, eulerR_EX01222 (h ^ 2) v x = 0) :
    ContDiff ℝ ∞ (logReverse_EX01223 v) ∧ (∀ x, 0 < logReverse_EX01223 v x) ∧
      (∫ x in (0:ℝ)..1, logReverse_EX01223 v x ^ 2 = 1) ∧
      ∃ lam : ℝ, ∀ x, -4 * angD_EX01217 (angD_EX01217 (logReverse_EX01223 v)) x
        + h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * logReverse_EX01223 v x
        - 4 * logReverse_EX01223 v x * Real.log (logReverse_EX01223 v x)
        = lam * logReverse_EX01223 v x := by
  have hR' : ∀ x, residual_EX01223 (h ^ 2) v x = 0 := fun x =>
    (residual_eq_eulerR_EX01203 x).trans (hR x)
  exact ⟨logReverse_contDiff_EX01223 hv, logReverse_pos_EX01223 hv.continuous,
    logReverse_sq_mass_EX01223 hv.continuous,
    ⟨2 * Real.log (massZ_EX01223 v) - (∫ y in (0:ℝ)..1, angD_EX01217 v y ^ 2) + h ^ 2 / 2,
      ex012_23_reverse_logarithmic_transformation_multiplier hv hR'⟩⟩

/-- Remove the Euler constant (EX012.03). For every `h : ℝ`:
(i) for every admissible `u` minimizing `E_h(u²)` among admissible densities, the mean-zero
logarithm `v = 2 log u - ∫ 2 log u` is smooth, one-periodic, mean-zero, and satisfies
`R(v, h²) = 0`; and (ii) every smooth mean-zero `v` with `R(v, h²) = 0` yields a smooth positive
normalized `u = exp(v/2)/√(∫ exp v)` that solves the Euler equation for some real `λ`. -/
theorem ex012_03_remove_euler_constant (h : ℝ) :
    (∀ {u : ℝ → ℝ}, IsAdmSmooth_EX01236 u →
      (∀ w : ℝ → ℝ, IsAdmSmooth_EX01236 w → groundE_EX01236 h u ≤ groundE_EX01236 h w) →
      ContDiff ℝ ∞ (centeredLog2_EX01221 u) ∧ Function.Periodic (centeredLog2_EX01221 u) 1 ∧
        (∫ t in (0:ℝ)..1, centeredLog2_EX01221 u t) = 0 ∧
        ∀ x, eulerR_EX01222 (h ^ 2) (centeredLog2_EX01221 u) x = 0) ∧
    (∀ {v : ℝ → ℝ}, ContDiff ℝ ∞ v → (∫ t in (0:ℝ)..1, v t) = 0 →
      (∀ x, eulerR_EX01222 (h ^ 2) v x = 0) →
      ContDiff ℝ ∞ (logReverse_EX01223 v) ∧ (∀ x, 0 < logReverse_EX01223 v x) ∧
        (∫ x in (0:ℝ)..1, logReverse_EX01223 v x ^ 2 = 1) ∧
        ∃ lam : ℝ, ∀ x, -4 * angD_EX01217 (angD_EX01217 (logReverse_EX01223 v)) x
          + h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * logReverse_EX01223 v x
          - 4 * logReverse_EX01223 v x * Real.log (logReverse_EX01223 v x)
          = lam * logReverse_EX01223 v x) :=
  ⟨fun hu hmin => ex012_03_remove_euler_constant_forward h hu hmin,
    fun hv hm hR => ex012_03_remove_euler_constant_converse h hv hm hR⟩

end DGPS.Frontier.EX012
