import DGPS.Frontier.EX012.T20

/-!
# EX012.02: Constrained Euler equation

Task id: EX012.02 (node EX012, one-site complementary range equation, assembly unit).
Title: Constrained Euler equation.

Let `h : ℝ`, `τ = h ^ 2`, `D = (2π)⁻¹ ∂ₓ`, `s₁(x) = sin (2π x)`. For a positive smooth one-periodic
`u` of unit `L²` mass on `[0,1]` (`IsAdmSmooth_EX01236 u`) that minimizes the displayed ground
functional `E_h(u²)` among such densities, `λ = E_h(u²)` and
`-4 D² u + τ s₁² u - 4 u log u = λ u` holds at every point.

## Provides

* `DGPS.Frontier.EX012.ex012_02_constrained_euler_equation`: for `h : ℝ` and admissible `u` with
  `groundE_EX01236 h u ≤ groundE_EX01236 h v` for every admissible `v`, the pointwise identity
  `-4 * angD_EX01217 (angD_EX01217 u) x + h ^ 2 * sin (2π x) ^ 2 * u x - 4 * u x * log (u x)
  = groundE_EX01236 h u * u x` for all `x`.
* `DGPS.Frontier.EX012.ex012_02_constrained_euler_equation_ground`: the same conclusion with the
  minimality hypothesis stated for the named functional `ex010_ground h` over all `AbsoluteDensity 1`
  (a stronger hypothesis, hence a weaker theorem).
* `DGPS.Frontier.EX012.ex012_02_constrained_euler_equation_lambda`: under the same hypotheses as the
  main theorem, the formula `λ = ∫₀¹ G u` with `G = -4 D² u + τ s₁² u - 4 u log u`.

No helper declarations are introduced; all component arguments (EX012.16–EX012.19) are consumed
through the proved theorem `ex012_20_stationarity_implies_pointwise_euler_identity` of EX012.20.

## R5 notes

* Hypotheses: `h : ℝ` and the admissibility bundle `IsAdmSmooth_EX01236 u` (`C^∞`, one-periodic,
  strictly positive, `∫₀¹ u² = 1`), which is exactly "smooth periodic `u > 0` of squared integral
  one". The only other hypothesis is the minimality `hmin`. No hypothesis is added.
* Minimality is read as: `u²` minimizes `E_h` among all admissible smooth densities
  (`IsAdmSmooth_EX01236 v`). This is the class in which EX012.16 produces competitors. The `_ground`
  variant instead minimizes the named functional `ex010_ground h` over all `AbsoluteDensity 1`; this
  is the stronger hypothesis and is converted by `ground_smoothDensity_EX01236` (EX012.36).
* The displayed functional `E_h(u²) = groundE_EX01236 h u` is the expression that the EX012.36 gate
  identifies with `ex010_ground h (smoothDensity_EX01236 u _)`. This identification is a definition
  check, with scalar `1`; no constant is altered.
* `τ = h²` is written as `h ^ 2`, and `λ = E_h(u²)` as `groundE_EX01236 h u`, in the conclusion; no
  separate variables are introduced.
* `D` is `angD_EX01217 = (2π)⁻¹ • deriv`, applied twice in `D² u = angD (angD u)`. The angular
  scaling is kept on both occurrences of `D`.
* The conclusion is a pointwise equality on all of `ℝ` (not an a.e. statement). It is the
  statement of `euler_T_EX01220 h u x = groundE_EX01236 h u * u x` from EX012.20, unfolded.
* The `_lambda` formula is the integration-by-parts identity of the specification's proof, obtained
  here from the pointwise identity and `∫₀¹ u² = 1`; it is not part of the frozen statement.
* Read literally throughout: the statement is over `[0,1]` interval integrals, and the identity is
  for every real `x` by one-periodicity of both sides.
-/

namespace DGPS.Frontier.EX012

/-- Constrained Euler equation: the pointwise Euler identity for a minimizing admissible `u`. -/
theorem ex012_02_constrained_euler_equation (h : ℝ) {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u)
    (hmin : ∀ v : ℝ → ℝ, IsAdmSmooth_EX01236 v → groundE_EX01236 h u ≤ groundE_EX01236 h v) :
    ∀ x : ℝ, -4 * angD_EX01217 (angD_EX01217 u) x + h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * u x
      - 4 * u x * Real.log (u x) = groundE_EX01236 h u * u x :=
  (ex012_20_stationarity_implies_pointwise_euler_identity h hu).2 hmin

/-- Constrained Euler equation with minimality for the named functional `ex010_ground h`. -/
theorem ex012_02_constrained_euler_equation_ground (h : ℝ) {u : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u)
    (hmin : ∀ σ : AbsoluteDensity 1,
      DGPS.Circle.VonMisesSmallField.ex010_ground h (smoothDensity_EX01236 u hu)
        ≤ DGPS.Circle.VonMisesSmallField.ex010_ground h σ) :
    ∀ x : ℝ, -4 * angD_EX01217 (angD_EX01217 u) x + h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * u x
      - 4 * u x * Real.log (u x) = groundE_EX01236 h u * u x :=
  ex012_20_stationarity_implies_pointwise_euler_identity_ground h hu hmin

/-- The formula `λ = ∫₀¹ G u` for the constrained Euler equation, with `G` the left side. -/
theorem ex012_02_constrained_euler_equation_lambda (h : ℝ) {u : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u)
    (hmin : ∀ v : ℝ → ℝ, IsAdmSmooth_EX01236 v → groundE_EX01236 h u ≤ groundE_EX01236 h v) :
    groundE_EX01236 h u = ∫ x in (0:ℝ)..1,
      (-4 * angD_EX01217 (angD_EX01217 u) x + h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * u x
        - 4 * u x * Real.log (u x)) * u x := by
  have hpt := ex012_02_constrained_euler_equation h hu hmin
  have hcongr : ∫ x in (0:ℝ)..1,
      (-4 * angD_EX01217 (angD_EX01217 u) x + h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * u x
        - 4 * u x * Real.log (u x)) * u x
      = ∫ x in (0:ℝ)..1, groundE_EX01236 h u * u x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [hpt x]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, hu.mass, mul_one]

end DGPS.Frontier.EX012
