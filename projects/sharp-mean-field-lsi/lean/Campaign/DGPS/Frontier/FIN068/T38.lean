import DGPS.FiniteN.QuarticSaddleGlobalFIN066

/-!
# FIN068.38 — Named potential definition gate

## Bindings

| Source object / notion | Actual declaration (file:line) | Type / binders | Discrepancy with the specification text |
|---|---|---|---|
| `quarticPsi_FIN066` | `DGPS.FiniteN.QuarticSaddleGlobalFIN066.quarticPsi_FIN066`, `DGPS/FiniteN/QuarticSaddleGlobalFIN066.lean:389` | `EuclideanSpace ℝ (Fin 2) → ℝ`; body `(w 0 - 1) ^ 2 / (2 * quarticKappa) + (w 1) ^ 2 / (2 * (quarticKappa * quarticEta)) - Real.log (besselI 0 (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)))` | The body is printed and agrees with the displayed formula. Only the parenthesisation `2 * (κ * η)` versus `2 κ η` differs (equal by `mul_assoc`). The definition is defined on all of the plane, so the identification holds globally, not only near `(-4, 0)`. |
| `b = g(4)` (`quarticB`) | `DGPS.Models.quarticB`, `DGPS/FiniteN/QuarticSaddle.lean:41` | `ℝ`; body `besselRatio 4` | none |
| `κ = 5/b` (`quarticKappa`) | `DGPS.Models.quarticKappa`, `DGPS/FiniteN/QuarticSaddle.lean:44` | `ℝ`; body `5 / quarticB` | none |
| `η = 4/5` (`quarticEta`) | `DGPS.Models.quarticEta`, `DGPS/FiniteN/QuarticSaddle.lean:47` | `ℝ`; body `4 / 5` | none |
| `I_0` | `DGPS.Circle.BesselMoments.besselI`, `DGPS/Circle/BesselMoments.lean:44` | `ℕ → ℝ → ℝ`; `besselI n t = ∫ θ, exp (t * angCos θ) * angMode n θ ∂angHaar` (the Haar probability measure on `AddCircle (2 * π)`) | The specification writes `I_0(t) = ∫ e^{t cos θ} dθ/(2π)`; the campaign object is the Haar average over `AddCircle (2π)` with factor `angMode 0 = 1`. The identification with the interval integral `(2π)⁻¹ ∫_0^{2π}` is proved here. |
| `besselRatio` (`g = I_0'/I_0`) | `DGPS.Circle.BesselMoments.besselRatio`, `DGPS/Circle/BesselMoments.lean:52` | `ℝ → ℝ`; body `besselI 1 t / besselI 0 t` | The campaign definition is `I_1/I_0`, not `I_0'/I_0`; they agree because `I_0' = I_1` (`hasDerivAt_besselI_zero`). The equality `besselRatio t = deriv (besselI 0) t / besselI 0 t` is proved here. |
| coordinates of `EuclideanSpace ℝ (Fin 2)` identified with `(x, y)` | `w 0`, `w 1`; the point `!₂[x, y]` | `EuclideanSpace ℝ (Fin 2)` | none (`!₂[x, y] 0 = x`, `!₂[x, y] 1 = y` by `simp`). |

## Task

FIN068.38, Named potential definition gate: for `(x, y)` near `(-4, 0)`, the actual
`quarticPsi_FIN066` equals `(x-1)^2/(2κ) + y^2/(2κη) - log I_0(√(x²+y²))`, with `η = 4/5`,
`κ = 5/b`, and the coordinates of `EuclideanSpace ℝ (Fin 2)` identified with `(x, y)`.

## Provides

* `DGPS.Frontier.FIN068.gate_fin068_38_named_potential_definition_gate`: for every `x y : ℝ`,
  `quarticPsi_FIN066 !₂[x, y]` equals the displayed formula with `κ = 5 / besselRatio 4`,
  `η = 4 / 5` and `I_0(t) = (2π)⁻¹ ∫_0^{2π} exp (t cos s) ds` (global, hence near `(-4, 0)`).
* `DGPS.Frontier.FIN068.gate_fin068_38_named_potential_definition_gate_apply`: the same
  statement for a point `w` of `EuclideanSpace ℝ (Fin 2)`, with `x = w 0`, `y = w 1`.
* `DGPS.Frontier.FIN068.gate_fin068_38_named_potential_definition_gate_besselI`: the same with
  `I_0` the campaign object `besselI 0`.
* `DGPS.Frontier.FIN068.gate_fin068_38_named_potential_definition_gate_eventually`: the identity
  holds on a neighbourhood of `w₋ = !₂[-4, 0]`.
* `DGPS.Frontier.FIN068.gate_fin068_38_named_potential_definition_gate_constants`:
  `quarticB = besselRatio 4`, `quarticKappa = 5 / quarticB`, `quarticEta = 4 / 5`.
* `DGPS.Frontier.FIN068.gate_fin068_38_named_potential_definition_gate_besselI_zero_integral`:
  `besselI 0 t = (2π)⁻¹ ∫_0^{2π} exp (t cos s) ds = ∫ exp (t cos θ) ∂angHaar`.
* `DGPS.Frontier.FIN068.gate_fin068_38_named_potential_definition_gate_besselRatio`:
  `besselRatio t = deriv (besselI 0) t / besselI 0 t`.

## R5 notes

* No hypothesis is added; the identification is an equality of functions on the whole plane.
  "Near `(-4, 0)`" is read as a weaker, local consequence of the global equality, and is also
  stated (the `_eventually` lemma).
* The definition body of `quarticPsi_FIN066` is printed above (`#print` / source line 389), so
  the gate is closed by unfolding it; no definition is changed.
* `η` and `κ` are the campaign constants `quarticEta`, `quarticKappa`. The displayed constants
  `4/5` and `5 / besselRatio 4` are reached by unfolding `quarticEta`, `quarticKappa`, `quarticB`.
* The specification's `g = I_0'/I_0` is read via the campaign definition `besselRatio = I_1/I_0`;
  the specification's `I_0` via the campaign Haar-average `besselI 0`, and in the main theorem
  also as the literal interval-integral average `(2π)⁻¹ ∫_0^{2π} e^{t cos s} ds` (this is
  `K_0` of the node preamble up to the normalising `1/(2π)` of `dm`).
* `y^2/(2κη)` is written `y^2 / (2 * κ * η)`; the definition has `2 * (κ * η)`; they agree by
  `mul_assoc`.
* Coordinates: `x = w 0`, `y = w 1`; the point with coordinates `(x, y)` is `!₂[x, y]`.
-/

open DGPS.Circle.BesselMoments DGPS.Circle.AngularNormalization
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.Frontier.FIN068

/-- `I_0(t) = (2π)⁻¹ ∫_0^{2π} exp (t cos s) ds`, and also the Haar average of `exp (t cos θ)`. -/
theorem gate_fin068_38_named_potential_definition_gate_besselI_zero_integral (t : ℝ) :
    besselI 0 t = (2 * Real.pi)⁻¹ * ∫ s in (0 : ℝ)..2 * Real.pi, Real.exp (t * Real.cos s) ∧
      besselI 0 t = ∫ θ, Real.exp (t * angCos θ) ∂angHaar := by
  refine ⟨?_, ?_⟩
  · rw [besselI_eq_interval]
    simp
  · simp [besselI, angMode_zero]

/-- `g = I_0'/I_0` agrees with the campaign `besselRatio = I_1/I_0`. -/
theorem gate_fin068_38_named_potential_definition_gate_besselRatio (t : ℝ) :
    besselRatio t = deriv (besselI 0) t / besselI 0 t := by
  rw [(hasDerivAt_besselI_zero t).deriv]
  rfl

/-- The campaign constants unfold to `b = g(4)`, `κ = 5/b`, `η = 4/5`. -/
theorem gate_fin068_38_named_potential_definition_gate_constants :
    quarticB = besselRatio 4 ∧ quarticKappa = 5 / quarticB ∧ quarticEta = 4 / 5 :=
  ⟨rfl, rfl, rfl⟩

/-- Pointwise form with `I_0 = besselI 0`. -/
theorem gate_fin068_38_named_potential_definition_gate_besselI
    (x y : ℝ) :
    quarticPsi_FIN066 !₂[x, y] =
      (x - 1) ^ 2 / (2 * (5 / besselRatio 4)) +
        y ^ 2 / (2 * (5 / besselRatio 4) * (4 / 5)) -
          Real.log (besselI 0 (Real.sqrt (x ^ 2 + y ^ 2))) := by
  unfold quarticPsi_FIN066
  simp only [quarticKappa, quarticB, quarticEta]
  simp [mul_assoc]

/-- Pointwise form on a point `w` of `EuclideanSpace ℝ (Fin 2)`, with `x = w 0`, `y = w 1`. -/
theorem gate_fin068_38_named_potential_definition_gate_apply
    (w : EuclideanSpace ℝ (Fin 2)) :
    quarticPsi_FIN066 w =
      (w 0 - 1) ^ 2 / (2 * (5 / besselRatio 4)) +
        (w 1) ^ 2 / (2 * (5 / besselRatio 4) * (4 / 5)) -
          Real.log (besselI 0 (Real.sqrt (w 0 ^ 2 + w 1 ^ 2))) := by
  unfold quarticPsi_FIN066
  simp only [quarticKappa, quarticB, quarticEta]
  rw [mul_assoc]

/-- The named potential definition gate: the actual `quarticPsi_FIN066` at the point with
coordinates `(x, y)` equals
`(x-1)^2/(2κ) + y^2/(2κη) - log I_0(√(x²+y²))` with `κ = 5/b`, `b = g(4)`, `η = 4/5` and
`I_0(t) = (2π)⁻¹ ∫_0^{2π} exp (t cos s) ds`. -/
theorem gate_fin068_38_named_potential_definition_gate (x y : ℝ) :
    quarticPsi_FIN066 !₂[x, y] =
      (x - 1) ^ 2 / (2 * (5 / besselRatio 4)) +
        y ^ 2 / (2 * (5 / besselRatio 4) * (4 / 5)) -
          Real.log ((2 * Real.pi)⁻¹ *
            ∫ s in (0 : ℝ)..2 * Real.pi, Real.exp (Real.sqrt (x ^ 2 + y ^ 2) * Real.cos s)) := by
  rw [gate_fin068_38_named_potential_definition_gate_besselI,
    ← (gate_fin068_38_named_potential_definition_gate_besselI_zero_integral _).1]

/-- The identification holds on a neighbourhood of `w₋ = (-4, 0)` (indeed everywhere). -/
theorem gate_fin068_38_named_potential_definition_gate_eventually :
    ∀ᶠ w in nhds (!₂[(-4 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)),
      quarticPsi_FIN066 w =
        (w 0 - 1) ^ 2 / (2 * (5 / besselRatio 4)) +
          (w 1) ^ 2 / (2 * (5 / besselRatio 4) * (4 / 5)) -
            Real.log ((2 * Real.pi)⁻¹ * ∫ s in (0 : ℝ)..2 * Real.pi,
              Real.exp (Real.sqrt (w 0 ^ 2 + w 1 ^ 2) * Real.cos s)) :=
  Filter.Eventually.of_forall fun w => by
    rw [gate_fin068_38_named_potential_definition_gate_apply,
      ← (gate_fin068_38_named_potential_definition_gate_besselI_zero_integral _).1]

end DGPS.Frontier.FIN068
