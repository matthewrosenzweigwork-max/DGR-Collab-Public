import DGPS.FiniteN.QuarticSaddleGlobalFIN066

/-!
Bindings (campaign paths relative to `Campaign/`; line numbers at base commit a2af2f9):

| Source object / notion | Actual declaration (file:line) | Type / binders | Discrepancy with the specification text |
|---|---|---|---|
| measure `m` in `K_k(t) = ∫ cos^k θ e^{t cos θ} dm` | `DGPS.Circle.AngularNormalization.angHaar` (`DGPS/Circle/AngularNormalization.lean:26`), on `AngCircle = AddCircle (2 * π)` (`:24`) | `Measure AngCircle` (normalized Haar, i.e. `dθ/(2π)`) | none: `m` is read as this probability measure, matching `I₀(t) = ∫ e^{t cos θ} dθ/(2π)` |
| `cos θ` | `DGPS.Circle.BesselMoments.angCos` (`DGPS/Circle/BesselMoments.lean:41`) `= angMode 1`, `angMode` at `:18` | `AngCircle → ℝ` | none |
| `I_n`, hence `I₀`, `I₁` | `DGPS.Circle.BesselMoments.besselI` (`DGPS/Circle/BesselMoments.lean:44`); body `∫ θ, Real.exp (t * angCos θ) * angMode n θ ∂angHaar` | `(n : ℕ) (t : ℝ) : ℝ` | none: it IS an integral definition (not a series), so unfolding closes the gate; the integrand carries `cos (n θ)`, which is `1` for `n = 0` and `cos θ` for `n = 1` |
| `besselRatio` | `DGPS.Circle.BesselMoments.besselRatio` (`DGPS/Circle/BesselMoments.lean:52`); body `besselI 1 t / besselI 0 t` | `(t : ℝ) : ℝ` | none |
| `K_k` | NOT in the campaign; introduced here as `K_FIN06837` | `(k : ℕ) (t : ℝ) : ℝ` | new helper definition, `∫ θ, angCos θ ^ k * Real.exp (t * angCos θ) ∂angHaar` |
| `quarticB` (`b = g(4)`) | `DGPS.Models.quarticB` (`DGPS/FiniteN/QuarticSaddle.lean:41`) `:= besselRatio 4` | `ℝ` | namespace is `DGPS.Models`, not `DGPS.FiniteN` |
| `quarticKappa` (`κ = 5/b`) | `DGPS.Models.quarticKappa` (`DGPS/FiniteN/QuarticSaddle.lean:44`) `:= 5 / quarticB` | `ℝ` | none |
| `quarticEta` (`η = 4/5`) | `DGPS.Models.quarticEta` (`DGPS/FiniteN/QuarticSaddle.lean:47`) `:= 4 / 5` | `ℝ` | none |
| `quarticPsi_FIN066` | `DGPS.FiniteN.QuarticSaddleGlobalFIN066.quarticPsi_FIN066` (`DGPS/FiniteN/QuarticSaddleGlobalFIN066.lean:389`) | `(w : EuclideanSpace ℝ (Fin 2)) : ℝ` | body is printed and uses `besselI 0 (√(w 0 ^ 2 + w 1 ^ 2))`; the equality with the displayed formula is Task 38, not this gate |
| derivative `I₀' = I₁` | `DGPS.Circle.BesselMoments.hasDerivAt_besselI_zero` (`:409`) | `HasDerivAt (besselI 0) (besselI 1 t) t` | none |
| `g'` | `DGPS.Circle.BesselMoments.hasDerivAt_besselRatio` (`:449`) | `HasDerivAt besselRatio ((∫ cos·exp·cos ∗ I₀ - I₁ ∗ I₁)/I₀²) t` | its numerator integral is exactly `K 2 t` |
| other `besselI` | `DGPS.Examples.ThreeSpeciesCircle.besselI` (`DGPS/Examples/ThreeSpeciesCircle/Model.lean:79`) | `(k : ℕ) (h : ℝ) : ℝ` via an interval integral | a different declaration with the same short name; it is NOT the object used by `besselRatio` and is not bound here |

Task id and title: FIN068.37, Named Bessel integral and ratio definition gate (module `DGPS.Frontier.FIN068.T37`).

Provides:
* `DGPS.Frontier.FIN068.K_FIN06837`: `K_k(t) = ∫ (cos θ)^k e^{t cos θ} dm` on the angular circle.
* `DGPS.Frontier.FIN068.gate_fin068_37_named_bessel_integral_ratio_definition_gate`: for every real `t`,
  `besselI 0 t = K 0 t`, `besselI 1 t = K 1 t` and `besselRatio t = K 1 t / K 0 t`.
* `DGPS.Frontier.FIN068.gate_fin068_37_named_bessel_integral_ratio_definition_gate_interval`:
  `K k t = (2π)⁻¹ ∫ s in 0..2π, cos s ^ k * exp (t * cos s)`.
* `DGPS.Frontier.FIN068.gate_fin068_37_named_bessel_integral_ratio_definition_gate_pos`: `0 < K 0 t`.
* `DGPS.Frontier.FIN068.gate_fin068_37_named_bessel_integral_ratio_definition_gate_hasDerivAt_K0`:
  `HasDerivAt (K 0) (K 1 t) t` (the identification `I₀' = I₁ = K₁`).
* `DGPS.Frontier.FIN068.gate_fin068_37_named_bessel_integral_ratio_definition_gate_hasDerivAt_ratio`:
  `HasDerivAt besselRatio ((K 2 t * K 0 t - K 1 t ^ 2) / K 0 t ^ 2) t`.
* `DGPS.Frontier.FIN068.gate_fin068_37_named_bessel_integral_ratio_definition_gate_quartic`:
  `quarticB = K 1 4 / K 0 4`, `quarticKappa = 5 * K 0 4 / K 1 4` and
  `deriv besselRatio 4 = (K 2 4 * K 0 4 - K 1 4 ^ 2) / K 0 4 ^ 2` (the `v₀` of FIN065 in `K` form).
* `DGPS.Frontier.FIN068.gate_fin068_37_named_bessel_integral_ratio_definition_gate_psi`:
  `quarticPsi_FIN066 w` with `besselI 0` replaced by `K 0` (a restatement of the actual body).

R5 notes:
* The campaign defines `besselI n` directly by the angular integral, so no series-integral equality
  is needed; every identity is proved by unfolding, `angMode 0 = 1` and `angMode 1 = angCos`.
* The measure `m` of the specification is read as the normalized Haar measure `angHaar`
  (`dθ/(2π)`), the only reading consistent with `I₀(t) = ∫ e^{t cos θ} dθ/(2π)`.
* The identities are proved for every real `t` (no neighbourhood of `4` is needed).
* No hypothesis is added to any specification statement.
* The ratio identity is literal division `K 1 t / K 0 t`; `K 0 t > 0` is recorded separately,
  but is not needed for the identity (Lean division).
* The derivative statements about `v₀` are provable consequences recorded for downstream use; the
  equality of `quarticPsi_FIN066` with the displayed formula (Task 38) is not claimed here
  beyond the `K 0` restatement of its actual body.
-/

open MeasureTheory Real
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Frontier.FIN068

/-- `K_k(t) = ∫ (cos θ)^k e^{t cos θ} dm` over the angular circle with normalized Haar measure. -/
noncomputable def K_FIN06837 (k : ℕ) (t : ℝ) : ℝ :=
  ∫ θ, angCos θ ^ k * Real.exp (t * angCos θ) ∂angHaar

theorem besselI_zero_eq_K_FIN06837 (t : ℝ) : besselI 0 t = K_FIN06837 0 t := by
  unfold besselI K_FIN06837
  rw [angMode_zero]
  simp

theorem besselI_one_eq_K_FIN06837 (t : ℝ) : besselI 1 t = K_FIN06837 1 t := by
  unfold besselI K_FIN06837
  have : angMode 1 = angCos := rfl
  rw [this]
  simp [mul_comm]

theorem besselI2Moment_eq_K_FIN06837 (t : ℝ) :
    (∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar) = K_FIN06837 2 t := by
  unfold K_FIN06837
  congr 1
  funext θ
  ring

/-- Main gate: the campaign `I₀`, `I₁` and `besselRatio` are `K₀`, `K₁` and `K₁/K₀`, for every `t`. -/
theorem gate_fin068_37_named_bessel_integral_ratio_definition_gate :
    ∀ t : ℝ, besselI 0 t = K_FIN06837 0 t ∧ besselI 1 t = K_FIN06837 1 t ∧
      besselRatio t = K_FIN06837 1 t / K_FIN06837 0 t := fun t =>
  ⟨besselI_zero_eq_K_FIN06837 t, besselI_one_eq_K_FIN06837 t, by
    unfold besselRatio
    rw [besselI_zero_eq_K_FIN06837, besselI_one_eq_K_FIN06837]⟩

theorem gate_fin068_37_named_bessel_integral_ratio_definition_gate_interval (k : ℕ) (t : ℝ) :
    K_FIN06837 k t =
      (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π, Real.cos s ^ k * Real.exp (t * Real.cos s) := by
  unfold K_FIN06837
  apply integral_ang
  intro s
  simp [angCos, angMode_coe]

theorem gate_fin068_37_named_bessel_integral_ratio_definition_gate_pos (t : ℝ) :
    0 < K_FIN06837 0 t := by
  rw [← besselI_zero_eq_K_FIN06837]
  exact besselI_zero_pos t

theorem gate_fin068_37_named_bessel_integral_ratio_definition_gate_hasDerivAt_K0 (t : ℝ) :
    HasDerivAt (K_FIN06837 0) (K_FIN06837 1 t) t := by
  have h := hasDerivAt_besselI_zero t
  have e : besselI 0 = K_FIN06837 0 := funext besselI_zero_eq_K_FIN06837
  rw [e, besselI_one_eq_K_FIN06837] at h
  exact h

theorem gate_fin068_37_named_bessel_integral_ratio_definition_gate_hasDerivAt_ratio (t : ℝ) :
    HasDerivAt besselRatio
      ((K_FIN06837 2 t * K_FIN06837 0 t - K_FIN06837 1 t ^ 2) / K_FIN06837 0 t ^ 2) t := by
  have h := hasDerivAt_besselRatio t
  rw [besselI2Moment_eq_K_FIN06837, besselI_zero_eq_K_FIN06837, besselI_one_eq_K_FIN06837] at h
  convert h using 2
  ring

theorem gate_fin068_37_named_bessel_integral_ratio_definition_gate_quartic :
    DGPS.Models.quarticB = K_FIN06837 1 4 / K_FIN06837 0 4 ∧
    DGPS.Models.quarticKappa = 5 * K_FIN06837 0 4 / K_FIN06837 1 4 ∧
    deriv besselRatio 4 =
      (K_FIN06837 2 4 * K_FIN06837 0 4 - K_FIN06837 1 4 ^ 2) / K_FIN06837 0 4 ^ 2 := by
  have hb : DGPS.Models.quarticB = K_FIN06837 1 4 / K_FIN06837 0 4 :=
    (gate_fin068_37_named_bessel_integral_ratio_definition_gate 4).2.2
  refine ⟨hb, ?_, (gate_fin068_37_named_bessel_integral_ratio_definition_gate_hasDerivAt_ratio 4).deriv⟩
  unfold DGPS.Models.quarticKappa
  rw [hb, div_div_eq_mul_div]

theorem gate_fin068_37_named_bessel_integral_ratio_definition_gate_psi
    (w : EuclideanSpace ℝ (Fin 2)) :
    DGPS.FiniteN.QuarticSaddleGlobalFIN066.quarticPsi_FIN066 w =
      (w 0 - 1) ^ 2 / (2 * DGPS.Models.quarticKappa) +
        (w 1) ^ 2 / (2 * (DGPS.Models.quarticKappa * DGPS.Models.quarticEta)) -
        Real.log (K_FIN06837 0 (Real.sqrt (w 0 ^ 2 + w 1 ^ 2))) := by
  unfold DGPS.FiniteN.QuarticSaddleGlobalFIN066.quarticPsi_FIN066
  rw [besselI_zero_eq_K_FIN06837]

end DGPS.Frontier.FIN068
