import DGPS.Circle.BesselMoments

/-!
Task id and title: FIN068.14, Uniform integrability, bounds, and positivity (module
`DGPS.Frontier.FIN068.T14`).

Provides:
* `DGPS.Frontier.FIN068.K_FIN06814`: `K_k(t) = ∫ (cos θ)^k e^{t cos θ} dm` on the angular circle
  `AddCircle (2π)` with the normalized Haar measure `angHaar` (same body as the gate-37 definition).
* `DGPS.Frontier.FIN068.fin068_14_uniform_integrability_bounds_positivity`: for every `k`, every
  `M ≥ 0` and every `|t| ≤ M`, the integrand of `K_k(t)` is continuous, its absolute value is at
  most `exp M` at every point, and `|K_k(t)| ≤ exp M`; moreover `exp (-|t|) ≤ K_0(t)` and
  `0 < K_0(t)` for every real `t`.
* `DGPS.Frontier.FIN068.fin068_14_uniform_integrability_bounds_positivity_continuous`: the
  integrand `θ ↦ (cos θ)^k e^{t cos θ}` is continuous (for every real `t`).
* `DGPS.Frontier.FIN068.fin068_14_uniform_integrability_bounds_positivity_integrand_bound`:
  `|(cos θ)^k e^{t cos θ}| ≤ exp M` for `|t| ≤ M`.
* `DGPS.Frontier.FIN068.fin068_14_uniform_integrability_bounds_positivity_integrable`: the
  integrand is integrable for `angHaar`.
* `DGPS.Frontier.FIN068.fin068_14_uniform_integrability_bounds_positivity_abs_le`:
  `|K_k(t)| ≤ exp M` for `|t| ≤ M`.
* `DGPS.Frontier.FIN068.fin068_14_uniform_integrability_bounds_positivity_lower`:
  `exp (-|t|) ≤ K_0(t)` for every real `t`.
* `DGPS.Frontier.FIN068.fin068_14_uniform_integrability_bounds_positivity_pos`: `0 < K_0(t)`.

R5 notes:
* The measure `m` is read as the normalized Haar measure `angHaar` (`dθ/(2π)`, a probability
  measure), the reading used by the gate FIN068.37; `cos θ` is `angCos`.
* The campaign has no `K_k`; it is introduced here as the helper `K_FIN06814` with the body of the
  gate-37 definition (this task has no prerequisite inside the frontier, so T37 is not imported).
* No hypothesis is added: `0 ≤ M` and `|t| ≤ M` are exactly those of the specification; continuity,
  integrability and positivity hold for every real `t`, and `|c|^k ≤ 1` is used for every `k`.
* The specification's "integrand is continuous and its absolute value is at most `exp M`" is
  stated pointwise (`∀ θ`), and integrability is recorded as a separate corollary.
-/

open MeasureTheory Real
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Frontier.FIN068

/-- `K_k(t) = ∫ (cos θ)^k e^{t cos θ} dm` over the angular circle with normalized Haar measure. -/
noncomputable def K_FIN06814 (k : ℕ) (t : ℝ) : ℝ :=
  ∫ θ, angCos θ ^ k * Real.exp (t * angCos θ) ∂angHaar

theorem abs_angCos_le_one_FIN06814 (θ : AngCircle) : |angCos θ| ≤ 1 :=
  abs_angMode_le 1 θ

theorem fin068_14_uniform_integrability_bounds_positivity_continuous (k : ℕ) (t : ℝ) :
    Continuous (fun θ : AngCircle => angCos θ ^ k * Real.exp (t * angCos θ)) := by
  have hc : Continuous angCos := continuous_angMode 1
  fun_prop

theorem fin068_14_uniform_integrability_bounds_positivity_integrand_bound (k : ℕ) {M t : ℝ}
    (ht : |t| ≤ M) (θ : AngCircle) :
    |angCos θ ^ k * Real.exp (t * angCos θ)| ≤ Real.exp M := by
  have h1 : |angCos θ| ≤ 1 := abs_angCos_le_one_FIN06814 θ
  have h2 : |angCos θ ^ k| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1
  have h3 : |t * angCos θ| ≤ |t| := by
    rw [abs_mul]; calc |t| * |angCos θ| ≤ |t| * 1 := by gcongr
      _ = |t| := mul_one _
  have h4 : Real.exp (t * angCos θ) ≤ Real.exp M :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (h3.trans ht))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |angCos θ ^ k| * Real.exp (t * angCos θ) ≤ 1 * Real.exp M := by
        gcongr
    _ = Real.exp M := one_mul _

theorem fin068_14_uniform_integrability_bounds_positivity_integrable (k : ℕ) (t : ℝ) :
    Integrable (fun θ : AngCircle => angCos θ ^ k * Real.exp (t * angCos θ)) angHaar :=
  (fin068_14_uniform_integrability_bounds_positivity_continuous k t).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fin068_14_uniform_integrability_bounds_positivity_abs_le (k : ℕ) {M t : ℝ}
    (ht : |t| ≤ M) : |K_FIN06814 k t| ≤ Real.exp M := by
  have h := norm_integral_le_of_norm_le_const (μ := angHaar)
    (f := fun θ : AngCircle => angCos θ ^ k * Real.exp (t * angCos θ)) (C := Real.exp M)
    (Filter.Eventually.of_forall fun θ => by
      simpa [Real.norm_eq_abs] using
        fin068_14_uniform_integrability_bounds_positivity_integrand_bound k ht θ)
  simpa [K_FIN06814, Real.norm_eq_abs] using h

theorem fin068_14_uniform_integrability_bounds_positivity_lower (t : ℝ) :
    Real.exp (-|t|) ≤ K_FIN06814 0 t := by
  have hint := fin068_14_uniform_integrability_bounds_positivity_integrable 0 t
  have h := integral_mono (μ := angHaar) (integrable_const (Real.exp (-|t|))) hint
    (fun θ => by
      have h1 : |angCos θ| ≤ 1 := abs_angCos_le_one_FIN06814 θ
      have h3 : -|t| ≤ t * angCos θ := by
        have : |t * angCos θ| ≤ |t| := by
          rw [abs_mul]; calc |t| * |angCos θ| ≤ |t| * 1 := by gcongr
            _ = |t| := mul_one _
        linarith [neg_abs_le (t * angCos θ)]
      simpa using Real.exp_le_exp.mpr h3)
  simpa [K_FIN06814] using h

theorem fin068_14_uniform_integrability_bounds_positivity_pos (t : ℝ) : 0 < K_FIN06814 0 t :=
  lt_of_lt_of_le (Real.exp_pos _) (fin068_14_uniform_integrability_bounds_positivity_lower t)

theorem fin068_14_uniform_integrability_bounds_positivity (k : ℕ) {M : ℝ} (_hM : 0 ≤ M) :
    (∀ t : ℝ, |t| ≤ M →
      Continuous (fun θ : AngCircle => angCos θ ^ k * Real.exp (t * angCos θ)) ∧
      (∀ θ : AngCircle, |angCos θ ^ k * Real.exp (t * angCos θ)| ≤ Real.exp M) ∧
      |K_FIN06814 k t| ≤ Real.exp M) ∧
    (∀ t : ℝ, Real.exp (-|t|) ≤ K_FIN06814 0 t ∧ 0 < K_FIN06814 0 t) :=
  ⟨fun _ ht =>
    ⟨fin068_14_uniform_integrability_bounds_positivity_continuous _ _,
     fun θ => fin068_14_uniform_integrability_bounds_positivity_integrand_bound k ht θ,
     fin068_14_uniform_integrability_bounds_positivity_abs_le k ht⟩,
   fun t => ⟨fin068_14_uniform_integrability_bounds_positivity_lower t,
     fin068_14_uniform_integrability_bounds_positivity_pos t⟩⟩

end DGPS.Frontier.FIN068
