import DGPS.Frontier.FIN068.T14

/-!
Task id and title: FIN068.15, One derivative step (module `DGPS.Frontier.FIN068.T15`).

Provides:
* `DGPS.Frontier.FIN068.fin068_15_one_derivative_step`: for every `k : ℕ` and every real `t`,
  `HasDerivAt (fun s => K_FIN06814 k s) (K_FIN06814 (k + 1) t) t`, i.e. `d/dt K_k(t) = K_{k+1}(t)`.
* `DGPS.Frontier.FIN068.integrand_hasDerivAt_FIN06815`: pointwise in `θ`, the parameter derivative of
  `s ↦ (cos θ)^k e^{s cos θ}` is `(cos θ)^(k+1) e^{t cos θ}` at `s = t`.
* `DGPS.Frontier.FIN068.integrand_bound_FIN06815`: for `|s - t| < 1`, the absolute value of the
  parameter derivative `(cos θ)^(k+1) e^{s cos θ}` is at most `exp (|t| + 1)`.

R5 notes:
* The measure `m` is read as the normalized Haar measure `angHaar` (`dθ/(2π)`), and `cos θ` is
  `angCos`, as in FIN068.14 (`K_FIN06814`, whose integrability and continuity are imported and not
  re-proved here).
* The specification's "for every natural `k` and real `t`" is stated literally: `k : ℕ`, `t : ℝ`,
  with no restriction on `t`. The derivative is with respect to the real parameter `s` of
  `K_FIN06814 k s`, over all of `ℝ`.
* The specification's "on `|s − t| < 1`" is formalized with `ε = 1` in the Mathlib dominated
  differentiation theorem (`Metric.ball t 1`). The dominator `exp (|t| + 1)` is a constant depending on
  the base point `t` (a local dominator), not a uniform bound in `t`, consistent with the specification.
* The dominator is integrable because `angHaar` is a finite (probability) measure; this is used
  implicitly through `integrable_const`.
* The specification's "the parameter derivative is continuous in `(s,x)` and hence measurable" is
  used in the form of continuity in `θ` for each fixed `s` (`AEStronglyMeasurable` of the derivative
  at the base point); the joint continuity is not separately stated.
* No hypothesis is added; no part of the specification is weakened. The name `_FIN06815` suffix is
  attached to helpers as required by the brief.
-/

open MeasureTheory Real Metric Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Frontier.FIN068

/-- The parameter derivative of the integrand `s ↦ (cos θ)^k e^{s cos θ}` at `s = t`. -/
theorem integrand_hasDerivAt_FIN06815 (k : ℕ) (θ : AngCircle) (t : ℝ) :
    HasDerivAt (fun s : ℝ => angCos θ ^ k * Real.exp (s * angCos θ))
      (angCos θ ^ (k + 1) * Real.exp (t * angCos θ)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * angCos θ) (1 * angCos θ) t :=
    (hasDerivAt_id' t).mul_const (angCos θ)
  have h2 := (h1.exp).const_mul (angCos θ ^ k)
  convert h2 using 1
  rw [pow_succ]
  ring

/-- Uniform-in-`θ` dominator for the parameter derivative on `|s - t| < 1`. -/
theorem integrand_bound_FIN06815 (k : ℕ) {t s : ℝ} (hs : |s - t| < 1) (θ : AngCircle) :
    ‖angCos θ ^ (k + 1) * Real.exp (s * angCos θ)‖ ≤ Real.exp (|t| + 1) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |angCos θ| ≤ 1 := abs_angCos_le_one_FIN06814 θ
  have h2 : |angCos θ ^ (k + 1)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1
  have h3 : |s * angCos θ| ≤ |s| := by
    rw [abs_mul]
    calc |s| * |angCos θ| ≤ |s| * 1 := by gcongr
      _ = |s| := mul_one _
  have h4 : |s| ≤ |t| + 1 := by
    linarith [abs_sub_abs_le_abs_sub s t]
  have h5 : Real.exp (s * angCos θ) ≤ Real.exp (|t| + 1) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (h3.trans h4))
  calc |angCos θ ^ (k + 1)| * Real.exp (s * angCos θ) ≤ 1 * Real.exp (|t| + 1) := by
        gcongr
    _ = Real.exp (|t| + 1) := one_mul _

/-- One derivative step: `d/dt K_k(t) = K_{k+1}(t)` for every natural `k` and real `t`. -/
theorem fin068_15_one_derivative_step (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => K_FIN06814 k s) (K_FIN06814 (k + 1) t) t := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := angHaar)
    (F := fun s θ => angCos θ ^ k * Real.exp (s * angCos θ))
    (F' := fun s θ => angCos θ ^ (k + 1) * Real.exp (s * angCos θ))
    (x₀ := t) (bound := fun _ => Real.exp (|t| + 1)) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s =>
      (fin068_14_uniform_integrability_bounds_positivity_continuous k s).aestronglyMeasurable)
    (fin068_14_uniform_integrability_bounds_positivity_integrable k t)
    ((fin068_14_uniform_integrability_bounds_positivity_continuous (k + 1) t).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ s hs => by
      have hs' : |s - t| < 1 := by
        have := Metric.mem_ball.mp hs
        rwa [Real.dist_eq] at this
      exact integrand_bound_FIN06815 k hs' θ)
    (integrable_const _)
    (Filter.Eventually.of_forall fun θ s _ => integrand_hasDerivAt_FIN06815 k θ s)
  exact key.2

end DGPS.Frontier.FIN068
