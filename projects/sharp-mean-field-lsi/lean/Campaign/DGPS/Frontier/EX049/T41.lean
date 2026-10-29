import DGPS.Frontier.EX049.T07
import DGPS.Frontier.EX049.T25

/-!
# EX049.41: Quantified density and multiplier bounds

Task id and title: EX049.41, "Quantified density and multiplier bounds" (node EX049, frontier unit,
leaf formalization, prerequisites EX049.05, EX049.07 and EX049.25).  For a real `h ≥ 2` put
`P = 2h + 6√h`.  On the angular circle let `U = 1 - cos θ`, `Φ_h = hU + R_h(U)` with `R_h = corr h`,
`Z_h = ∫ exp(-Φ_h) dm` and `q_h = Z_h⁻¹ exp(-Φ_h)`.  Then `0 ≤ Φ_h ≤ P`, `e^{-P} ≤ Z_h ≤ 1`,
`e^{-P} ≤ q_h ≤ e^P`, and `q_h`, `√q_h`, `1/√q_h` are smooth and periodic with bounded first
derivatives.

The proof uses `0 ≤ U ≤ 2` and the correction bound of EX049.07, the bound `e^{-P} ≤ exp(-Φ_h) ≤ 1`
integrated against the probability measure, and the quotient bounds `Z_h⁻¹ ∈ [1, e^P]`.

## Provides
* `DGPS.Frontier.EX049.ex049_41_quantified_density_multiplier_bounds` : the main statement, for
  `2 ≤ h`, with six conjuncts: the bounds on `Φ_h`, the bounds on `Z_h`, the bounds on `q_h`, and
  smoothness, periodicity and bounded derivatives of `q_h`, `√q_h` and `1/√q_h`.
* `DGPS.Frontier.EX049.integrand_quot_EX04941` : on `(0,2)` the campaign integrand equals the
  quotient `quot_EX04906 h`.
* `DGPS.Frontier.EX049.phi_bounds_EX04941` : `0 ≤ hU + R_h(U) ≤ 2h + 6√h` at every point of the circle.
* `DGPS.Frontier.EX049.logq_bounds_EX04941` : `e^{-P} ≤ exp(logq h θ) ≤ 1` at every point, where
  `logq h = -Φ_h`.
* `DGPS.Frontier.EX049.Zh_bounds_EX04941` : `e^{-P} ≤ Z_h ≤ 1`.
* `DGPS.Frontier.EX049.qAng_bounds_EX04941` : `e^{-P} ≤ q_h(θ) ≤ e^P` at every point of the circle.
* `DGPS.Frontier.EX049.bounded_deriv_EX04941` : a `C^∞` function on `ℝ` with period `2π` has a
  bounded derivative.

## R5 notes
* The only hypothesis is `2 ≤ h`, the specification's "fixed `h ≥ 2`".  No hypothesis is added and
  no conclusion is weakened.
* The densities live on the circle `AngCircle` (`AddCircle (2π)`, the campaign's circle) with the
  normalized Haar measure `angHaar`.  Smoothness, periodicity and bounded derivatives are stated for
  the lifts `t ↦ f (t : Real.Angle)` on `ℝ`.  Periodicity of a lift is the same as being a function
  on the circle, since `(t + 2π : Real.Angle) = t`.  "Bounded first derivatives" is read as
  `∃ C, ∀ t, |deriv f t| ≤ C` for the lift.  Because the lift is periodic, this bound covers the
  whole circle.
* `Φ_h` is written as `h * Uang θ + corr h (Uang θ)`, the specification's `hU + R_h(U)` with `R_h`
  bound to `corr h` by EX049.25.  The campaign integrand is the continuous totalization of `r_h`.
  It equals `r_h` on `(0,2)` (EX049.25, `integrand_eq_rsrc_EX04925`), and the values at `0` and
  `2` do not enter any integral.  The bound of EX049.07 is applied to `g = integrand h` on
  `U = univ`, so no abstract smooth extension is needed here.
* `Z_h` is `Zh h`, the integral of `exp (logq h θ)` against `angHaar`.  The identity
  `logq h θ = -Φ_h θ` is proved in this file and is what the specification's `∫ exp(-Φ_h) dm` means.
* `q_h` is `qAng h`, the campaign density `Z_h⁻¹ exp(-Φ_h)`, bound to the specification by EX049.25.
* `√q_h` and `1/√q_h` are written as `Real.sqrt (qAng h t)` and `1 / Real.sqrt (qAng h t)`.  Both
  are defined everywhere because `q_h > 0`.
* Smoothness of `q_h` uses `qAng_lift`, `contDiff_Lh` and `contDiff_sqrtQ` from the campaign ground
  state file, not EX049.05 directly.  EX049.05 enters the proof through EX049.07.
* The bound `Φ_h ≤ P` is not optimized.  It is the specification's constant `P = 2h + 6√h`.
-/

open scoped ContDiff
open Set MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredRankOne
open DGPS.Examples.EngineeredGroundState

namespace DGPS.Frontier.EX049

/-- On `(0,2)` the campaign integrand agrees with the quotient `quot_EX04906 h`. -/
theorem integrand_quot_EX04941 (h : ℝ) (hh : 0 < h) {v : ℝ} (hv : v ∈ Ioo (0:ℝ) 2) :
    integrand h v = quot_EX04906 h v :=
  (integrand_eq_rsrc_EX04925 h hh hv.1.ne' hv.2.ne).trans rfl

/-- For `h ≥ 2` and every `θ`, `0 ≤ hU + R_h(U) ≤ 2h + 6√h`. -/
theorem phi_bounds_EX04941 (h : ℝ) (hh : 2 ≤ h) (θ : AngCircle) :
    0 ≤ h * Uang θ + corr h (Uang θ) ∧
      h * Uang θ + corr h (Uang θ) ≤ 2 * h + 6 * Real.sqrt h := by
  have hpos : 0 < h := by linarith
  have hc : ContDiffOn ℝ ∞ (integrand h) univ := (contDiff_integrand h hpos).contDiffOn
  have hQg : ∀ v ∈ Ioo (0:ℝ) 2, integrand h v = quot_EX04906 h v :=
    fun v hv => integrand_quot_EX04941 h hpos hv
  obtain ⟨hu0, hu2⟩ := Uang_mem θ
  obtain ⟨hc0, hc1⟩ := integral_bounds_EX04907 h hh (integrand h) univ (subset_univ _) hc hQg
    (Uang θ) ⟨hu0, hu2⟩
  have hc0' : 0 ≤ corr h (Uang θ) := hc0
  have hc1' : corr h (Uang θ) ≤ 4 + 3 * Real.log h := hc1
  have hlog : 4 + 3 * Real.log h ≤ 6 * Real.sqrt h := sqrt_chain_EX04907 h hh
  constructor
  · nlinarith [mul_nonneg hpos.le hu0]
  · nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hu2)]

/-- Pointwise bound `e^{-P} ≤ exp(logq h θ) ≤ 1`, where `logq h = -Φ_h` and `P = 2h + 6√h`. -/
theorem logq_bounds_EX04941 (h : ℝ) (hh : 2 ≤ h) (θ : AngCircle) :
    Real.exp (-(2 * h + 6 * Real.sqrt h)) ≤ Real.exp (logq h θ) ∧ Real.exp (logq h θ) ≤ 1 := by
  obtain ⟨p0, p1⟩ := phi_bounds_EX04941 h hh θ
  have e : logq h θ = -(h * Uang θ + corr h (Uang θ)) := by
    unfold logq
    ring
  have a1 : -(2 * h + 6 * Real.sqrt h) ≤ -(h * Uang θ + corr h (Uang θ)) := by linarith
  have a2 : -(h * Uang θ + corr h (Uang θ)) ≤ 0 := by linarith
  have a3 := Real.exp_le_exp.2 a2
  rw [Real.exp_zero] at a3
  rw [e]
  exact ⟨Real.exp_le_exp.2 a1, a3⟩

/-- The normalizing constant satisfies `e^{-P} ≤ Z_h ≤ 1` with `P = 2h + 6√h`. -/
theorem Zh_bounds_EX04941 (h : ℝ) (hh : 2 ≤ h) :
    Real.exp (-(2 * h + 6 * Real.sqrt h)) ≤ Zh h ∧ Zh h ≤ 1 := by
  have hpos : 0 < h := by linarith
  have hint : Integrable (fun θ : AngCircle => Real.exp (logq h θ)) angHaar :=
    (Real.continuous_exp.comp (continuous_logq h hpos)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  constructor
  · have h1 := integral_mono (integrable_const (Real.exp (-(2 * h + 6 * Real.sqrt h)))) hint
      (fun θ => (logq_bounds_EX04941 h hh θ).1)
    unfold Zh
    simpa using h1
  · have h1 := integral_mono hint (integrable_const (1:ℝ))
      (fun θ => (logq_bounds_EX04941 h hh θ).2)
    unfold Zh
    simpa using h1

/-- The density satisfies `e^{-P} ≤ q_h(θ) ≤ e^P` at every point, with `P = 2h + 6√h`. -/
theorem qAng_bounds_EX04941 (h : ℝ) (hh : 2 ≤ h) (θ : AngCircle) :
    Real.exp (-(2 * h + 6 * Real.sqrt h)) ≤ qAng h θ ∧
      qAng h θ ≤ Real.exp (2 * h + 6 * Real.sqrt h) := by
  have hpos : 0 < h := by linarith
  obtain ⟨hZlo, hZhi⟩ := Zh_bounds_EX04941 h hh
  have hZpos : 0 < Zh h := Zh_pos h hpos
  obtain ⟨hE1, hE2⟩ := logq_bounds_EX04941 h hh θ
  have hEpos : 0 < Real.exp (logq h θ) := Real.exp_pos _
  have hinv1 : 1 ≤ (Zh h)⁻¹ := by
    nlinarith [mul_nonneg (sub_nonneg.2 hZhi) (inv_pos.2 hZpos).le, mul_inv_cancel₀ hZpos.ne']
  have hinv2 : (Zh h)⁻¹ ≤ Real.exp (2 * h + 6 * Real.sqrt h) := by
    have h1 : (Zh h)⁻¹ ≤ (Real.exp (-(2 * h + 6 * Real.sqrt h)))⁻¹ :=
      inv_anti₀ (Real.exp_pos _) hZlo
    rwa [Real.exp_neg, inv_inv] at h1
  unfold qAng
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hinv1) hEpos.le]
  · nlinarith [mul_nonneg (Real.exp_pos (2 * h + 6 * Real.sqrt h)).le (sub_nonneg.2 hE2),
      mul_nonneg (sub_nonneg.2 hinv2) hEpos.le]

/-- A `C^∞` function on `ℝ` with period `2π` has a bounded derivative.  The derivative is
continuous and periodic, so its values are attained on `[0, 2π]`. -/
theorem bounded_deriv_EX04941 {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (2 * Real.pi)) : ∃ C : ℝ, ∀ t : ℝ, |deriv f t| ≤ C := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hdp : Function.Periodic (deriv f) (2 * Real.pi) :=
    DGPS.Circle.StationaryFlux.periodic_deriv hp
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) (2 * Real.pi))).exists_bound_of_continuousOn
    hd.continuousOn
  refine ⟨C, fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hdp.exists_mem_Ico₀ Real.two_pi_pos t
  have hy' := hC y (Ico_subset_Icc_self hy)
  rw [hyt, ← Real.norm_eq_abs]
  exact hy'

/-- Quantified density and multiplier bounds.  For `h ≥ 2` and `P = 2h + 6√h`: `0 ≤ Φ_h ≤ P`,
`e^{-P} ≤ Z_h ≤ 1`, `e^{-P} ≤ q_h ≤ e^P`, and `q_h`, `√q_h`, `1/√q_h` are smooth, `2π`-periodic
and have bounded first derivatives (read on the lift to `ℝ`). -/
theorem ex049_41_quantified_density_multiplier_bounds (h : ℝ) (hh : 2 ≤ h) :
    (∀ θ : AngCircle, 0 ≤ h * Uang θ + corr h (Uang θ) ∧
        h * Uang θ + corr h (Uang θ) ≤ 2 * h + 6 * Real.sqrt h) ∧
    (Real.exp (-(2 * h + 6 * Real.sqrt h)) ≤ Zh h ∧ Zh h ≤ 1) ∧
    (∀ θ : AngCircle, Real.exp (-(2 * h + 6 * Real.sqrt h)) ≤ qAng h θ ∧
        qAng h θ ≤ Real.exp (2 * h + 6 * Real.sqrt h)) ∧
    (ContDiff ℝ ∞ (fun t : ℝ => qAng h (t : Real.Angle)) ∧
        Function.Periodic (fun t : ℝ => qAng h (t : Real.Angle)) (2 * Real.pi) ∧
        ∃ C : ℝ, ∀ t : ℝ, |deriv (fun s : ℝ => qAng h (s : Real.Angle)) t| ≤ C) ∧
    (ContDiff ℝ ∞ (fun t : ℝ => Real.sqrt (qAng h (t : Real.Angle))) ∧
        Function.Periodic (fun t : ℝ => Real.sqrt (qAng h (t : Real.Angle))) (2 * Real.pi) ∧
        ∃ C : ℝ, ∀ t : ℝ, |deriv (fun s : ℝ => Real.sqrt (qAng h (s : Real.Angle))) t| ≤ C) ∧
    (ContDiff ℝ ∞ (fun t : ℝ => 1 / Real.sqrt (qAng h (t : Real.Angle))) ∧
        Function.Periodic (fun t : ℝ => 1 / Real.sqrt (qAng h (t : Real.Angle))) (2 * Real.pi) ∧
        ∃ C : ℝ, ∀ t : ℝ, |deriv (fun s : ℝ => 1 / Real.sqrt (qAng h (s : Real.Angle))) t| ≤ C) := by
  have hpos : 0 < h := by linarith
  have hqc : ContDiff ℝ ∞ (fun t : ℝ => qAng h (t : Real.Angle)) := by
    have e : (fun t : ℝ => qAng h (t : Real.Angle)) = fun t => (Zh h)⁻¹ * Real.exp (Lh h t) :=
      funext (qAng_lift h)
    rw [e]
    exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_Lh h hpos))
  have hqp : Function.Periodic (fun t : ℝ => qAng h (t : Real.Angle)) (2 * Real.pi) := by
    intro t
    show qAng h ((t + 2 * Real.pi : ℝ) : Real.Angle) = qAng h (t : Real.Angle)
    rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
  have hsc : ContDiff ℝ ∞ (fun t : ℝ => Real.sqrt (qAng h (t : Real.Angle))) :=
    contDiff_sqrtQ h hpos
  have hsp : Function.Periodic (fun t : ℝ => Real.sqrt (qAng h (t : Real.Angle))) (2 * Real.pi) :=
    fun t => congrArg Real.sqrt (hqp t)
  have hic : ContDiff ℝ ∞ (fun t : ℝ => 1 / Real.sqrt (qAng h (t : Real.Angle))) :=
    contDiff_const.div hsc (fun t => (sqrtQ_pos h hpos t).ne')
  have hip : Function.Periodic (fun t : ℝ => 1 / Real.sqrt (qAng h (t : Real.Angle)))
      (2 * Real.pi) :=
    fun t => congrArg (fun x => 1 / x) (hsp t)
  exact ⟨fun θ => phi_bounds_EX04941 h hh θ, Zh_bounds_EX04941 h hh,
    fun θ => qAng_bounds_EX04941 h hh θ,
    ⟨hqc, hqp, bounded_deriv_EX04941 hqc hqp⟩, ⟨hsc, hsp, bounded_deriv_EX04941 hsc hsp⟩,
    ⟨hic, hip, bounded_deriv_EX04941 hic hip⟩⟩

end DGPS.Frontier.EX049
