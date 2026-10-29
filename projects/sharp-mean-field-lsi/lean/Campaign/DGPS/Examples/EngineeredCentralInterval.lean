import DGPS.Examples.EngineeredGroundState
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Interval ground-state extension for EX040

The ground-state identity is extended from smooth tests to absolutely continuous interval
representatives of finite weighted energy. Endpoint traces are arbitrary. This module does not
assert the central conditional LSI.
-/

open MeasureTheory Real Set Filter Topology

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredGroundState
open DGPS.Circle.AngularNormalization

/-- The pointwise conjugation identity only needs differentiability at the point. -/
theorem pointwise_ground_state_EX040 (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g t) :
    let w := liftGroundStateConj h g
    deriv g t ^ 2 * qAng h (t : AngCircle) =
      deriv w t ^ 2 + groundPot h t * w t ^ 2 -
        deriv (fun s => driftB h s * w s ^ 2 / 2) t := by
  intro w
  have hw : HasDerivAt w
      (deriv g t * sqrtQ h t + g t * (driftB h t / 2 * sqrtQ h t)) t :=
    hg.hasDerivAt.mul (hasDerivAt_sqrtQ h hh t)
  have hwd := hw.deriv
  have hb : HasDerivAt (driftB h) (deriv (driftB h) t) t :=
    (((contDiff_driftB h hh).differentiable (by simp)) t).hasDerivAt
  have hw2 : HasDerivAt (fun s => w s ^ 2)
      (2 * w t * (deriv g t * sqrtQ h t + g t * (driftB h t / 2 * sqrtQ h t))) t := by
    have hraw := hw.mul hw
    convert hraw using 1
    · funext s
      simp only [pow_two, Pi.mul_apply]
    · ring
  have hF : HasDerivAt (fun s => driftB h s * w s ^ 2 / 2)
      (deriv (driftB h) t * w t ^ 2 / 2 + driftB h t * w t *
        (deriv g t * sqrtQ h t + g t * (driftB h t / 2 * sqrtQ h t))) t := by
    convert (hb.mul hw2).div_const 2 using 1
    ring
  have hq : qAng h (t : AngCircle) = sqrtQ h t ^ 2 :=
    (sqrtQ_sqrtQ h hh t).symm
  rw [hF.deriv, hwd, hq]
  have hwval : w t = g t * sqrtQ h t := rfl
  rw [hwval]
  unfold groundPot
  ring

/-- EX038 on any interval for an absolutely continuous test of finite weighted energy.
No endpoint condition is imposed. -/
theorem interval_ground_state_identity_EX040 (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hE : IntervalIntegrable (fun t => deriv g t ^ 2 * qAng h (t : AngCircle)) volume a b) :
    let w := liftGroundStateConj h g
    AbsolutelyContinuousOnInterval w a b ∧
      IntervalIntegrable (fun t => deriv w t ^ 2 + groundPot h t * w t ^ 2) volume a b ∧
      (∫ t in a..b, deriv g t ^ 2 * qAng h (t : AngCircle)) =
        (∫ t in a..b, deriv w t ^ 2 + groundPot h t * w t ^ 2) -
          (driftB h b * w b ^ 2 - driftB h a * w a ^ 2) / 2 := by
  intro w
  have hs : AbsolutelyContinuousOnInterval (sqrtQ h) a b := by
    have hs1 : ContDiff ℝ 1 (sqrtQ h) := (contDiff_sqrtQ h hh).of_le (by simp)
    exact hs1.contDiffOn.absolutelyContinuousOnInterval
  have hw : AbsolutelyContinuousOnInterval w a b := hg.fun_mul hs
  have hb : AbsolutelyContinuousOnInterval (driftB h) a b := by
    have hb1 : ContDiff ℝ 1 (driftB h) := (contDiff_driftB h hh).of_le (by simp)
    exact hb1.contDiffOn.absolutelyContinuousOnInterval
  let F : ℝ → ℝ := fun t => driftB h t * w t ^ 2 / 2
  have hF : AbsolutelyContinuousOnInterval F a b := by
    simpa [F, pow_two, div_eq_mul_inv, mul_comm (2 : ℝ)⁻¹] using
      (hb.fun_mul (hw.fun_mul hw)).const_mul (2 : ℝ)⁻¹
  have heq : ∀ᵐ t, t ∈ uIoc a b →
      deriv g t ^ 2 * qAng h (t : AngCircle) + deriv F t =
        deriv w t ^ 2 + groundPot h t * w t ^ 2 := by
    filter_upwards [hg.ae_differentiableAt] with t ht hmem
    have hp := pointwise_ground_state_EX040 h hh (ht (uIoc_subset_uIcc hmem))
    change deriv g t ^ 2 * qAng h (t : AngCircle) =
      deriv w t ^ 2 + groundPot h t * w t ^ 2 - deriv F t at hp
    linarith
  have hsum := (hE.add hF.intervalIntegrable_deriv).congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).2 heq)
  refine ⟨hw, hsum, ?_⟩
  have hi := intervalIntegral.integral_congr_ae heq
  rw [intervalIntegral.integral_add hE hF.intervalIntegrable_deriv,
    hF.integral_deriv_eq_sub] at hi
  dsimp [F] at hi
  linarith

/-- On the central interval the unrestricted endpoint traces give a nonnegative boundary term. -/
theorem central_ground_state_boundary_nonneg_EX040 (h : ℝ) (hh : 0 < h) (g : ℝ → ℝ) :
    0 ≤ -(driftB h (π / 2) * liftGroundStateConj h g (π / 2) ^ 2 -
      driftB h (-(π / 2)) * liftGroundStateConj h g (-(π / 2)) ^ 2) / 2 := by
  have hr := mul_nonpos_of_nonpos_of_nonneg (driftB_right h hh)
    (sq_nonneg (liftGroundStateConj h g (π / 2)))
  have hl := mul_nonneg (driftB_left h hh)
    (sq_nonneg (liftGroundStateConj h g (-(π / 2))))
  linarith

/-- The ground-state energy on the central interval is bounded by the original weighted
energy, for arbitrary absolutely continuous finite-energy tests. -/
theorem central_ground_state_energy_le_EX040 (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ}
    (hg : AbsolutelyContinuousOnInterval g (-(π / 2)) (π / 2))
    (hE : IntervalIntegrable (fun t => deriv g t ^ 2 * qAng h (t : AngCircle)) volume
      (-(π / 2)) (π / 2)) :
    (∫ t in -(π / 2)..π / 2,
      deriv (liftGroundStateConj h g) t ^ 2 + groundPot h t * liftGroundStateConj h g t ^ 2) ≤
      ∫ t in -(π / 2)..π / 2, deriv g t ^ 2 * qAng h (t : AngCircle) := by
  have hi := (interval_ground_state_identity_EX040 h hh hg hE).2.2
  have hb := central_ground_state_boundary_nonneg_EX040 h hh g
  linarith

end DGPS.Examples
