import DGPS.Examples.EngineeredRankOneDrift
import DGPS.Circle.StationaryFlux

open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open DGPS.Circle.AngularNormalization


/-!
# Periodic and interval ground-state conjugation (EX038)

For the engineered reference density `q_h = qAng h` (EX030), let `b = driftB h = (log q_h)'`
and `Vcal = groundPot h = b² / 4 + b' / 2` (EX037). For smooth `g` and `w = g √q_h`:

* the pointwise identity `g'² q_h = w'² + Vcal w² - (b w² / 2)'` (since `(√q_h)' = (b / 2) √q_h`);
* on the full angular circle, periodicity kills the boundary, so
  `∫ g'² dμ_h = ∫ (w'² + Vcal w²) dm` with `μ_h = q_h m` and `m` the normalized angular Haar
  measure;
* on `J₀ = [-π/2, π/2]` (lifted angle), the identity has the boundary contribution
  `B = -[b w²]_{-π/2}^{π/2} / (4π)` under `dt / (2π)`, and `B ≥ 0` since
  `b(π/2) = -(h + R_h'(1)) ≤ 0 ≤ b(-π/2)`.

All statements are proved for every `h > 0` (the uniform estimates of EX037 are not needed for
the identity itself, only the formula `b = -(h + R_h'(U)) sin` and `R_h' ≥ 0`).
Main output: `DGPS.Examples.periodic_and_interval_ground_state_conjugation`.
-/

namespace DGPS.Examples.EngineeredGroundState

open DGPS.Examples.EngineeredRankOne DGPS.Circle.StationaryFlux

/-- `log q_h` on the lifted angle. -/
noncomputable def Lh (h t : ℝ) : ℝ := logq h (t : Real.Angle)

/-- `√q_h` on the lifted angle. -/
noncomputable def sqrtQ (h t : ℝ) : ℝ := Real.sqrt (qAng h (t : Real.Angle))

theorem Lh_eq (h t : ℝ) : Lh h t = -(h * (1 - Real.cos t)) - corr h (1 - Real.cos t) := by
  unfold Lh logq; rw [drift_Uang]

theorem contDiff_Lh (h : ℝ) (hh : 0 < h) : ContDiff ℝ ∞ (Lh h) := by
  have e : Lh h = fun t => -(h * (1 - Real.cos t)) - corr h (1 - Real.cos t) := funext (Lh_eq h)
  rw [e]
  have hc : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.cos t) := contDiff_const.sub Real.contDiff_cos
  exact (contDiff_const.mul hc).neg.sub ((contDiff_corr h hh).comp hc)

theorem hasDerivAt_Lh (h : ℝ) (hh : 0 < h) (t : ℝ) : HasDerivAt (Lh h) (driftB h t) t :=
  (((contDiff_Lh h hh).differentiable (by simp)) t).hasDerivAt

theorem contDiff_driftB (h : ℝ) (hh : 0 < h) : ContDiff ℝ ∞ (driftB h) := by
  have e : driftB h = fun s => -(h + integrand h (1 - Real.cos s)) * Real.sin s :=
    funext (driftB_eq h hh)
  rw [e]
  have hc : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.cos t) := contDiff_const.sub Real.contDiff_cos
  exact (contDiff_const.add ((contDiff_integrand h hh).comp hc)).neg.mul Real.contDiff_sin

theorem qAng_lift (h t : ℝ) : qAng h (t : Real.Angle) = (Zh h)⁻¹ * exp (Lh h t) := rfl

theorem sqrtQ_eq (h : ℝ) (hh : 0 < h) (t : ℝ) :
    sqrtQ h t = Real.sqrt (Zh h)⁻¹ * exp (Lh h t / 2) := by
  unfold sqrtQ
  rw [qAng_lift, Real.sqrt_mul (inv_pos.2 (Zh_pos h hh)).le, Real.exp_half]

theorem sqrtQ_pos (h : ℝ) (hh : 0 < h) (t : ℝ) : 0 < sqrtQ h t := by
  rw [sqrtQ_eq h hh]
  exact mul_pos (Real.sqrt_pos.2 (inv_pos.2 (Zh_pos h hh))) (exp_pos _)

theorem sqrtQ_sqrtQ (h : ℝ) (hh : 0 < h) (t : ℝ) : sqrtQ h t ^ 2 = qAng h (t : Real.Angle) := by
  unfold sqrtQ
  exact Real.sq_sqrt (qAng_pos h hh _).le

theorem contDiff_sqrtQ (h : ℝ) (hh : 0 < h) : ContDiff ℝ ∞ (sqrtQ h) := by
  have e : sqrtQ h = fun t => Real.sqrt (Zh h)⁻¹ * exp (Lh h t / 2) := funext (sqrtQ_eq h hh)
  rw [e]
  exact contDiff_const.mul (Real.contDiff_exp.comp ((contDiff_Lh h hh).div_const 2))

theorem hasDerivAt_sqrtQ (h : ℝ) (hh : 0 < h) (t : ℝ) :
    HasDerivAt (sqrtQ h) (driftB h t / 2 * sqrtQ h t) t := by
  have e : sqrtQ h = fun t => Real.sqrt (Zh h)⁻¹ * exp (Lh h t / 2) := funext (sqrtQ_eq h hh)
  rw [e]
  have h1 : HasDerivAt (fun t => Lh h t / 2) (driftB h t / 2) t :=
    (hasDerivAt_Lh h hh t).div_const 2
  have h2 := (h1.exp).const_mul (Real.sqrt (Zh h)⁻¹)
  convert h2 using 1
  ring

/-- the pointwise ground-state identity -/
theorem pointwise (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    let w : ℝ → ℝ := fun t => g t * sqrtQ h t
    HasDerivAt (fun t => driftB h t * w t ^ 2 / 2)
        (deriv (driftB h) t * w t ^ 2 / 2 + driftB h t * w t * deriv w t) t ∧
      deriv g t ^ 2 * qAng h (t : Real.Angle) =
        deriv w t ^ 2 + groundPot h t * w t ^ 2 -
          (deriv (driftB h) t * w t ^ 2 / 2 + driftB h t * w t * deriv w t) := by
  intro w
  have hgd : HasDerivAt g (deriv g t) t := ((hg.differentiable (by simp)) t).hasDerivAt
  have hw : HasDerivAt w (deriv g t * sqrtQ h t + g t * (driftB h t / 2 * sqrtQ h t)) t :=
    hgd.mul (hasDerivAt_sqrtQ h hh t)
  have hwd : deriv w t = deriv g t * sqrtQ h t + g t * (driftB h t / 2 * sqrtQ h t) := hw.deriv
  have hbd : HasDerivAt (driftB h) (deriv (driftB h) t) t :=
    (((contDiff_driftB h hh).differentiable (by simp)) t).hasDerivAt
  constructor
  · have h1 : HasDerivAt (fun t => w t ^ 2) (2 * w t * deriv w t) t := by
      have := hw.mul hw
      rw [← hwd] at this
      convert this using 1
      · funext x; simp [pow_two]
      · ring
    have h2 := (hbd.mul h1).div_const 2
    convert h2 using 1
    ring
  · rw [← sqrtQ_sqrtQ h hh t, hwd]
    unfold groundPot
    simp only [w]
    ring


theorem continuous_groundPot (h : ℝ) (hh : 0 < h) : Continuous (groundPot h) := by
  have hb := contDiff_driftB h hh
  have hd : Continuous (deriv (driftB h)) := hb.continuous_deriv (by simp)
  unfold groundPot
  exact (hb.continuous.pow 2).div_const 4 |>.add (hd.div_const 2)

/-- the integrated ground-state identity on any lifted interval `[a, b]`. -/
theorem interval_identity (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (a b : ℝ) :
    let w : ℝ → ℝ := fun t => g t * sqrtQ h t
    ∫ t in a..b, deriv g t ^ 2 * qAng h (t : Real.Angle) =
      (∫ t in a..b, (deriv w t ^ 2 + groundPot h t * w t ^ 2)) -
        (driftB h b * w b ^ 2 / 2 - driftB h a * w a ^ 2 / 2) := by
  intro w
  have hw : ContDiff ℝ ∞ w := hg.mul (contDiff_sqrtQ h hh)
  have hwc : Continuous w := hw.continuous
  have hdw : Continuous (deriv w) := hw.continuous_deriv (by simp)
  have hdg : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hb := contDiff_driftB h hh
  have hdb : Continuous (deriv (driftB h)) := hb.continuous_deriv (by simp)
  have hq : Continuous (fun t : ℝ => qAng h (t : Real.Angle)) := by
    have e : (fun t : ℝ => qAng h (t : Real.Angle)) = fun t => sqrtQ h t ^ 2 :=
      funext fun t => (sqrtQ_sqrtQ h hh t).symm
    rw [e]; exact (contDiff_sqrtQ h hh).continuous.pow 2
  have hF : Continuous (fun t => deriv w t ^ 2 + groundPot h t * w t ^ 2) :=
    (hdw.pow 2).add ((continuous_groundPot h hh).mul (hwc.pow 2))
  have hΦ : Continuous (fun t => deriv (driftB h) t * w t ^ 2 / 2 + driftB h t * w t * deriv w t) :=
    ((hdb.mul (hwc.pow 2)).div_const 2).add ((hb.continuous.mul hwc).mul hdw)
  have e1 : (fun t : ℝ => deriv g t ^ 2 * qAng h (t : Real.Angle)) = fun t =>
      (deriv w t ^ 2 + groundPot h t * w t ^ 2) -
        (deriv (driftB h) t * w t ^ 2 / 2 + driftB h t * w t * deriv w t) :=
    funext fun t => (pointwise h hh hg t).2
  have e2 : ∫ t in a..b, (deriv (driftB h) t * w t ^ 2 / 2 + driftB h t * w t * deriv w t) =
      driftB h b * w b ^ 2 / 2 - driftB h a * w a ^ 2 / 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => (pointwise h hh hg t).1)
      (hΦ.intervalIntegrable a b)
  rw [e1, intervalIntegral.integral_sub (hF.intervalIntegrable a b) (hΦ.intervalIntegrable a b), e2]


theorem driftB_periodic (h : ℝ) (hh : 0 < h) : Function.Periodic (driftB h) (2 * π) := fun t => by
  rw [driftB_eq h hh, driftB_eq h hh, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem groundPot_periodic (h : ℝ) (hh : 0 < h) : Function.Periodic (groundPot h) (2 * π) :=
  fun t => by
    unfold groundPot
    rw [driftB_periodic h hh t, periodic_deriv (driftB_periodic h hh) t]

theorem exists_angSec_eq (x : ℝ) : ∃ n : ℤ, angSec (x : AngCircle) = x + n * (2 * π) := by
  have h : (((angSec (x : AngCircle) : ℝ) - x : ℝ) : AngCircle) = 0 := by
    rw [AddCircle.coe_sub, coe_angSec, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [zsmul_eq_mul] at hn; linarith⟩

theorem groundPot_angSec (h : ℝ) (hh : 0 < h) (x : ℝ) :
    groundPot h (angSec (x : AngCircle)) = groundPot h x := by
  obtain ⟨n, hn⟩ := exists_angSec_eq x
  rw [hn]
  exact (groundPot_periodic h hh).int_mul n x

theorem integral_angHaar_eq (φ : AngCircle → ℝ) :
    ∫ θ, φ θ ∂angHaar = (2 * π)⁻¹ * ∫ x in (0 : ℝ)..2 * π, lift φ x := by
  rw [integral_lift_period]
  field_simp

theorem continuous_qAng (h : ℝ) (hh : 0 < h) : Continuous (qAng h) := by
  unfold qAng
  exact continuous_const.mul (continuous_exp.comp (continuous_logq h hh))

/-- The engineered reference measure `μ_h = q_h m` on the angular circle (EX030, before the
identification `angEquiv` with the unit-period torus). -/
noncomputable def circleReference (h : ℝ) : Measure AngCircle :=
  angHaar.withDensity fun θ => ENNReal.ofReal (qAng h θ)

/-- The ground-state conjugate `w = g √q_h` of `g` on the angular circle. -/
noncomputable def groundStateConj (h : ℝ) (g : AngCircle → ℝ) : AngCircle → ℝ :=
  fun θ => g θ * Real.sqrt (qAng h θ)

/-- The ground-state conjugate `w = g √q_h` of a function `g` on the lifted angle. -/
noncomputable def liftGroundStateConj (h : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun t => g t * Real.sqrt (qAng h (t : AngCircle))

theorem integral_circleReference (h : ℝ) (hh : 0 < h) (F : AngCircle → ℝ) :
    ∫ θ, F θ ∂(circleReference h) = ∫ θ, F θ * qAng h θ ∂angHaar := by
  unfold circleReference
  rw [integral_withDensity_eq_integral_toReal_smul
    (((continuous_qAng h hh).measurable).ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (qAng_pos h hh θ).le, mul_comm]

theorem periodic_part (h : ℝ) (hh : 0 < h) {g : AngCircle → ℝ} (hg : IsSmoothAngular g) :
    IsSmoothAngular (groundStateConj h g) ∧
      ∫ θ, angDeriv g θ ^ 2 ∂(circleReference h) =
        ∫ θ, (angDeriv (groundStateConj h g) θ ^ 2 +
          groundPot h (angSec θ) * groundStateConj h g θ ^ 2) ∂angHaar := by
  have hlw : lift (groundStateConj h g) = fun t => lift g t * sqrtQ h t := rfl
  have hsm : IsSmoothAngular (groundStateConj h g) := by
    rw [isSmooth_iff, hlw]; exact hg.mul (contDiff_sqrtQ h hh)
  refine ⟨hsm, ?_⟩
  rw [integral_circleReference h hh, integral_angHaar_eq, integral_angHaar_eq]
  congr 1
  have hg' : ContDiff ℝ ∞ (lift g) := hg
  have key := interval_identity h hh hg' 0 (2 * π)
  have e1 : (fun x => lift (fun θ => angDeriv g θ ^ 2 * qAng h θ) x) =
      fun x => deriv (lift g) x ^ 2 * qAng h (x : Real.Angle) := by
    funext x
    show angDeriv g (x : AngCircle) ^ 2 * qAng h (x : AngCircle) = _
    rw [angDeriv_coe]
    rfl
  have e2 : (fun x => lift (fun θ => angDeriv (groundStateConj h g) θ ^ 2 +
        groundPot h (angSec θ) * groundStateConj h g θ ^ 2) x) =
      fun x => deriv (fun t => lift g t * sqrtQ h t) x ^ 2 +
        groundPot h x * (lift g x * sqrtQ h x) ^ 2 := by
    funext x
    show angDeriv (groundStateConj h g) (x : AngCircle) ^ 2 +
      groundPot h (angSec (x : AngCircle)) * groundStateConj h g (x : AngCircle) ^ 2 = _
    rw [angDeriv_coe, groundPot_angSec h hh, hlw]
    rfl
  rw [e1, e2]
  have hper : driftB h (2 * π) * (lift g (2 * π) * sqrtQ h (2 * π)) ^ 2 / 2 -
      driftB h 0 * (lift g 0 * sqrtQ h 0) ^ 2 / 2 = 0 := by
    have a1 : driftB h (2 * π) = driftB h 0 := by
      simpa using driftB_periodic h hh 0
    have a2 : lift g (2 * π) = lift g 0 := by simpa using lift_periodic g 0
    have a3 : sqrtQ h (2 * π) = sqrtQ h 0 := by simp [sqrtQ]
    rw [a1, a2, a3]; ring
  simp only at key
  rw [key, hper, sub_zero]


theorem driftB_right (h : ℝ) (hh : 0 < h) : driftB h (π / 2) ≤ 0 := by
  rw [driftB_eq h hh, Real.sin_pi_div_two, Real.cos_pi_div_two]
  have : 0 ≤ integrand h (1 - 0) := integrand_nonneg h hh ⟨by norm_num, by norm_num⟩
  linarith

theorem driftB_left (h : ℝ) (hh : 0 < h) : 0 ≤ driftB h (-(π / 2)) := by
  rw [driftB_eq h hh, Real.sin_neg, Real.sin_pi_div_two, Real.cos_neg, Real.cos_pi_div_two]
  have : 0 ≤ integrand h (1 - 0) := integrand_nonneg h hh ⟨by norm_num, by norm_num⟩
  linarith

theorem interval_part (h : ℝ) (hh : 0 < h) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    (2 * π)⁻¹ * ∫ t in -(π / 2)..π / 2, deriv g t ^ 2 * qAng h (t : AngCircle) =
        (2 * π)⁻¹ * (∫ t in -(π / 2)..π / 2, (deriv (liftGroundStateConj h g) t ^ 2 +
          groundPot h t * liftGroundStateConj h g t ^ 2)) +
        -(driftB h (π / 2) * liftGroundStateConj h g (π / 2) ^ 2 -
          driftB h (-(π / 2)) * liftGroundStateConj h g (-(π / 2)) ^ 2) / (4 * π) ∧
      0 ≤ -(driftB h (π / 2) * liftGroundStateConj h g (π / 2) ^ 2 -
          driftB h (-(π / 2)) * liftGroundStateConj h g (-(π / 2)) ^ 2) / (4 * π) := by
  have key := interval_identity h hh hg (-(π / 2)) (π / 2)
  have hw : liftGroundStateConj h g = fun t => g t * sqrtQ h t := rfl
  have hp := Real.pi_pos
  constructor
  · rw [hw]
    simp only at key
    have key2 : (∫ t in -(π / 2)..π / 2, deriv g t ^ 2 * qAng h (t : AngCircle)) = _ := key
    rw [key2]
    field_simp
    ring
  · have h1 := driftB_right h hh
    have h2 := driftB_left h hh
    have h3 : 0 ≤ liftGroundStateConj h g (π / 2) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ liftGroundStateConj h g (-(π / 2)) ^ 2 := sq_nonneg _
    have : driftB h (π / 2) * liftGroundStateConj h g (π / 2) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h1 h3
    have : 0 ≤ driftB h (-(π / 2)) * liftGroundStateConj h g (-(π / 2)) ^ 2 :=
      mul_nonneg h2 h4
    apply div_nonneg _ (by positivity)
    linarith

end DGPS.Examples.EngineeredGroundState

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredGroundState
  DGPS.Circle.AngularNormalization

/-- EX038: ground-state conjugation `w = g √q_h`, `b = (log q_h)'`, `Vcal = b²/4 + b'/2`.

* Full circle: for smooth `g`, `w` is smooth and `∫ (g')² dμ_h = ∫ (w'² + Vcal w²) dm`, where
  `μ_h = q_h m` and `m = angHaar` is normalized angular Haar measure.
* Interval `J₀ = [-π/2, π/2]` (lifted angle, `g` smooth on `ℝ`): under the normalized measure
  `dt/(2π)`, `∫_{J₀} (g')² q_h dm = ∫_{J₀} (w'² + Vcal w²) dm + B` with boundary contribution
  `B = -[b w²]_{-π/2}^{π/2}/(4π)`, and `B ≥ 0` because `b(π/2) ≤ 0 ≤ b(-π/2)`. -/
theorem periodic_and_interval_ground_state_conjugation (h : ℝ) (hh : 0 < h) :
    (∀ g : AngCircle → ℝ, IsSmoothAngular g →
      IsSmoothAngular (groundStateConj h g) ∧
        ∫ θ, angDeriv g θ ^ 2 ∂(circleReference h) =
          ∫ θ, (angDeriv (groundStateConj h g) θ ^ 2 +
            groundPot h (angSec θ) * groundStateConj h g θ ^ 2) ∂angHaar) ∧
    (driftB h (π / 2) ≤ 0 ∧ 0 ≤ driftB h (-(π / 2)) ∧
      ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
        (2 * π)⁻¹ * ∫ t in -(π / 2)..π / 2, deriv g t ^ 2 * qAng h (t : AngCircle) =
          (2 * π)⁻¹ * (∫ t in -(π / 2)..π / 2, (deriv (liftGroundStateConj h g) t ^ 2 +
            groundPot h t * liftGroundStateConj h g t ^ 2)) +
          -(driftB h (π / 2) * liftGroundStateConj h g (π / 2) ^ 2 -
            driftB h (-(π / 2)) * liftGroundStateConj h g (-(π / 2)) ^ 2) / (4 * π) ∧
        0 ≤ -(driftB h (π / 2) * liftGroundStateConj h g (π / 2) ^ 2 -
            driftB h (-(π / 2)) * liftGroundStateConj h g (-(π / 2)) ^ 2) / (4 * π)) :=
  ⟨fun _ hg => periodic_part h hh hg, driftB_right h hh, driftB_left h hh,
    fun _ hg => interval_part h hh hg⟩

end DGPS.Examples
