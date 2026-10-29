import LeanResearch.PeriodicAttractiveLogGas.RadialScaling
import LeanResearch.PeriodicAttractiveLogGas.RadialHarmonicReproduction
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-! The logarithmic part of source Lemma 2.2's radial regularization bound.

The exact circle average is obtained from the pinned Mathlib logarithmic
circle-average theorem, including its integrable singular-circle case. Polar
Fubini below is justified by applying the nonnegative polar formula to the
norm of an actually integrable function. Thus the continuous harmonic polar
lemma is not applied to the logarithmic singularity.

The final theorem uses the already constructed scaled radial probability
kernel, with its actual nonnegativity, mass, and compact support. No Green
regularization bound or logarithmic averaging inequality is assumed.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ContDiff Convolution ENNReal

namespace PeriodicAttractiveLogGas

/-- The logarithm is genuinely integrable on every circle, even when that
circle passes through its pole. This is the pinned Mathlib meromorphic-log
integrability theorem, with the source's negative-log normalization. -/
theorem circleIntegrable_neg_log_norm_const_sub (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z : ℂ ↦ -Real.log ‖c - z‖) 0 r := by
  have heq : (fun z : ℂ ↦ -Real.log ‖c - z‖) =
      (fun z : ℂ ↦ -Real.log ‖z - c‖) := by
    funext z
    rw [norm_sub_rev c z]
  rw [heq]
  exact (circleIntegrable_log_norm_sub_const (a := c) (c := 0) r).neg

/-- The exact logarithmic circle mean, including the boundary case in which
the singularity lies on the circle. -/
theorem circleAverage_log_norm_sub_const_eq_log_max (c : ℂ) (r : ℝ)
    (hr : 0 < r) :
    Real.circleAverage (fun z : ℂ ↦ Real.log ‖z - c‖) 0 r =
      Real.log (max ‖c‖ r) := by
  by_cases hcr : ‖c‖ ≤ r
  · rw [max_eq_right hcr]
    apply circleAverage_log_norm_sub_const_of_mem_closedBall
    simpa only [mem_closedBall, dist_zero_right, abs_of_pos hr] using hcr
  · have hrc : r < ‖c‖ := lt_of_not_ge hcr
    have hcn : ‖c‖ ≠ 0 := ne_of_gt (hr.trans hrc)
    have hratio : 1 ≤ |r⁻¹ * ‖c‖| := by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg c))]
      simpa only [inv_mul_cancel₀ hr.ne'] using
        mul_le_mul_of_nonneg_left hrc.le (inv_nonneg.mpr hr.le)
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne',
      zero_sub, norm_neg, Real.posLog_eq_log hratio,
      Real.log_mul (inv_ne_zero hr.ne') hcn, Real.log_inv, max_eq_left hrc.le]
    ring

/-- Conversion to the unnormalized angular integral used in planar polar
coordinates. Endpoints carry zero one-dimensional Lebesgue measure. -/
theorem integral_polar_circle_log_norm_sub_const (c : ℂ) (r : ℝ)
    (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      Real.log ‖Complex.polarCoord.symm (r, θ) - c‖) =
      (2 * Real.pi) * Real.log (max ‖c‖ r) := by
  have hpolar (θ : ℝ) :
      Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
    simp only [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin, zero_add]
  simp_rw [hpolar]
  have hp : (fun θ ↦ Real.log ‖circleMap 0 r θ - c‖).Periodic (2 * Real.pi) :=
    fun θ ↦ congrArg (fun z : ℂ ↦ Real.log ‖z - c‖) (periodic_circleMap 0 r θ)
  have hangle : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hshift : (∫ θ in -Real.pi..Real.pi, Real.log ‖circleMap 0 r θ - c‖) =
      ∫ θ in 0..2 * Real.pi, Real.log ‖circleMap 0 r θ - c‖ := by
    simpa only [hangle, zero_add] using hp.intervalIntegral_add_eq (-Real.pi) 0
  have hmean := circleAverage_log_norm_sub_const_eq_log_max c r hr
  rw [Real.circleAverage_def, smul_eq_mul] at hmean
  have hfull : (∫ θ in 0..2 * Real.pi, Real.log ‖circleMap 0 r θ - c‖) =
      (2 * Real.pi) * Real.log (max ‖c‖ r) := by
    simpa only [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),
      one_mul] using congrArg (fun a : ℝ ↦ (2 * Real.pi) * a) hmean
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    hshift, hfull]

/-- The manuscript's exact circular-mean identity for the negative logarithm. -/
theorem integral_polar_circle_neg_log_norm_const_sub (c : ℂ) (r : ℝ)
    (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      -Real.log ‖c - Complex.polarCoord.symm (r, θ)‖) =
      (2 * Real.pi) * (-Real.log (max ‖c‖ r)) := by
  simp_rw [norm_sub_rev c]
  rw [integral_neg, integral_polar_circle_log_norm_sub_const c r hr]
  ring

/-- Measurable integrable functions admit actual polar integrability. The
proof uses the nonnegative change of variables on the norm, rather than a
continuity assumption that would fail at a logarithmic pole. -/
theorem integrableOn_complex_polar_of_integrable {q : ℂ → ℝ}
    (hq : Measurable q) (hi : Integrable q volume) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * q (Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) volume := by
  refine ⟨(measurable_fst.mul
    (hq.comp continuous_complex_polar_symm.measurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ‖p.1 * q (Complex.polarCoord.symm p)‖) =
        ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * ENNReal.ofReal ‖q (Complex.polarCoord.symm p)‖ := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      change ENNReal.ofReal ‖p.1 * q (Complex.polarCoord.symm p)‖ =
        ENNReal.ofReal p.1 * ENNReal.ofReal ‖q (Complex.polarCoord.symm p)‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hp.1,
        ENNReal.ofReal_mul hp.1.le]
    _ = ∫⁻ z : ℂ, ENNReal.ofReal ‖q z‖ := by
      simpa only [smul_eq_mul, polarCoord] using
        Complex.lintegral_comp_polarCoord_symm (fun z : ℂ ↦ ENNReal.ofReal ‖q z‖)
    _ < (⊤ : ℝ≥0∞) := (hasFiniteIntegral_iff_norm q).1 hi.hasFiniteIntegral

/-- Fubini for the actual polar integrand, with integrability on the product
of the restricted radial and angular Lebesgue measures. -/
theorem integral_complex_eq_polar_iterated_of_integrable {q : ℂ → ℝ}
    (hq : Measurable q) (hi : Integrable q volume) :
    (∫ z, q z) = ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
      r * q (Complex.polarCoord.symm (r, θ)) := by
  rw [← Complex.integral_comp_polarCoord_symm q]
  simp only [smul_eq_mul]
  exact setIntegral_prod _ (integrableOn_complex_polar_of_integrable hq hi)

/-- The outer integral in the preceding Fubini formula is integrable. This
permits a real integral inequality even though the logarithm changes sign. -/
theorem integrableOn_complex_polar_iterated_of_integrable {q : ℂ → ℝ}
    (hq : Measurable q) (hi : Integrable q volume) :
    IntegrableOn (fun r : ℝ ↦ ∫ θ in Ioo (-Real.pi) Real.pi,
      r * q (Complex.polarCoord.symm (r, θ))) (Ioi (0 : ℝ)) volume := by
  have hp := integrableOn_complex_polar_of_integrable hq hi
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  exact hp.integral_prod_left

/-- A nonnegative radial density cannot increase the negative logarithm.
The total mass is explicit, and both singular and constant comparison
integrands have actual integrability hypotheses. -/
theorem integral_complex_radial_mul_neg_log_le {κ : ℂ → ℝ} {c : ℂ}
    (hκ : Measurable κ) (hκi : Integrable κ volume)
    (hκnonneg : ∀ z, 0 ≤ κ z)
    (hκrad : ∀ {z w : ℂ}, ‖z‖ = ‖w‖ → κ z = κ w)
    (hc : c ≠ 0)
    (hqi : Integrable (fun z : ℂ ↦ κ z * (-Real.log ‖c - z‖)) volume) :
    (∫ z : ℂ, κ z * (-Real.log ‖c - z‖)) ≤
      (∫ z : ℂ, κ z) * (-Real.log ‖c‖) := by
  have hq : Measurable (fun z : ℂ ↦ κ z * (-Real.log ‖c - z‖)) :=
    hκ.mul ((measurable_const.sub measurable_id).norm.log.neg)
  have hqconst : Measurable (fun z : ℂ ↦ κ z * (-Real.log ‖c‖)) :=
    hκ.mul measurable_const
  have hqconsti : Integrable (fun z : ℂ ↦ κ z * (-Real.log ‖c‖)) volume :=
    hκi.mul_const _
  have hinner : ∀ r ∈ Ioi (0 : ℝ),
      (∫ θ in Ioo (-Real.pi) Real.pi,
        r * (κ (Complex.polarCoord.symm (r, θ)) *
          (-Real.log ‖c - Complex.polarCoord.symm (r, θ)‖))) ≤
      ∫ θ in Ioo (-Real.pi) Real.pi,
        r * (κ (Complex.polarCoord.symm (r, θ)) * (-Real.log ‖c‖)) := by
    intro r hr
    have hrpos : 0 < r := hr
    have hκr (θ : ℝ) : κ (Complex.polarCoord.symm (r, θ)) = κ (r : ℂ) :=
      hκrad (by simp only [Complex.norm_polarCoord_symm, Complex.norm_real, Real.norm_eq_abs])
    have hleft : (∫ θ in Ioo (-Real.pi) Real.pi,
        r * (κ (Complex.polarCoord.symm (r, θ)) *
          (-Real.log ‖c - Complex.polarCoord.symm (r, θ)‖))) =
        (r * κ (r : ℂ) * (2 * Real.pi)) * (-Real.log (max ‖c‖ r)) := by
      simp_rw [hκr, ← mul_assoc]
      rw [integral_const_mul, integral_polar_circle_neg_log_norm_const_sub c r hrpos]
      ring
    have hright : (∫ θ in Ioo (-Real.pi) Real.pi,
        r * (κ (Complex.polarCoord.symm (r, θ)) * (-Real.log ‖c‖))) =
        (r * κ (r : ℂ) * (2 * Real.pi)) * (-Real.log ‖c‖) := by
      simp_rw [hκr]
      rw [integral_Ioo_neg_pi_pi_const]
      ring
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left
      (neg_le_neg (Real.log_le_log (norm_pos_iff.mpr hc) (le_max_left _ _)))
      (mul_nonneg (mul_nonneg hrpos.le (hκnonneg _))
        (mul_nonneg (by norm_num) Real.pi_pos.le))
  calc
    (∫ z : ℂ, κ z * (-Real.log ‖c - z‖)) =
        ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
          r * (κ (Complex.polarCoord.symm (r, θ)) *
            (-Real.log ‖c - Complex.polarCoord.symm (r, θ)‖)) :=
      integral_complex_eq_polar_iterated_of_integrable hq hqi
    _ ≤ ∫ r in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
          r * (κ (Complex.polarCoord.symm (r, θ)) * (-Real.log ‖c‖)) :=
      setIntegral_mono_on
        (integrableOn_complex_polar_iterated_of_integrable hq hqi)
        (integrableOn_complex_polar_iterated_of_integrable hqconst hqconsti)
        measurableSet_Ioi hinner
    _ = ∫ z : ℂ, κ z * (-Real.log ‖c‖) :=
      (integral_complex_eq_polar_iterated_of_integrable hqconst hqconsti).symm
    _ = (∫ z : ℂ, κ z) * (-Real.log ‖c‖) := integral_mul_const _ _

/-- Actual integrability of the singular logarithmic convolution, at every
evaluation point including the origin. -/
theorem integrable_scaledRadialMollifier_mul_planarLogKernel
    (ε : ℝ) (hε : 0 < ε) (x : PlanarSpace) :
    Integrable (fun y : PlanarSpace ↦
      scaledRadialMollifier ε y * planarLogKernel (x - y)) volume := by
  have hi := ((hasCompactSupport_scaledRadialMollifier ε hε).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) locallyIntegrable_planarLogKernel
    (contDiff_scaledRadialMollifier ε).continuous x).integrable_swap
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hi

/-- Radial regularization does not increase the actual planar negative
logarithm away from its pole. The scale has no upper restriction. -/
theorem integral_scaledRadialMollifier_mul_planarLogKernel_le
    (ε : ℝ) (hε : 0 < ε) {x : PlanarSpace} (hx : x ≠ 0) :
    (∫ y : PlanarSpace, scaledRadialMollifier ε y * planarLogKernel (x - y)) ≤
      planarLogKernel x := by
  let l : ℂ ≃ₗᵢ[ℝ] PlanarSpace := Complex.orthonormalBasisOneI.repr
  let c : ℂ := l.symm x
  let κ : ℂ → ℝ := fun z ↦ scaledRadialMollifier ε (l z)
  have hc : c ≠ 0 := by
    intro h
    apply hx
    have h' := congrArg l h
    simpa only [c, l.apply_symm_apply, map_zero] using h'
  have hκ : Measurable κ :=
    (contDiff_scaledRadialMollifier ε).continuous.measurable.comp l.continuous.measurable
  have hκi : Integrable κ volume :=
    l.measurePreserving.integrable_comp_of_integrable
      (integrable_scaledRadialMollifier ε hε)
  have hκnonneg : ∀ z : ℂ, 0 ≤ κ z :=
    fun z ↦ scaledRadialMollifier_nonneg ε (l z)
  have hκrad : ∀ {z w : ℂ}, ‖z‖ = ‖w‖ → κ z = κ w := by
    intro z w hzw
    exact scaledRadialMollifier_eq_of_norm_eq ε (by simpa only [l.norm_map] using hzw)
  have hlog (z : ℂ) : planarLogKernel (x - l z) = -Real.log ‖c - z‖ := by
    have hsub : x - l z = l (c - z) := by simp only [map_sub, c, l.apply_symm_apply]
    rw [planarLogKernel, hsub, l.norm_map]
  have hqi : Integrable (fun z : ℂ ↦ κ z * (-Real.log ‖c - z‖)) volume := by
    have hi := l.measurePreserving.integrable_comp_of_integrable
      (integrable_scaledRadialMollifier_mul_planarLogKernel ε hε x)
    change Integrable (fun z : ℂ ↦ scaledRadialMollifier ε (l z) *
      planarLogKernel (x - l z)) volume at hi
    simpa only [hlog, κ] using hi
  have hmass : (∫ z : ℂ, κ z) = 1 := by
    change (∫ z : ℂ, scaledRadialMollifier ε (l z)) = 1
    rw [l.measurePreserving.integral_comp l.toHomeomorph.measurableEmbedding]
    exact integral_scaledRadialMollifier ε hε
  have hnormc : ‖c‖ = ‖x‖ := l.symm.norm_map x
  have hchange := l.measurePreserving.integral_comp l.toHomeomorph.measurableEmbedding
    (fun y : PlanarSpace ↦ scaledRadialMollifier ε y * planarLogKernel (x - y))
  calc
    (∫ y : PlanarSpace, scaledRadialMollifier ε y * planarLogKernel (x - y)) =
        ∫ z : ℂ, κ z * (-Real.log ‖c - z‖) := by
      rw [← hchange]
      simp only [hlog, κ]
    _ ≤ (∫ z : ℂ, κ z) * (-Real.log ‖c‖) :=
      integral_complex_radial_mul_neg_log_le hκ hκi hκnonneg hκrad hc hqi
    _ = planarLogKernel x := by
      rw [hmass, one_mul, hnormc]
      rfl

end PeriodicAttractiveLogGas
