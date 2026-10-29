import LeanResearch.PeriodicAttractiveLogGas.GreenConvolution
import LeanResearch.PeriodicAttractiveLogGas.LogMollifierUpper
import LeanResearch.PeriodicAttractiveLogGas.RadialMollifierMoments
import Mathlib.Topology.TietzeExtension

/-! The local one-sided Green regularization bound in source Lemma 2.2.
The harmonic remainder is extended continuously only to make all global
integrals literal; the extension agrees with the actual remainder on the
closed quarter ball and remains harmonic in its interior. The logarithmic
convolution is separately integrable, including across the pole. -/

noncomputable section
open MeasureTheory Set Metric InnerProductSpace Filter
open scoped Topology Convolution

namespace PeriodicAttractiveLogGas

theorem exists_continuous_greenRemainder_extension :
    ∃ H : PlanarSpace → ℝ, Continuous H ∧
      EqOn H smoothGreenLogRemainder (closedBall (0 : PlanarSpace) (1 / 4 : ℝ)) ∧
      HarmonicOnNhd H (ball (0 : PlanarSpace) (1 / 4 : ℝ)) := by
  let K := closedBall (0 : PlanarSpace) (1 / 4 : ℝ)
  have hc : ContinuousOn smoothGreenLogRemainder K :=
    contDiffOn_smoothGreenLogRemainder.continuousOn.mono
      closedBall_quarter_subset_centeredOpenBox
  let f : C(K, ℝ) := ⟨fun x ↦ smoothGreenLogRemainder x, hc.domRestrict⟩
  obtain ⟨H, hH⟩ := f.exists_restrict_eq isClosed_closedBall
  have heq : EqOn H smoothGreenLogRemainder K := by
    intro x hx
    exact congrArg (fun g : C(K, ℝ) ↦ g ⟨x, hx⟩) hH
  refine ⟨H, H.continuous, heq, ?_⟩
  intro x hx
  have hlocal : smoothGreenLogRemainder =ᶠ[𝓝 x] H := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (heq (ball_subset_closedBall hy)).symm
  exact (harmonicAt_congr_nhds hlocal).mp
    (harmonicOnNhd_smoothGreenLogRemainder x
      (closedBall_quarter_subset_centeredOpenBox (ball_subset_closedBall hx)))

theorem regularizedGreen_local_upper (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) {x : PlanarSpace}
    (hx : ‖x‖ ≤ (1 / 8 : ℝ)) (hne : x ≠ 0) :
    regularizedGreen ε hε (torusQuotient x) ≤
      regularGreenRepresentative (torusQuotient x) + (Real.pi / 2) * ε ^ 2 := by
  obtain ⟨H, hHcont, hHeq, hHharm⟩ := exists_continuous_greenRemainder_extension
  have hxquarter : x ∈ closedBall (0 : PlanarSpace) (1 / 4 : ℝ) :=
    mem_closedBall_zero_iff.mpr (by linarith)
  have hHlocal : HarmonicOnNhd H (closedBall x ε) := by
    intro z hz
    apply hHharm
    rw [mem_ball_zero_iff]
    have hd : ‖z - x‖ ≤ ε := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have ht : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - x) x
    linarith
  have hL := integrable_scaledRadialMollifier_mul_planarLogKernel ε hε x
  have hQ : Integrable (fun y ↦ scaledRadialMollifier ε y * planarGreenQuadratic (x - y)) volume :=
    integrable_scaledRadialMollifier_mul_continuous ε hε
      (contDiff_planarGreenQuadratic.continuous.comp (continuous_const.sub continuous_id))
  have hH : Integrable (fun y ↦ scaledRadialMollifier ε y * H (x - y)) volume :=
    integrable_scaledRadialMollifier_mul_continuous ε hε
      (hHcont.comp (continuous_const.sub continuous_id))
  have hLQ : Integrable (fun y ↦ scaledRadialMollifier ε y * planarLogKernel (x - y) +
      scaledRadialMollifier ε y * planarGreenQuadratic (x - y)) volume := hL.add hQ
  have heq : (fun y ↦ regularGreenLift (x - y) * scaledRadialMollifier ε y) =ᵐ[volume]
      (fun y ↦ scaledRadialMollifier ε y * planarLogKernel (x - y) +
        scaledRadialMollifier ε y * planarGreenQuadratic (x - y) +
        scaledRadialMollifier ε y * H (x - y)) := by
    filter_upwards [volume.ae_ne x] with y hy
    by_cases hzero : scaledRadialMollifier ε y = 0
    · simp only [hzero, mul_zero, zero_mul, add_zero]
    · have hybound := mem_ball_zero_iff.mp (support_scaledRadialMollifier_subset ε hε hzero)
      have hnorm : ‖x - y‖ < (1 / 4 : ℝ) := by
        have ht := norm_sub_le x y
        linarith
      have hmem : x - y ∈ closedBall (0 : PlanarSpace) (1 / 4 : ℝ) :=
        mem_closedBall_zero_iff.mpr hnorm.le
      have hxyne : x - y ≠ 0 := sub_ne_zero.mpr hy.symm
      have hexp := regularGreenRepresentative_local_expansion
        (closedBall_quarter_subset_centeredOpenBox hmem) hxyne
      rw [regularGreenRepresentative_lift] at hexp
      rw [hexp, hHeq hmem]
      ring
  rw [regularizedGreen_lift_eq_convolution ε hε hεsmall, convolution_mul_swap,
    integral_congr_ae heq, integral_add hLQ hH, integral_add hL hQ,
    integral_scaledRadialMollifier_mul_sub_harmonic ε hε hHcont hHlocal,
    hHeq hxquarter,
    regularGreenRepresentative_local_expansion
      (closedBall_quarter_subset_centeredOpenBox hxquarter) hne]
  have hlog := integral_scaledRadialMollifier_mul_planarLogKernel_le ε hε hne
  have hquad := integral_scaledRadialMollifier_mul_quadratic_le ε hε x
  linarith

theorem regularizedGreen_torus_local_upper (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) {z : Torus}
    (hz : torusEuclideanNorm z ≤ (1 / 8 : ℝ)) (hne : z ≠ 0) :
    regularizedGreen ε hε z ≤ regularGreenRepresentative z + (Real.pi / 2) * ε ^ 2 := by
  have hlift : centeredLift z ≠ 0 := by
    intro h
    apply hne
    simpa only [h, torusQuotient_zero] using (torusQuotient_centeredLift z).symm
  simpa only [torusQuotient_centeredLift] using
    regularizedGreen_local_upper ε hε hεsmall
      (by simpa only [norm_centeredLift] using hz) hlift

end PeriodicAttractiveLogGas
