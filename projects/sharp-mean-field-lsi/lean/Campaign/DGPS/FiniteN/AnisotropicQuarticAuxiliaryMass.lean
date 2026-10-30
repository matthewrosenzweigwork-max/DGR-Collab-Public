import DGPS.FiniteN.AnisotropicQuarticLaplace
import DGPS.FiniteN.AnisotropicQuarticFIN069
import DGPS.FiniteN.TiltedXYRateFIN049

/-! Genuine quartic auxiliary normalization and normalized local bounds for FIN070. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff ENNReal

namespace DGPS.FiniteN

theorem quartic_potential_contDiff : ContDiff ℝ ∞ quarticPsi_FIN066 := by
  have hmap : ContDiff ℝ ∞ amap_FIN066 := by
    rw [show amap_FIN066 = fun z => Alin_FIN066 z +
      !₂[-1 / Real.sqrt quarticKappa, 0] from funext amap_eq_FIN066]
    exact Alin_FIN066.contDiff.add contDiff_const
  rw [quarticPsi_eq_FIN066]
  exact (AttractiveLandscape.contDiff_psi_infty
    continuous_U_FIN066 continuous_Phi_FIN066).comp hmap

/-- Actual normalizer finiteness, for every positive real N, by a Gaussian majorant. -/
theorem quartic_weight_integrable (N : ℝ) (hN : 0 < N) :
    Integrable (fun w => Real.exp (-(N * quarticPsi_FIN066 w))) := by
  obtain ⟨b, hb, C, hgrow⟩ := quartic_quadratic_growth (0 : EuclideanSpace ℝ (Fin 2))
  have hG := Tools.QuadraticLaplace.gaussian_integrable (mul_pos hN hb)
    (0 : EuclideanSpace ℝ (Fin 2))
  have hi : Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (N * (C - quarticPsi_FIN066 0)) * Real.exp (-(N * b) * ‖w‖ ^ 2)) := by
    simpa only [sub_zero] using hG.const_mul (Real.exp (N * (C - quarticPsi_FIN066 0)))
  have hm : Continuous (fun w => Real.exp (-(N * quarticPsi_FIN066 w))) :=
    (Real.continuous_exp.comp (quartic_potential_contDiff.continuous.const_mul N).neg)
  refine hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hg := hgrow w
  rw [dist_zero_right] at hg
  nlinarith [mul_le_mul_of_nonneg_left hg hN.le]

/-- The actual finite normalizer is strictly positive. -/
theorem quartic_partition_pos (N : ℝ) (hN : 0 < N) :
    0 < ∫ w, Real.exp (-(N * quarticPsi_FIN066 w)) := by
  rw [integral_pos_iff_support_of_nonneg (fun w => (Real.exp_pos _).le)
    (quartic_weight_integrable N hN)]
  have hs : Function.support (fun w => Real.exp (-(N * quarticPsi_FIN066 w))) = univ :=
    Set.eq_univ_of_forall fun w => (Real.exp_pos _).ne'
  rw [hs]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

/-- The actual normalized auxiliary measure is a probability; no infinite-normalizer
or zero-measure branch is used. -/
theorem quartic_imsEta_probability (N : ℝ) (hN : 0 < N) :
    IsProbabilityMeasure (imsEta N quarticPsi_FIN066) := by
  have hI := quartic_weight_integrable N hN
  have hZ := quartic_partition_pos N hN
  have hz : (∫⁻ w, ENNReal.ofReal (Real.exp (-(N * quarticPsi_FIN066 w)))) =
      ENNReal.ofReal (∫ w, Real.exp (-(N * quarticPsi_FIN066 w))) :=
    (ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)).symm
  refine ⟨?_⟩
  unfold imsEta
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul, hz]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hZ).ne' ENNReal.ofReal_ne_top

/-- Actual normalized mass outside every fixed ball is exponentially small. -/
theorem quartic_normalized_gap_tails :
    ∃ t : ℝ, 1 < t ∧ ∀ r : ℝ, 0 < r → ∃ c > 0, ∃ C > 0,
      ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
        ((imsEta N quarticPsi_FIN066)
          {w | r ≤ dist w (!₂[t, 0] : EuclideanSpace ℝ (Fin 2))}).toReal ≤
            C * Real.exp (-(c * N)) := by
  obtain ⟨t, ht, hbound, htail⟩ := quartic_auxiliary_laplace_and_gap_tails
  refine ⟨t, ht, fun r hr => ?_⟩
  obtain ⟨c, hc, C, hC, N0, hN0, htail⟩ := htail r hr
  refine ⟨c, hc, C, hC, N0, hN0, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one (hN0.trans hN)
  have hS : MeasurableSet {w : EuclideanSpace ℝ (Fin 2) | r ≤ dist w !₂[t, 0]} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  rw [TiltedXY.Fin049.imsEta_real_FIN049 N quarticPsi_FIN066 (quartic_partition_pos N hNpos)
    {w : EuclideanSpace ℝ (Fin 2) | r ≤ dist w !₂[t, 0]} hS]
  exact (div_le_iff₀ (quartic_partition_pos N hNpos)).mpr (htail N hN)

/-- The checked actual FIN069 estimate in the normalized probability used by IMS. -/
theorem quartic_normalized_unstable_local_dirichlet :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ !₂[-4, 0] ∈ U ∧
      ∃ a : ℝ, 0 < a ∧ ∀ N : ℝ, 1 ≤ N →
        ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
          tsupport F ⊆ U →
            a * Real.sqrt N * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
              ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
  obtain ⟨U, hU, hw, a, ha, hlocal⟩ := quartic_unstable_local_dirichlet_square_root_n
  refine ⟨U, hU, hw, a, ha, fun N hN F hF hFc hFU => ?_⟩
  letI := quartic_imsEta_probability N (lt_of_lt_of_le zero_lt_one hN)
  rw [TiltedXY.Fin049.imsEta_integral_FIN049 N quarticPsi_FIN066 quartic_potential_contDiff,
    TiltedXY.Fin049.imsEta_integral_FIN049 N quarticPsi_FIN066 quartic_potential_contDiff]
  have hnonneg : 0 ≤ (∫⁻ w,
      ENNReal.ofReal (Real.exp (-(N * quarticPsi_FIN066 w))))⁻¹.toReal := ENNReal.toReal_nonneg
  have h := mul_le_mul_of_nonneg_left (hlocal N hN F hF hFc hFU) hnonneg
  convert h using 1 <;> ring

end DGPS.FiniteN
