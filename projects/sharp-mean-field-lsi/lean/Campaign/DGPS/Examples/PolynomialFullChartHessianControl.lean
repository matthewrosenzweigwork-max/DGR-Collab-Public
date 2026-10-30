import DGPS.Examples.PolynomialSpeciesFullHessianControl
import DGPS.Examples.PolynomialSpeciesRangeStationarity
import Mathlib.Analysis.Calculus.MeanValue

/-! The gradient remainder on the FULL original Banach C2 chart. Joint
Hessian control comes from the actual value's smoothness; stationarity is
proved for every independent reference and rate. No reduced graph is used. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Chart := PeriodicC2_STR02969
private abbrev Input := (ℝ × ℝ) × ℝ × Chart

private theorem fixedValue_smooth (p : ℝ × ℝ) (γ : ℝ) :
    ContDiff ℝ ∞ (polynomialRangeDeficit p
      (DGPS.Circle.AngularNormalization.a0 * (1 + γ))) := by
  have hi : ContDiff ℝ ∞ (fun u : Chart => ((p, DGPS.Circle.AngularNormalization.a0 * (1 + γ), u) : PolynomialEulerInput)) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have ht := polynomialRangeDeficit_smooth.comp hi
  exact ht

private theorem fixedGradient_smooth (p : ℝ × ℝ) (γ : ℝ) :
    ContDiff ℝ ∞ (fderiv ℝ (polynomialRangeDeficit p
      (DGPS.Circle.AngularNormalization.a0 * (1 + γ)))) :=
  (fixedValue_smooth p γ).fderiv_right (by simp)

/-- The radius and positive constant precede ALL independent references,
normalized rate shifts, and full C2 chart points. The gradient and remainder
are measured in the full continuous-linear-functional norm. -/
theorem polynomialRangeDeficit_full_gradient_remainder :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ (p : ℝ × ℝ) (γ : ℝ) (u : PeriodicC2_STR02969),
        ‖(p, γ, u)‖ < δ →
        ‖fderiv ℝ (polynomialRangeDeficit p
            (DGPS.Circle.AngularNormalization.a0 * (1 + γ))) u -
          polynomialRangeFullHessian 0 u‖ ≤ K * ‖(p, γ, u)‖ * ‖u‖ := by
  obtain ⟨δ, K, hδ, hK, hH⟩ := polynomialRangeFullHessian_lipschitz_origin
  refine ⟨δ, K + 1, hδ, by positivity, fun p γ u hu => ?_⟩
  let H0 : Chart →L[ℝ] Chart →L[ℝ] ℝ := polynomialRangeFullHessian 0
  let R : Chart → Chart →L[ℝ] ℝ := fun v =>
    fderiv ℝ (polynomialRangeDeficit p
      (DGPS.Circle.AngularNormalization.a0 * (1 + γ))) v - H0 v
  have hR0 : R 0 = 0 := by
    simp only [R, polynomialRangeDeficit_fderiv_zero, map_zero, sub_zero]
  have hDR (v : Chart) :
      HasFDerivAt R (polynomialRangeFullHessian (p, γ, v) - H0) v := by
    have hd := ((fixedGradient_smooth p γ).differentiable (by simp) v).hasFDerivAt
    exact hd.sub H0.hasFDerivAt
  have hsmall (v : Chart) (hv : v ∈ Metric.closedBall (0 : Chart) ‖u‖) :
      ‖(p, γ, v)‖ ≤ ‖(p, γ, u)‖ := by
    have hv' : ‖v‖ ≤ ‖u‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    simp only [Prod.norm_def]
    exact max_le_max le_rfl (max_le_max le_rfl hv')
  have hb (v : Chart) (hv : v ∈ Metric.closedBall (0 : Chart) ‖u‖) :
      ‖polynomialRangeFullHessian (p, γ, v) - H0‖ ≤ K * ‖(p, γ, u)‖ := by
    exact (hH (p, γ, v) ((hsmall v hv).trans_lt hu)).trans
      (mul_le_mul_of_nonneg_left (hsmall v hv) hK)
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v (_ : v ∈ Metric.closedBall (0 : Chart) ‖u‖) => (hDR v).hasFDerivWithinAt)
    hb (convex_closedBall (0 : Chart) ‖u‖)
    (show (0 : Chart) ∈ Metric.closedBall 0 ‖u‖ by
      simpa only [Metric.mem_closedBall, dist_self] using norm_nonneg u)
    (show u ∈ Metric.closedBall (0 : Chart) ‖u‖ by
      simp only [Metric.mem_closedBall, dist_zero_right, le_refl])
  rw [hR0, sub_zero, sub_zero] at hm
  change ‖R u‖ ≤ (K + 1) * ‖(p, γ, u)‖ * ‖u‖
  have hKK : K ≤ K + 1 := le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKK (norm_nonneg (p, γ, u))) (norm_nonneg u))

end DGPS.Examples.PolynomialSpecies
