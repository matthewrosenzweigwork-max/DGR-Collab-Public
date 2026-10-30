import DGPS.FiniteN.QuarticSaddleGlobalFIN066

/-! A fixed strongly convex neighborhood of the actual quartic global minimum. -/

open Set Metric
open scoped ContDiff
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

/-- Actual positive critical field, global minimum and a fixed neighborhood with a
uniform positive Hessian lower bound. No local spectral inequality is a hypothesis. -/
theorem quartic_minimum_strong_convex_patch :
    ∃ t : ℝ, 1 < t ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
        ∀ x ∈ ball (!₂[t, 0] : EuclideanSpace ℝ (Fin 2)) r,
          ∀ v : EuclideanSpace ℝ (Fin 2),
            c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ quarticPsi_FIN066) x v v := by
  obtain ⟨t, ht, hroot, huniq, hmin⟩ := global_minimizer_FIN066
  obtain ⟨hg, hu, c, hc, hH⟩ := psi_global_FIN066 ht hroot hmin
  have hmap : ContDiff ℝ ∞ amap_FIN066 := by
    rw [show amap_FIN066 = fun z => Alin_FIN066 z +
      !₂[-1 / Real.sqrt quarticKappa, 0] from funext amap_eq_FIN066]
    exact Alin_FIN066.contDiff.add contDiff_const
  have hψ : ContDiff ℝ ∞ quarticPsi_FIN066 := by
    rw [quarticPsi_eq_FIN066]
    exact (DGPS.FiniteN.AttractiveLandscape.contDiff_psi_infty
      continuous_U_FIN066 continuous_Phi_FIN066).comp hmap
  let H := fderiv ℝ (fderiv ℝ quarticPsi_FIN066)
  let w0 : EuclideanSpace ℝ (Fin 2) := !₂[t, 0]
  have hcont : Continuous H :=
    (hψ.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  let U := {x | ‖H x - H w0‖ < c / 2}
  have hncont : Continuous (fun x => ‖H x - H w0‖) :=
    (continuous_norm (E := EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).comp (hcont.sub continuous_const)
  have hU : IsOpen U := isOpen_lt hncont continuous_const
  have hw : w0 ∈ U := by
    change ‖H w0 - H w0‖ < c / 2
    have hz : ‖H w0 - H w0‖ = 0 := by
      rw [sub_self]
      change ‖(0 : EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ = 0
      exact norm_zero (E := EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    rw [hz]
    exact half_pos hc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hw)
  refine ⟨t, ht, hg, hu, r, c / 2, hr, half_pos hc, fun x hx v => ?_⟩
  have hxU : ‖H x - H w0‖ < c / 2 := hball hx
  have hnorm : ‖(H x - H w0) v v‖ ≤ (c / 2) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖H x - H w0‖ * ‖v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ = ‖H x - H w0‖ * ‖v‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hxU.le (sq_nonneg _)
  have hlow : -((c / 2) * ‖v‖ ^ 2) ≤ (H x - H w0) v v :=
    (neg_le_neg hnorm).trans (by
      simpa only [Real.norm_eq_abs] using neg_abs_le ((H x - H w0) v v))
  have hsum : (H x - H w0) v v + H w0 v v = H x v v := by simp
  have hc0 : c * ‖v‖ ^ 2 ≤ H w0 v v := hH v
  change (c / 2) * ‖v‖ ^ 2 ≤ H x v v
  linarith

end DGPS.FiniteN
