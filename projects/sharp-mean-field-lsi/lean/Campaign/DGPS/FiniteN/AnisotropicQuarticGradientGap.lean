import DGPS.FiniteN.AnisotropicQuarticExterior

/-! Actual gradient gap and exterior rate off any open cover of the critical set. -/

open MeasureTheory Set Metric
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.FiniteN

/-- Compact minimization inside the far-field radius and the actual far-gradient
bound give a positive gradient gap off an open neighborhood of all actual critical points. -/
theorem quartic_gradient_gap_off_critical_cover
    (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : IsOpen V)
    (hcover : {w | fderiv ℝ quarticPsi_FIN066 w = 0} ⊆ V) :
    ∃ δ > 0, ∀ w, w ∉ V → δ ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖ := by
  obtain ⟨ρ, hρ, c, hc, hfar⟩ := quartic_gradient_far_bound
  let K := closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ ∩ Vᶜ
  have hK : IsCompact K := (isCompact_closedBall 0 ρ).inter_right hV.isClosed_compl
  have hcont : Continuous (fun w => ‖fderiv ℝ quarticPsi_FIN066 w‖) :=
    (continuous_norm (E := EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).comp
      (quartic_potential_contDiff.continuous_fderiv (by simp))
  have hlocal : ∃ b > 0, ∀ w ∈ K, b ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖ := by
    by_cases hKn : K.Nonempty
    · obtain ⟨w0, hw0, hmin⟩ := hK.exists_isMinOn hKn hcont.continuousOn
      have hpos : 0 < ‖fderiv ℝ quarticPsi_FIN066 w0‖ := by
        apply norm_pos_iff.mpr
        intro hz
        exact hw0.2 (hcover hz)
      exact ⟨_, hpos, fun w hw => hmin hw⟩
    · exact ⟨1, zero_lt_one, fun w hw => False.elim (hKn ⟨w, hw⟩)⟩
  obtain ⟨b, hb, hlocal⟩ := hlocal
  refine ⟨min b (c * ρ), lt_min hb (mul_pos hc hρ), fun w hw => ?_⟩
  by_cases hwρ : ‖w‖ ≤ ρ
  · exact (min_le_left _ _).trans (hlocal w ⟨by simpa only [mem_closedBall, dist_zero_right] using hwρ, hw⟩)
  · have hρw : ρ ≤ ‖w‖ := (lt_of_not_ge hwρ).le
    exact (min_le_right _ _).trans
      ((mul_le_mul_of_nonneg_left hρw hc.le).trans (hfar w hρw))

/-- The complement of any genuine open critical cover has an actual normalized
N-squared Dirichlet rate. The gradient gap is derived, not assumed. -/
theorem quartic_off_critical_cover_dirichlet
    (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : IsOpen V)
    (hcover : {w | fderiv ℝ quarticPsi_FIN066 w = 0} ⊆ V) :
    ∃ a : ℝ, 0 < a ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        tsupport F ⊆ Vᶜ →
          a * N ^ 2 * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
            ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
  obtain ⟨δ, hδ, hgap⟩ := quartic_gradient_gap_off_critical_cover V hV hcover
  obtain ⟨a, ha, N0, hN0, hlevel⟩ := quartic_gradient_level_dirichlet δ hδ
  exact ⟨a, ha, N0, hN0, fun N hN F hF hFc hFS =>
    hlevel N hN F hF hFc fun w hw => hgap w (hFS hw)⟩

end DGPS.FiniteN
