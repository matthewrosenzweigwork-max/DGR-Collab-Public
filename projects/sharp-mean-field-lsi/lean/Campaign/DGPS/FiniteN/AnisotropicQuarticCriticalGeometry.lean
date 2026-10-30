import DGPS.FiniteN.AnisotropicQuarticExteriorGeometry
import DGPS.FiniteN.QuarticSaddleCriticalFIN067

/-! Actual complete critical geometry for the finite FIN070 patch cover. -/

open Set Metric
open DGPS.Models DGPS.Circle.BesselMoments
open DGPS.FiniteN.QuarticSaddleGlobalFIN066 DGPS.FiniteN.QuarticSaddleCriticalFIN067

namespace DGPS.FiniteN

/-- All actual critical fields are the unique physical positive field or a
negative-axis field with parameter in (0,4]. -/
theorem quartic_critical_point_classification {t : ℝ} (ht : 1 < t)
    (hroot : t = 1 + quarticKappa * besselRatio t)
    (w : EuclideanSpace ℝ (Fin 2)) (hw : fderiv ℝ quarticPsi_FIN066 w = 0) :
    w = !₂[t, 0] ∨ ∃ s : ℝ, 0 < s ∧ s ≤ 4 ∧ w = !₂[-s, 0] ∧
      fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 := by
  obtain ⟨t0, ht0, hroot0, huniq, hmin⟩ := global_minimizer_FIN066
  have htt : t = t0 := huniq t (by linarith) hroot
  have haxis : w 1 = 0 := axis_of_crit_FIN067 hw
  have heq : w = !₂[w 0, 0] := by
    ext i
    fin_cases i
    · rfl
    · exact haxis
  by_cases hp : 0 < w 0
  · have h0 := ((crit_iff_FIN067 w).mp hw).1
    rw [haxis] at h0
    have hsqrt : Real.sqrt (w 0 ^ 2 + (0 : ℝ) ^ 2) = w 0 := by
      rw [show w 0 ^ 2 + (0 : ℝ) ^ 2 = w 0 ^ 2 by ring]
      exact Real.sqrt_sq hp.le
    rw [hsqrt] at h0
    have hcancel : w 0 * besselRatio (w 0) / w 0 = besselRatio (w 0) := by
      field_simp
    rw [hcancel] at h0
    have hr : w 0 = 1 + quarticKappa * besselRatio (w 0) := by linarith
    have hx : w 0 = t := (huniq (w 0) hp hr).trans htt.symm
    exact Or.inl (heq.trans (by rw [hx]))
  · by_cases hz : w 0 = 0
    · have h0 := ((crit_iff_FIN067 w).mp hw).1
      simp [hz, haxis] at h0
    · have hn : w 0 < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      let s := -w 0
      have hs : 0 < s := neg_pos.mpr hn
      have hws : w = !₂[-s, 0] := by simpa only [s, neg_neg] using heq
      have hcrit : fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 := hws ▸ hw
      exact Or.inr ⟨s, hs, le_four_of_crit_FIN067 hs hcrit, hws, hcrit⟩

/-- The actual critical set is compact, from the proved far-gradient lower bound. -/
theorem quartic_critical_set_compact :
    IsCompact {w : EuclideanSpace ℝ (Fin 2) | fderiv ℝ quarticPsi_FIN066 w = 0} := by
  obtain ⟨ρ, hρ, c, hc, hfar⟩ := quartic_gradient_far_bound
  have hclosed : IsClosed {w : EuclideanSpace ℝ (Fin 2) | fderiv ℝ quarticPsi_FIN066 w = 0} :=
    isClosed_eq (quartic_potential_contDiff.continuous_fderiv (by simp)) continuous_const
  refine (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ).of_isClosed_subset hclosed ?_
  intro w hw
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  have hwρ : ρ < ‖w‖ := lt_of_not_ge h
  have hf := hfar w hwρ.le
  have hwzero : fderiv ℝ quarticPsi_FIN066 w = 0 := hw
  have hz : ‖fderiv ℝ quarticPsi_FIN066 w‖ = 0 := by
    rw [hwzero]
    exact norm_zero (E := EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  rw [hz] at hf
  exact (not_lt_of_ge hf) (mul_pos hc (hρ.trans hwρ))

end DGPS.FiniteN
