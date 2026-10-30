import DGPS.FiniteN.QuarticSaddleGlobalFIN066
import DGPS.FiniteN.Tools.QuadraticLaplace

/-! Actual auxiliary normalization and fixed-neighborhood exponential tails. -/

open MeasureTheory Metric
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.AttractiveLandscape
open scoped ContDiff

namespace DGPS.FiniteN

/-- Actual quadratic growth relative to any fixed field, with a fixed positive coefficient. -/
theorem quartic_quadratic_growth (w0 : EuclideanSpace ℝ (Fin 2)) :
    ∃ b > 0, ∃ C : ℝ, ∀ w, b * dist w w0 ^ 2 - C ≤
      quarticPsi_FIN066 w - quarticPsi_FIN066 w0 := by
  have hk := quarticKappa_pos_FIN066
  let L := Real.sqrt (quarticKappa * (1 + quarticEta))
  let C := ‖amap_FIN066 w0‖ ^ 2 / 4 + L ^ 2 +
    Real.log (zeta featU_FIN066 featPhi_FIN066 0) + quarticPsi_FIN066 w0
  refine ⟨1 / (8 * quarticKappa), by positivity, C, fun w => ?_⟩
  have hp := psi_lower_bound continuous_U_FIN066 continuous_Phi_FIN066
    norm_Phi_le_FIN066 (amap_FIN066 w)
  rw [psi_amap_FIN066 w] at hp
  have hA := norm_Alin_FIN066 (w - w0)
  have heq : Alin_FIN066 (w - w0) = amap_FIN066 w - amap_FIN066 w0 := by
    rw [map_sub, amap_eq_FIN066, amap_eq_FIN066]
    abel
  rw [heq] at hA
  have hn := norm_sub_le (amap_FIN066 w) (amap_FIN066 w0)
  have hsq : ‖amap_FIN066 w - amap_FIN066 w0‖ ^ 2 ≤
      2 * ‖amap_FIN066 w‖ ^ 2 + 2 * ‖amap_FIN066 w0‖ ^ 2 := by
    nlinarith [norm_nonneg (amap_FIN066 w - amap_FIN066 w0),
      norm_nonneg (amap_FIN066 w), norm_nonneg (amap_FIN066 w0),
      sq_nonneg (‖amap_FIN066 w‖ - ‖amap_FIN066 w0‖)]
  have hdist : dist w w0 ^ 2 ≤
      (2 * ‖amap_FIN066 w‖ ^ 2 + 2 * ‖amap_FIN066 w0‖ ^ 2) * quarticKappa := by
    rw [dist_eq_norm]
    exact (div_le_iff₀ hk).mp (hA.trans hsq)
  have hcomplete : ‖amap_FIN066 w‖ ^ 2 / 4 - L ^ 2 -
      Real.log (zeta featU_FIN066 featPhi_FIN066 0) ≤ quarticPsi_FIN066 w := by
    dsimp [L] at *
    nlinarith [sq_nonneg (‖amap_FIN066 w‖ / 2 - Real.sqrt (quarticKappa * (1 + quarticEta)))]
  have hdivide : dist w w0 ^ 2 / (8 * quarticKappa) ≤
      (‖amap_FIN066 w‖ ^ 2 + ‖amap_FIN066 w0‖ ^ 2) / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * quarticKappa)).2
    nlinarith [hdist]
  dsimp [C]
  rw [show 1 / (8 * quarticKappa) * dist w w0 ^ 2 =
    dist w w0 ^ 2 / (8 * quarticKappa) by ring]
  linarith only [hdivide, hcomplete]

/-- Actual two-dimensional auxiliary normalization and fixed-radius gap tails at the
same unique global minimum. Constants and neighborhoods precede particle number. -/
theorem quartic_auxiliary_laplace_data :
    ∃ t : ℝ, 1 < t ∧ t = 1 + Models.quarticKappa * DGPS.Circle.BesselMoments.besselRatio t ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      fderiv ℝ quarticPsi_FIN066 !₂[t, 0] = 0 ∧
      (∃ c > 0, ∀ v : EuclideanSpace ℝ (Fin 2),
        c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[t, 0] v v) ∧
      (∃ L > 0, ∃ A > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
        L * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0])) ≤
          ∫ w, Real.exp (-(N * quarticPsi_FIN066 w)) ∧
        ∫ w, Real.exp (-(N * quarticPsi_FIN066 w)) ≤
          A * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) ∧
      ∀ r : ℝ, 0 < r → ∃ c > 0, ∃ C > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧
        ∀ N : ℝ, N0 ≤ N →
          ∫ w in {w | r ≤ dist w (!₂[t, 0] : EuclideanSpace ℝ (Fin 2))},
              Real.exp (-(N * quarticPsi_FIN066 w)) ≤
            C * Real.exp (-(c * N)) * ∫ w, Real.exp (-(N * quarticPsi_FIN066 w)) := by
  obtain ⟨t, ht, hroot, huniq, hmin⟩ := global_minimizer_FIN066
  obtain ⟨hg, hu, hH⟩ := psi_global_FIN066 ht hroot hmin
  have hmap : ContDiff ℝ ∞ amap_FIN066 := by
    rw [show amap_FIN066 = fun z => Alin_FIN066 z +
      !₂[-1 / Real.sqrt quarticKappa, 0] from funext amap_eq_FIN066]
    exact Alin_FIN066.contDiff.add contDiff_const
  have hψ : ContDiff ℝ ∞ quarticPsi_FIN066 := by
    rw [quarticPsi_eq_FIN066]
    exact (contDiff_psi_infty continuous_U_FIN066 continuous_Phi_FIN066).comp hmap
  have h := quadratic_minimum_laplace_bounds_and_gap_tails
    (hψ.of_le (by simp)) hg (fun w hw => hu w hw.le) hH
    (quartic_quadratic_growth !₂[t, 0])
  refine ⟨t, ht, hroot, hg, hu, critical_quarticPsi_FIN066 hroot, hH, ?_, h.2⟩
  obtain ⟨L, hL, A, hA, N0, hN0, hbound⟩ := h.1
  refine ⟨L, hL, A, hA, N0, hN0, fun N hN => ?_⟩
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ) = 2 := by simp
  simpa only [hdim, show -((2 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
    using hbound N hN

/-- The original Laplace and tail interface, retained verbatim as a projection of
one actual same-minimum data producer. -/
theorem quartic_auxiliary_laplace_and_gap_tails :
    ∃ t : ℝ, 1 < t ∧
      (∃ L > 0, ∃ A > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
        L * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0])) ≤
          ∫ w, Real.exp (-(N * quarticPsi_FIN066 w)) ∧
        ∫ w, Real.exp (-(N * quarticPsi_FIN066 w)) ≤
          A * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) ∧
      ∀ r : ℝ, 0 < r → ∃ c > 0, ∃ C > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧
        ∀ N : ℝ, N0 ≤ N →
          ∫ w in {w | r ≤ dist w (!₂[t, 0] : EuclideanSpace ℝ (Fin 2))},
              Real.exp (-(N * quarticPsi_FIN066 w)) ≤
            C * Real.exp (-(c * N)) * ∫ w, Real.exp (-(N * quarticPsi_FIN066 w)) := by
  obtain ⟨t, ht, hroot, hg, hu, hcrit, hH, hbound, htail⟩ := quartic_auxiliary_laplace_data
  exact ⟨t, ht, hbound, htail⟩

end DGPS.FiniteN
