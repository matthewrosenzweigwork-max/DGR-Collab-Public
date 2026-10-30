import DGPS.FiniteN.AnisotropicQuarticCriticalGeometry
import DGPS.FiniteN.AnisotropicQuarticOtherCritical
import DGPS.FiniteN.AnisotropicQuarticMinimumData

/-! Actual normalized patches at every nonminimum critical field, for FIN070. -/

open MeasureTheory Set
open DGPS.Models DGPS.Circle.BesselMoments
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff ENNReal

namespace DGPS.FiniteN

/-- Every actual critical field different from the physical positive field has a
fixed open patch with at least a square-root-N normalized Dirichlet lower rate. -/
theorem quartic_nonminimum_critical_patch {t : ℝ} (ht : 1 < t)
    (hroot : t = 1 + quarticKappa * besselRatio t)
    (w : EuclideanSpace ℝ (Fin 2)) (hw : fderiv ℝ quarticPsi_FIN066 w = 0)
    (hne : w ≠ !₂[t, 0]) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ w ∈ U ∧
      ∃ a : ℝ, 0 < a ∧ ∀ N : ℝ, 1 ≤ N →
        ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
          tsupport F ⊆ U →
            a * Real.sqrt N * (∫ x, F x ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
              ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
  rcases quartic_critical_point_classification ht hroot w hw with h | ⟨s, hs, hs4, hws, hcrit⟩
  · exact False.elim (hne h)
  · by_cases hsEq : s = 4
    · obtain ⟨U, hU, hUp, a, ha, hlocal⟩ := quartic_normalized_unstable_local_dirichlet
      refine ⟨U, hU, ?_, a, ha, hlocal⟩
      simpa only [hws, hsEq] using hUp
    · have hslt : s < 4 := lt_of_le_of_ne hs4 hsEq
      obtain ⟨U, hU, hUp, a, ha, hlocal⟩ := quartic_other_critical_local_dirichlet hs hslt hcrit
      refine ⟨U, hU, hws.symm ▸ hUp, a, ha, fun N hN F hF hFc hFU => ?_⟩
      have hN0 : 0 ≤ N := zero_le_one.trans hN
      haveI := quartic_imsEta_probability N (lt_of_lt_of_le zero_lt_one hN)
      have hsqrt : Real.sqrt N ≤ N := Real.sqrt_le_iff.mpr ⟨hN0, by nlinarith⟩
      have hraw := hlocal N hN0 F hF hFc hFU
      have hnormalized : a * N * (∫ x, F x ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
          ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
        rw [TiltedXY.Fin049.imsEta_integral_FIN049 N quarticPsi_FIN066 quartic_potential_contDiff,
          TiltedXY.Fin049.imsEta_integral_FIN049 N quarticPsi_FIN066 quartic_potential_contDiff]
        have hz : 0 ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * quarticPsi_FIN066 x))))⁻¹.toReal :=
          ENNReal.toReal_nonneg
        have h := mul_le_mul_of_nonneg_left hraw hz
        convert h using 1 <;> ring
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt ha.le)
        (integral_nonneg fun x => sq_nonneg (F x))).trans hnormalized

end DGPS.FiniteN
