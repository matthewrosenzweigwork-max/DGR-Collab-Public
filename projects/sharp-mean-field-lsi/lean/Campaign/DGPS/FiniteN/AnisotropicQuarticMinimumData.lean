import DGPS.FiniteN.AnisotropicQuarticAuxiliaryMass
import DGPS.FiniteN.AnisotropicQuarticMinimumPatch

/-! One actual minimum witness for the local convexity and normalized mass data. -/

open MeasureTheory Metric Set
open DGPS.Models DGPS.Circle.BesselMoments
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.FiniteN

/-- The physical positive critical field, its fixed convex neighborhood, and all
normalized exponential gap tails use one and the same global minimum witness. -/
theorem quartic_minimum_data :
    ∃ t : ℝ, 1 < t ∧ t = 1 + quarticKappa * besselRatio t ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      fderiv ℝ quarticPsi_FIN066 !₂[t, 0] = 0 ∧
      ∃ r c : ℝ, 0 < r ∧ 0 < c ∧
        (∀ x ∈ ball (!₂[t, 0] : EuclideanSpace ℝ (Fin 2)) r,
          ∀ v : EuclideanSpace ℝ (Fin 2),
            c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ quarticPsi_FIN066) x v v) ∧
        ∀ R : ℝ, 0 < R → ∃ b > 0, ∃ C > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧
          ∀ N : ℝ, N0 ≤ N →
            ((imsEta N quarticPsi_FIN066)
              {w | R ≤ dist w (!₂[t, 0] : EuclideanSpace ℝ (Fin 2))}).toReal ≤
                C * Real.exp (-(b * N)) := by
  obtain ⟨t, ht, hroot, hg, hu, hcrit, hH, hbound, htail⟩ := quartic_auxiliary_laplace_data
  obtain ⟨tm, htm, hgm, hum, r, c, hr, hc, hess⟩ := quartic_minimum_strong_convex_patch
  have heq : (!₂[tm, 0] : EuclideanSpace ℝ (Fin 2)) = !₂[t, 0] := hu _ (hgm _)
  have htmt : tm = t := by
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) heq
    simpa using h
  subst tm
  refine ⟨t, ht, hroot, hg, hu, hcrit,
    r, c, hr, hc, hess, fun R hR => ?_⟩
  obtain ⟨b, hb, C, hC, N0, hN0, htail⟩ := htail R hR
  refine ⟨b, hb, C, hC, N0, hN0, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one (hN0.trans hN)
  have hS : MeasurableSet {w : EuclideanSpace ℝ (Fin 2) | R ≤ dist w !₂[t, 0]} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  rw [TiltedXY.Fin049.imsEta_real_FIN049 N quarticPsi_FIN066 (quartic_partition_pos N hNpos)
    {w : EuclideanSpace ℝ (Fin 2) | R ≤ dist w !₂[t, 0]} hS]
  exact (div_le_iff₀ (quartic_partition_pos N hNpos)).mpr (htail N hN)

end DGPS.FiniteN
