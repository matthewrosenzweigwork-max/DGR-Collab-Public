import LeanResearch.PeriodicAttractiveLogGas.GreenLocalBounds
import LeanResearch.PeriodicAttractiveLogGas.GreenFarBounds

/-! Global logarithmic and ordinary derivative bounds for the actual regular
Green representative. The local singular estimate is combined with a compact
bound away from the pole. The torus radius is the proved Euclidean quotient
radius, and the constants depend only on this fixed unit square torus. -/

noncomputable section
open Set Metric

namespace PeriodicAttractiveLogGas

theorem abs_log_norm_le_of_mem_centeredFarSet {x : PlanarSpace}
    (hx : x ∈ centeredFarSet) : |Real.log ‖x‖| ≤ |Real.log (1 / 4 : ℝ)| := by
  have hr1 := norm_le_one_of_mem_centeredClosedSquare hx.1
  have hl0 := Real.log_nonpos (norm_nonneg x) hr1
  have hl4 := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hx.2
  rw [abs_of_nonpos hl0]
  linarith [neg_le_abs (Real.log (1 / 4 : ℝ))]

theorem exists_smoothGreenLift_square_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ centeredClosedSquare, x ≠ 0 →
      |smoothGreenLift x + Real.log ‖x‖| ≤ C ∧
      ‖fderiv ℝ smoothGreenLift x‖ ≤ C / ‖x‖ ∧
      ‖fderiv ℝ (fderiv ℝ smoothGreenLift) x‖ ≤ C / (‖x‖ ^ 2) := by
  obtain ⟨A, hA, hlocal⟩ := exists_smoothGreenLift_quarter_bounds
  obtain ⟨B, hB, hfar⟩ := exists_greenFar_bounds
  let C : ℝ := A + B + |Real.log (1 / 4 : ℝ)| + 1
  have hAC : A ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log (1 / 4 : ℝ))]
  have hBC : B ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log (1 / 4 : ℝ))]
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x hx hne
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hne
  have hr1 := norm_le_one_of_mem_centeredClosedSquare hx
  have hr2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  by_cases hsmall : ‖x‖ ≤ (1 / 4 : ℝ)
  · obtain ⟨h0, h1, h2⟩ := hlocal x (mem_closedBall_zero_iff.mpr hsmall) hne
    refine ⟨h0.trans hAC, h1.trans ?_, h2.trans ?_⟩ <;> gcongr
  · have hxfar : x ∈ centeredFarSet := ⟨hx, (lt_of_not_ge hsmall).le⟩
    obtain ⟨h0, h1, h2⟩ := hfar x hxfar
    refine ⟨?_, h1.trans ?_, h2.trans ?_⟩
    · calc
        |smoothGreenLift x + Real.log ‖x‖| ≤ |smoothGreenLift x| + |Real.log ‖x‖| :=
          abs_add_le _ _
        _ ≤ B + |Real.log (1 / 4 : ℝ)| :=
          add_le_add h0 (abs_log_norm_le_of_mem_centeredFarSet hxfar)
        _ ≤ C := by dsimp [C]; linarith
    · apply (le_div_iff₀ hr).2
      calc
        B * ‖x‖ ≤ B * 1 := mul_le_mul_of_nonneg_left hr1 hB
        _ = B := mul_one _
        _ ≤ C := hBC
    · apply (le_div_iff₀ (sq_pos_of_pos hr)).2
      calc
        B * ‖x‖ ^ 2 ≤ B * 1 := mul_le_mul_of_nonneg_left hr2 hB
        _ = B := mul_one _
        _ ≤ C := hBC

theorem regularGreenRepresentative_eq_smoothGreenLift_centered {z : Torus} (hz : z ≠ 0) :
    regularGreenRepresentative z = smoothGreenLift (centeredLift z) := by
  have hx : centeredLift z ∈ offIntegerLattice := by
    simpa only [offIntegerLattice, mem_ofPred_eq, torusQuotient_centeredLift] using hz
  simpa only [torusQuotient_centeredLift] using regularGreenRepresentative_lift_of_mem hx

/-- The actual regular kernel has a global logarithmic estimate and its
ordinary derivatives in the centered Euclidean lift have the correct orders. -/
theorem exists_regularGreenRepresentative_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C ∧
      ‖fderiv ℝ smoothGreenLift (centeredLift z)‖ ≤ C / torusEuclideanNorm z ∧
      ‖fderiv ℝ (fderiv ℝ smoothGreenLift) (centeredLift z)‖ ≤
        C / (torusEuclideanNorm z ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_smoothGreenLift_square_bounds
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hx : centeredLift z ≠ 0 := fun h ↦ hz ((centeredLift_eq_zero_iff z).mp h)
  simpa only [norm_centeredLift, ← regularGreenRepresentative_eq_smoothGreenLift_centered hz]
    using hb (centeredLift z) (centeredLift_mem_closedSquare z) hx

/-- A finite lower bound holds also at the chosen origin value. No positive
coupling normalizer or Gibbs estimate is assumed. -/
theorem exists_regularGreenRepresentative_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Torus, -C ≤ regularGreenRepresentative z := by
  obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_bounds
  refine ⟨C, hC, ?_⟩
  intro z
  by_cases hz : z = 0
  · subst z
    rw [regularGreenRepresentative_zero]
    linarith
  · have hnorm1 : torusEuclideanNorm z ≤ 1 := by
      rw [← norm_centeredLift]
      exact norm_le_one_of_mem_centeredClosedSquare (centeredLift_mem_closedSquare z)
    have hl := Real.log_nonpos (torusEuclideanNorm_nonneg z) hnorm1
    have hlow := (abs_le.mp (hb z hz).1).1
    linarith

end PeriodicAttractiveLogGas
