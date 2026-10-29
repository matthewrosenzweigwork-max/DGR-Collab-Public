import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierLocalUpper
import Mathlib.Analysis.Calculus.MeanValue

/-! The complementary Taylor estimate in source Lemma 2.2. The two ordinary
mean-value estimates below give a remainder without the factor one half.
Our fixed mollifier is supported in the half-scale ball; this leaves enough
room to retain the source's stated upper constant 128 C. -/

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff

namespace PeriodicAttractiveLogGas

theorem planar_firstOrder_remainder_le {f : PlanarSpace → ℝ}
    {x y : PlanarSpace} {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hf : ∀ z ∈ closedBall x r, DifferentiableAt ℝ f z)
    (hf' : ∀ z ∈ closedBall x r, DifferentiableAt ℝ (fderiv ℝ f) z)
    (hb : ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C)
    (hy : y ∈ closedBall x r) :
    |f y - f x - fderiv ℝ f x (y - x)| ≤ C * r * ‖y - x‖ := by
  have hx : x ∈ closedBall x r := mem_closedBall_self hr
  have hs : Convex ℝ (closedBall x r) := convex_closedBall x r
  have hd : ∀ z ∈ closedBall x r, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * r := by
    intro z hz
    exact (hs.norm_image_sub_le_of_norm_fderiv_le hf' hb hx hz).trans
      (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hz) hC)
  have hrem := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z ↦ f z - fderiv ℝ f x z)
    (f' := fun z ↦ fderiv ℝ f z - fderiv ℝ f x)
    (fun z hz ↦ ((hf z hz).hasFDerivAt.sub (fderiv ℝ f x).hasFDerivAt).hasFDerivWithinAt)
    hd hx hy
  have heq : (f y - fderiv ℝ f x y) - (f x - fderiv ℝ f x x) =
      f y - f x - fderiv ℝ f x (y - x) := by rw [map_sub]; ring
  simpa only [heq, Real.norm_eq_abs] using hrem

theorem torusEuclideanNorm_near_far_point {x z : PlanarSpace}
    (hx : (1 / 8 : ℝ) ≤ torusEuclideanNorm (torusQuotient x))
    (hz : z ∈ closedBall x (1 / 16 : ℝ)) :
    (1 / 16 : ℝ) ≤ torusEuclideanNorm (torusQuotient z) := by
  have htri := torusEuclideanDist_triangle (torusQuotient x) (torusQuotient z) 0
  simp only [torusEuclideanDist_zero] at htri
  have hdist := torusEuclideanDist_quotient_le x z
  have hzx : dist x z ≤ (1 / 16 : ℝ) := by
    simpa only [mem_closedBall, dist_comm] using hz
  linarith

theorem regularGreenLift_far_hessian_bound {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : Torus, z ≠ 0 → ‖greenHessian z‖ ≤ C / torusEuclideanNorm z ^ 2)
    {x z : PlanarSpace} (hx : (1 / 8 : ℝ) ≤ torusEuclideanNorm (torusQuotient x))
    (hz : z ∈ closedBall x (1 / 16 : ℝ)) :
    ‖fderiv ℝ (fderiv ℝ regularGreenLift) z‖ ≤ 256 * C := by
  have hnorm := torusEuclideanNorm_near_far_point hx hz
  have hne : torusQuotient z ≠ 0 := by
    intro heq
    simp only [heq, torusEuclideanNorm_zero] at hnorm
    norm_num at hnorm
  rw [← greenHessian_lift]
  apply (hb _ hne).trans
  have hsq : (1 / 256 : ℝ) ≤ torusEuclideanNorm (torusQuotient z) ^ 2 := by nlinarith
  have hpos : 0 < torusEuclideanNorm (torusQuotient z) ^ 2 := by linarith
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem regularizedGreen_far_upper {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : Torus, z ≠ 0 → ‖greenHessian z‖ ≤ C / torusEuclideanNorm z ^ 2)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 16 : ℝ))
    (x : PlanarSpace) (hx : (1 / 8 : ℝ) ≤ torusEuclideanNorm (torusQuotient x)) :
    regularizedGreen ε hε (torusQuotient x) ≤
      regularGreenRepresentative (torusQuotient x) + 128 * C * ε ^ 2 := by
  have hball : closedBall x (ε / 2) ⊆ closedBall x (1 / 16 : ℝ) :=
    closedBall_subset_closedBall (by linarith)
  have hoff : ∀ z ∈ closedBall x (ε / 2), z ∈ offIntegerLattice := by
    intro z hz
    change torusQuotient z ≠ 0
    intro heq
    have hn := torusEuclideanNorm_near_far_point hx (hball hz)
    simp only [heq, torusEuclideanNorm_zero] at hn
    norm_num at hn
  have hf : ∀ z ∈ closedBall x (ε / 2), DifferentiableAt ℝ regularGreenLift z := by
    intro z hz
    exact (contDiffOn_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds (hoff z hz))).differentiableAt (by simp)
  have hf' : ∀ z ∈ closedBall x (ε / 2),
      DifferentiableAt ℝ (fderiv ℝ regularGreenLift) z := by
    intro z hz
    exact (contDiffOn_fderiv_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds (hoff z hz))).differentiableAt (by simp)
  have hh : ∀ z ∈ closedBall x (ε / 2),
      ‖fderiv ℝ (fderiv ℝ regularGreenLift) z‖ ≤ 256 * C :=
    fun z hz ↦ regularGreenLift_far_hessian_bound hC hb hx (hball hz)
  have hpoint (y : PlanarSpace) :
      scaledRadialMollifier ε y * regularGreenLift (x - y) ≤
        scaledRadialMollifier ε y *
          (regularGreenLift x - fderiv ℝ regularGreenLift x y + 128 * C * ε ^ 2) := by
    by_cases hy : scaledRadialMollifier ε y = 0
    · simp only [hy, zero_mul, le_refl]
    · have hyn : ‖y‖ < ε / 2 := by
        by_contra h
        exact hy (scaledRadialMollifier_eq_zero_of_half_le_norm ε hε (le_of_not_gt h))
      have hxy : x - y ∈ closedBall x (ε / 2) := by
        simpa only [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hyn.le
      have hrem := planar_firstOrder_remainder_le (f := regularGreenLift)
        (by positivity : 0 ≤ ε / 2) (by positivity : 0 ≤ 256 * C) hf hf' hh hxy
      have heq : x - y - x = -y := by abel
      rw [heq, norm_neg, map_neg, sub_neg_eq_add] at hrem
      have hu := (le_abs_self (regularGreenLift (x - y) - regularGreenLift x +
        fderiv ℝ regularGreenLift x y)).trans hrem
      apply mul_le_mul_of_nonneg_left _ (scaledRadialMollifier_nonneg ε y)
      have hm : 256 * C * (ε / 2) * ‖y‖ ≤ 64 * C * ε ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hyn.le (show 0 ≤ 256 * C * (ε / 2) by positivity)
        nlinarith
      nlinarith [mul_nonneg hC (sq_nonneg ε)]
  have hint : Integrable (fun y ↦ scaledRadialMollifier ε y * regularGreenLift (x - y)) volume := by
    have hi := ((hasCompactSupport_scaledRadialMollifier ε hε).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) locallyIntegrable_regularGreenLift
      (contDiff_scaledRadialMollifier ε).continuous x).integrable_swap
    change Integrable (fun y ↦ regularGreenLift (x - y) * scaledRadialMollifier ε y) volume at hi
    simpa only [mul_comm] using hi
  have hconst := (integrable_scaledRadialMollifier ε hε).mul_const (regularGreenLift x)
  have hlin := integrable_scaledRadialMollifier_mul_continuous ε hε
    (fderiv ℝ regularGreenLift x).continuous
  have hbound := (integrable_scaledRadialMollifier ε hε).mul_const (128 * C * ε ^ 2)
  have hsub : Integrable (fun y ↦ scaledRadialMollifier ε y * regularGreenLift x -
      scaledRadialMollifier ε y * fderiv ℝ regularGreenLift x y) volume := hconst.sub hlin
  rw [regularizedGreen_lift_eq_convolution ε hε hεsmall, convolution_mul_swap,
    regularGreenRepresentative_lift]
  calc
    (∫ y, regularGreenLift (x - y) * scaledRadialMollifier ε y) =
        ∫ y, scaledRadialMollifier ε y * regularGreenLift (x - y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ ↦ mul_comm _ _)
    _ ≤ ∫ y, scaledRadialMollifier ε y *
        (regularGreenLift x - fderiv ℝ regularGreenLift x y + 128 * C * ε ^ 2) :=
      integral_mono hint
        (integrable_scaledRadialMollifier_mul_continuous ε hε
          ((continuous_const.sub (fderiv ℝ regularGreenLift x).continuous).add continuous_const)) hpoint
    _ = regularGreenLift x + 128 * C * ε ^ 2 := by
      simp_rw [mul_add, mul_sub]
      rw [integral_add hsub hbound, integral_sub hconst hlin, integral_mul_const,
        integral_mul_const, integral_scaledRadialMollifier ε hε,
        integral_scaledRadialMollifier_mul_linear]
      ring

theorem exists_regularizedGreen_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
      ∀ z : Torus, z ≠ 0 →
        regularizedGreen ε hε z ≤ regularGreenRepresentative z + C * ε ^ 2 := by
  obtain ⟨B, hB, hb⟩ := exists_regularGreenRepresentative_torus_bounds
  refine ⟨max (Real.pi / 2) (128 * B), lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro ε hε hs z hz
  by_cases hr : torusEuclideanNorm z ≤ (1 / 8 : ℝ)
  · exact (regularizedGreen_torus_local_upper ε hε hs hr hz).trans
      (add_le_add_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ε)) _)
  · have hfar := regularizedGreen_far_upper hB.le (fun z hz ↦ (hb z hz).2.2.1)
      ε hε hs (centeredLift z) (by simpa only [torusQuotient_centeredLift] using (not_le.mp hr).le)
    simp only [torusQuotient_centeredLift] at hfar
    exact hfar.trans
      (add_le_add_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ε)) _)

end PeriodicAttractiveLogGas
