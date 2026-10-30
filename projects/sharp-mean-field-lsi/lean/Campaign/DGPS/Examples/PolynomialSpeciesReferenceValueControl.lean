import DGPS.Examples.PolynomialSpeciesRangeStationarity
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual independent-reference value control in the FULL C2 chart. Both
the zero-chart value and its full chart derivative vanish genuinely. Thus the
full joint first derivative vanishes at the origin before any estimate. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Input := (ℝ × ℝ) × ℝ × PeriodicC2_STR02969
local instance : NormedAddCommGroup (Input →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Input →L[ℝ] ℝ) := inferInstance

private def value (z : Input) : ℝ :=
  polynomialRangeDeficit z.1 (DGPS.Circle.AngularNormalization.a0 * (1 + z.2.1)) z.2.2

private theorem value_smooth : ContDiff ℝ ∞ value := polynomialRangeDeficit_smooth.comp
  (contDiff_fst.prodMk ((contDiff_const.mul (contDiff_const.add contDiff_snd.fst)).prodMk contDiff_snd.snd))

private theorem derivative_zero : fderiv ℝ value (0 : Input) = 0 := by
  have hd (z : Input) : HasDerivAt (fun t : ℝ => value (t • z)) (fderiv ℝ value 0 z) 0 := by
    have hs : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
    exact (value_smooth.differentiable (by simp) 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 hs (by simp)
  have hparam (p : ℝ × ℝ) (γ : ℝ) : fderiv ℝ value 0 (p, γ, 0) = 0 := by
    have he : (fun t : ℝ => value (t • ((p, γ, 0) : Input))) = fun _ => 0 := by
      funext t
      simp only [value, Prod.smul_mk, smul_zero, polynomialRangeDeficit_zero]
    exact (hd (p, γ, 0)).unique (by rw [he]; exact hasDerivAt_const 0 0)
  have hchart (u : PeriodicC2_STR02969) : fderiv ℝ value 0 (0, 0, u) = 0 := by
    have hs : ContDiff ℝ ∞ (polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0) :=
      by
        have hi : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => (((0,0), DGPS.Circle.AngularNormalization.a0,u) : PolynomialEulerInput)) := contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
        have ht := polynomialRangeDeficit_smooth.comp hi
        exact ht
    have hu : HasDerivAt (fun t : ℝ => t • u) u 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
    have he := (hs.differentiable (by simp) 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu (by simp)
    rw [polynomialRangeDeficit_fderiv_zero, ContinuousLinearMap.zero_apply] at he
    have hf : (fun t : ℝ => value (t • ((0, 0, u) : Input))) =
        fun t => polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0 (t • u) := by
      funext t
      simp only [value, Prod.smul_mk, smul_zero, add_zero, mul_one, (show (0 : ℝ × ℝ) = (0,0) from rfl)]
    exact (hd (0, 0, u)).unique (by rw [hf]; exact he)
  apply ContinuousLinearMap.ext
  rintro ⟨p, γ, u⟩
  have he : ((p, γ, u) : Input) = (p, γ, 0) + (0, 0, u) := by ext <;> simp
  rw [he, map_add, hparam, hchart, add_zero, ContinuousLinearMap.zero_apply]

/-- Full-joint zero derivative and actual smoothness produce a value error
linear in the independent tilt and one order smaller in the joint size.
No selected reference root is differentiated. -/
theorem polynomialRangeDeficit_reference_value_error :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ (h s γ : ℝ) (u : PeriodicC2_STR02969),
      ‖(((h, s), γ, u) : (ℝ × ℝ) × ℝ × PeriodicC2_STR02969)‖ < δ →
      |polynomialRangeDeficit (h, s) (DGPS.Circle.AngularNormalization.a0 * (1 + γ)) u -
        polynomialRangeDeficit (h, 0) (DGPS.Circle.AngularNormalization.a0 * (1 + γ)) u| ≤
          K * ‖(((h, s), γ, u) : (ℝ × ℝ) × ℝ × PeriodicC2_STR02969)‖ * |s| := by
  have hDs : ContDiff ℝ 1 (fderiv ℝ value) := value_smooth.fderiv_right (by simp)
  have hc : ContDiffAt ℝ 1 (fderiv ℝ value) (0 : Input) := hDs.contDiffAt
  obtain ⟨K, T, hT, hLip⟩ := hc.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hT
  have h0ball : (0 : Input) ∈ Metric.ball 0 δ := by simpa only [Metric.mem_ball, dist_self] using hδ
  have hDbound (z : Input) (hz : ‖z‖ < δ) : ‖fderiv ℝ value z‖ ≤ K * ‖z‖ := by
    have hzball : z ∈ Metric.ball (0 : Input) δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have he := hLip.dist_le_mul z (hball hzball) 0 (hball h0ball)
    simpa only [derivative_zero, dist_zero_right] using he
  refine ⟨δ, K + 1, hδ, by positivity, fun h s γ u hz => ?_⟩
  let z : Input := ((h, s), γ, u)
  let z0 : Input := ((h, 0), γ, u)
  have hsmall (q : Input) (hq : q ∈ Metric.closedBall 0 ‖z‖) : ‖q‖ < δ :=
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hq : ‖q‖ ≤ ‖z‖).trans_lt hz
  have hb (q : Input) (hq : q ∈ Metric.closedBall 0 ‖z‖) : ‖fderiv ℝ value q‖ ≤ K * ‖z‖ :=
    (hDbound q (hsmall q hq)).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hq) K.coe_nonneg)
  have hz0 : z0 ∈ Metric.closedBall (0 : Input) ‖z‖ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simp only [z0, z, Prod.norm_def, norm_zero]
    exact max_le_max (max_le_max le_rfl (norm_nonneg s)) le_rfl
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun q _ => value_smooth.differentiable (by simp) q) hb
    (convex_closedBall (0 : Input) ‖z‖) hz0 (show z ∈ Metric.closedBall (0 : Input) ‖z‖ by simp)
  have hdist : ‖z - z0‖ = |s| := by
    simp only [z, z0, Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_def, norm_zero,
      Real.norm_eq_abs, max_self, max_eq_right (abs_nonneg s), max_eq_left (abs_nonneg s)]
  rw [Real.norm_eq_abs, hdist] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) (norm_nonneg z)) (abs_nonneg s))

end DGPS.Examples.PolynomialSpecies
