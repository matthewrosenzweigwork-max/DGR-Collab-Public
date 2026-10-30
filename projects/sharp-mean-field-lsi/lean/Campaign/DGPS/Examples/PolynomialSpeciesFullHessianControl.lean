import DGPS.Examples.PolynomialSpeciesRangeDeficit

/-! Local control of the FULL original C2-chart Hessian of the actual physical
deficit. This differs from the reduced amplitude Hessian: no implicit graph
is inserted here. It is needed to compare a finite profile with that graph. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Input := (ℝ × ℝ) × ℝ × PeriodicC2_STR02969

/-- Full chart Hessian with independent reference and NORMALIZED rate shift. -/
def polynomialRangeFullHessian (z : (ℝ × ℝ) × ℝ × PeriodicC2_STR02969) :
    PeriodicC2_STR02969 →L[ℝ] PeriodicC2_STR02969 →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (polynomialRangeDeficit z.1
    (DGPS.Circle.AngularNormalization.a0 * (1 + z.2.1)))) z.2.2

private def normalizedValue (z : Input) : ℝ :=
  polynomialRangeDeficit z.1 (DGPS.Circle.AngularNormalization.a0 * (1 + z.2.1)) z.2.2

private theorem normalizedValue_smooth : ContDiff ℝ ∞ normalizedValue := by
  exact polynomialRangeDeficit_smooth.comp
    (contDiff_fst.prodMk ((contDiff_const.mul (contDiff_const.add contDiff_snd.fst)).prodMk contDiff_snd.snd))

/-- Actual joint regularity in the independent field, tilt, rate and full C2
chart, with no Hessian-bound or graph-nearness assumption. -/
theorem polynomialRangeFullHessian_smooth_at_origin :
    ContDiffAt ℝ ∞ polynomialRangeFullHessian (0 : Input) := by
  let q := fun z : Input × PeriodicC2_STR02969 => (z.1.1, z.1.2.1, z.2)
  have hq : ContDiff ℝ ∞ q := by dsimp only [q]; fun_prop
  have hF : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : Input) (u : PeriodicC2_STR02969) =>
        polynomialRangeDeficit z.1 (DGPS.Circle.AngularNormalization.a0 * (1 + z.2.1)) u)) (0, 0) := by
    have h := normalizedValue_smooth.comp hq
    exact h.contDiffAt
  have hD : ContDiffAt ℝ ∞ (fun z : Input =>
      fderiv ℝ (polynomialRangeDeficit z.1
        (DGPS.Circle.AngularNormalization.a0 * (1 + z.2.1))) z.2.2) 0 :=
    ContDiffAt.fderiv hF contDiffAt_snd.snd (by simp)
  have hDF : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : Input) (u : PeriodicC2_STR02969) =>
        fderiv ℝ (polynomialRangeDeficit z.1
          (DGPS.Circle.AngularNormalization.a0 * (1 + z.2.1))) u)) (0, 0) := by
    have h := hD.comp (0 : Input × PeriodicC2_STR02969) hq.contDiffAt
    convert h using 1 <;> rfl
  exact ContDiffAt.fderiv hDF contDiffAt_snd.snd (by simp)

/-- Genuine uniform local operator bound on the full Hessian's change.
The constant precedes ALL independent parameters and chart points. -/
theorem polynomialRangeFullHessian_lipschitz_origin :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      ∀ z : (ℝ × ℝ) × ℝ × PeriodicC2_STR02969, ‖z‖ < δ →
        ‖polynomialRangeFullHessian z - polynomialRangeFullHessian 0‖ ≤ K * ‖z‖ := by
  obtain ⟨K, T, hT, hLip⟩ :=
    (polynomialRangeFullHessian_smooth_at_origin.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨δ, K, hδ, K.coe_nonneg, fun z hz => ?_⟩
  have hzball : z ∈ Metric.ball (0 : Input) δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have h0ball : (0 : Input) ∈ Metric.ball 0 δ := by simpa only [Metric.mem_ball, dist_self] using hδ
  have he := hLip.dist_le_mul z (hball hzball) 0 (hball h0ball)
  simpa only [dist_eq_norm, sub_zero] using he

end DGPS.Examples.PolynomialSpecies
