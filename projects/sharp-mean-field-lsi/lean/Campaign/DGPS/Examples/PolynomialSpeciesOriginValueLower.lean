import DGPS.Examples.PolynomialSpeciesOriginDeficit
import DGPS.Examples.PolynomialSpeciesRangeDeficit
import DGPS.Examples.PolynomialSpeciesGapComparison
import DGPS.Analysis.WeakConvolution

/-! Pure-origin VALUE lower bound of the actual polynomial deficit. The full
absolute-domain origin remainder is applied to the actual native chart, then
the same supplied graph's genuine gap comparison supplies the quartic scale.
No radial derivative bound or nonzero-field expansion is inferred. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ENNReal ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- On the full original absolute H1 domain, a small actual origin gap controls
its square by the actual scalar deficit. No positive-gap premise is needed. -/
theorem polynomial_origin_scalar_gap_deficit_lower
    (b : AbsoluteDrift (canonical_elementary_polynomial_model 0)) (ρ : AbsoluteDensity 1)
    (hG : (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) ≤ 1) :
    a0 / 12 * (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) ^ 2 ≤
      (scalarDissipation (canonical_elementary_polynomial_model 0) b ρ).toReal -
        2 * a0 * (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) := by
  let H := DGPS.Analysis.circleEntropy ρ
  let m := ∫ x, (polynomialRankOne 0).φ x ∂(densityMeasure ρ : Measure (Torus 1))
  let X := eta / 2 * m ^ 2
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hX : 0 ≤ X := by dsimp [X]; exact mul_nonneg (half_pos eta_pos).le (sq_nonneg m)
  have hg := (polynomial_origin_scalar_identities b ρ).1
  change (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) = H + X at hg
  have hX1 : X ≤ 1 := by linarith
  have hX2 : X ^ 2 ≤ X := by
    have hm := mul_le_mul_of_nonneg_left hX1 hX
    nlinarith only [hm]
  have hsq : (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) ^ 2 ≤
      2 * H ^ 2 + 2 * X := by rw [hg]; nlinarith [sq_nonneg (H - X)]
  have hr := polynomial_origin_scalar_deficit_remainder b ρ
  have hrem : a0 / 6 * H ^ 2 + 14 * a0 * X ≤
      (scalarDissipation (canonical_elementary_polynomial_model 0) b ρ).toReal -
        2 * a0 * (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) := by
    dsimp only at hr
    change a0 / 6 * H ^ 2 + 7 * eta * a0 * m ^ 2 ≤
      (scalarDissipation (canonical_elementary_polynomial_model 0) b ρ).toReal -
        2 * a0 * (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) at hr
    dsimp only [X]
    nlinarith only [hr]
  have hm := mul_le_mul_of_nonneg_left hsq (div_nonneg a0_pos.le (by norm_num : (0 : ℝ) ≤ 12))
  nlinarith [mul_nonneg a0_pos.le hX]

/-- Actual pure-origin same-graph VALUE quartic lower bound. All hypotheses
are factual conclusions of the existing common graph producer; neither a
quartic bound nor a radial estimate is an input. The graph is never reselected. -/
theorem polynomial_origin_same_graph_value_quartic_lower {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ × ℝ, ‖x‖ < δ →
      a0 / 768 * (x.1 ^ 2 + x.2 ^ 2) ^ 2 ≤
        polynomialRangeDeficit (0, 0) a0
          (polynomialGapLift ψ ((0, 0), 0) x) := by
  obtain ⟨δG, hδG, hcomp⟩ := polynomialReducedGap_uniform_comparison hU h0U hψ hzero hamp
  refine ⟨min δG 1, lt_min hδG zero_lt_one, fun x hx => ?_⟩
  let θ : (ℝ × ℝ) × ℝ := ((0, 0), 0)
  let u := polynomialGapLift ψ θ x
  let ρ := polynomialChartAbsolute 0 u
  let b := lipschitz_absoluteDrift (canonical_elementary_polynomial_model 0)
    (lipschitzData_canonical_model 0)
  have hxG : ‖(θ, x)‖ < δG := by
    have hn : ‖(θ, x)‖ = ‖x‖ := by
      change max (max (max ‖(0 : ℝ)‖ ‖(0 : ℝ)‖) ‖(0 : ℝ)‖) ‖x‖ = ‖x‖
      simp only [norm_zero, max_self, max_eq_right (norm_nonneg x)]
    rw [hn]
    exact hx.trans_le (min_le_left _ _)
  obtain ⟨_hentry, hlow, hupp⟩ := hcomp θ x hxG
  have hx1 : max |x.1| |x.2| < 1 := by
    simpa only [Prod.norm_def, Real.norm_eq_abs] using hx.trans_le (min_le_right _ _)
  have ha1 : |x.1| < 1 := (le_max_left _ _).trans_lt hx1
  have ha2 : |x.2| < 1 := (le_max_right _ _).trans_lt hx1
  have hr2 : x.1 ^ 2 + x.2 ^ 2 ≤ 2 := by
    have hs1 : x.1 ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg x.1) ha1.le 2
    have hs2 : x.2 ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg x.2) ha2.le 2
    linarith only [hs1, hs2]
  have hgap := polynomialReducedGap_actual ψ 0 0 x b
  rw [polynomial_root_origin] at hgap
  change polynomialReducedGap ψ θ x = (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) at hgap
  have hsmall : (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) ≤ 1 := by
    rw [← hgap]
    linarith
  have hvalue := polynomial_origin_scalar_gap_deficit_lower b ρ hsmall
  have hchart := polynomialChartAbsolute_deficit 0 a0 b u
  have hrestriction := polynomialRangeDeficit_actual 0 a0 u
  rw [polynomial_root_origin] at hrestriction
  change (scalarDissipation (canonical_elementary_polynomial_model 0) b ρ).toReal -
    2 * a0 * (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) = _ at hchart
  rw [hchart, ← hrestriction, ← hgap] at hvalue
  have hr : 0 ≤ (x.1 ^ 2 + x.2 ^ 2) / 8 := by positivity
  have hs := pow_le_pow_left₀ hr hlow 2
  have hm := mul_le_mul_of_nonneg_left hs (div_nonneg a0_pos.le (by norm_num : (0 : ℝ) ≤ 12))
  calc
    a0 / 768 * (x.1 ^ 2 + x.2 ^ 2) ^ 2 =
        a0 / 12 * ((x.1 ^ 2 + x.2 ^ 2) / 8) ^ 2 := by ring
    _ ≤ a0 / 12 * polynomialReducedGap ψ θ x ^ 2 := hm
    _ ≤ _ := hvalue

end DGPS.Examples.PolynomialSpecies
