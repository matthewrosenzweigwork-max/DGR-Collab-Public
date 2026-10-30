import DGPS.Examples.PolynomialSpeciesActualUniformCapture
import DGPS.Examples.PolynomialSpeciesPoincareMargin
import DGPS.Examples.PolynomialSpeciesNativeProfile

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- The original-domain optimizer's strict Poincare margin, on ONE retained
range graph. All profile, regularity, compact-box and coefficient-neighborhood
inputs are produced internally from actual global minimality. -/
theorem polynomial_scalarMinimizer_actual_poincare_margin
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (henv : ∀ a b h γ : ℝ,
      ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h (a0 * (1 + τ))
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
        (-2 * a0 * polynomialChartGap h
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      poincareRate (densityMeasure ρ) ≤ ENNReal.ofReal
        ((scalarRate (canonical_elementary_polynomial_model h) b).toReal - c * h ^ 2) ∧
      poincareRate (densityMeasure ρ) < scalarRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨δ₀, M, K, hδ₀, hM, _hK, hprofile⟩ :=
    polynomial_scalarMinimizer_absolute_profile_jet
      hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := hzero 0 0 0 h0U
  have hgraph0 : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0 :=
    fun p hp => (hgraph p hp (ψ p) (hψN p hp)).2 rfl
  obtain ⟨η, δP, c, hη, hδP, hc, hmargin⟩ :=
    polynomial_same_graph_profile_poincare_margin
      hU h0U hψ hψ0 hgraph0 hzero hamp M hM
  obtain ⟨δC, hδC, hcapture⟩ := polynomial_scalarMinimizer_compact_uniform_capture
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hamp
    (Metric.closedBall (0 : PolynomialScaledCoefficients) M)
    (isCompact_closedBall _ _) η hη
  obtain ⟨δS, hδS, hsmooth⟩ := polynomial_scalarMinimizer_smooth_representative
  let δ := min δ₀ (min δP (min δC (min δS (min 1 (1 / (2 * (M + 1)))))))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨δ, c, hδ, hc, ?_⟩
  intro h hh hsmall b ρ hG hmin
  have hh₀ : h < δ₀ := hsmall.trans_le (min_le_left _ _)
  have hhP : h ≤ δP := hsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhC : h < δC := hsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhS : h < δS := by dsimp only [δ] at hsmall; exact lt_of_lt_of_le hsmall (by exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hh1 : h ≤ 1 := by dsimp only [δ] at hsmall; exact hsmall.le.trans (by exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hhM : h ≤ 1 / (2 * (M + 1)) := by dsimp only [δ] at hsmall; exact hsmall.le.trans (by exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  obtain ⟨A, B, σ, α, hA, hB, hσ, hα, hs, hr, hp, hρ, _herr⟩ :=
    hprofile h hh hh₀ b ρ hG hmin
  have hr' : a0 * (1 + h ^ 2 * α) = (scalarRate (canonical_elementary_polynomial_model h) b).toReal := by
    rw [hr]
    field_simp [a0_pos.ne']
    <;> ring
  have hp' : polynomialScaledParameters (h, (A, B, α, σ)) ∈ U := hp
  have hρ' : ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h
      ((h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
        (ψ (polynomialScaledParameters (h, (A, B, α, σ))) : PeriodicC2_STR02969))).density := by
    simpa only [polynomialGapLift, polynomialGapSlice, polynomialScaledParameters] using hρ
  have hbox : (A, B, α, σ) ∈ Metric.closedBall (0 : PolynomialScaledCoefficients) M := by
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
    exact max_le hA (max_le hB (max_le hα hσ))
  obtain ⟨j, hj⟩ := hcapture h hh hhC (A, B, α, σ) hbox ⟨b, ρ, hs, hr', hG, hmin, hp', hρ'⟩
  have hnearA : |A - (-(1 + Real.sqrt 2) / 2)| < η := by
    have ht := (max_lt_iff.mp (show max (dist (A, B) (polynomialQuarticCriticalBase j).1)
      (dist α (polynomialQuarticCriticalBase j).2) < η by simpa only [Prod.dist_eq] using hj)).1
    have htA := (max_lt_iff.mp (show max (dist A (polynomialQuarticCriticalBase j).1.1)
      (dist B (polynomialQuarticCriticalBase j).1.2) < η by simpa only [Prod.dist_eq] using ht)).1
    simpa only [polynomialQuarticCriticalBase, Real.dist_eq] using htA
  have hnearα : |α - (3 - Real.sqrt 2) / 24| < η := by
    have ht := (max_lt_iff.mp (show max (dist (A, B) (polynomialQuarticCriticalBase j).1)
      (dist α (polynomialQuarticCriticalBase j).2) < η by simpa only [Prod.dist_eq] using hj)).2
    simpa only [polynomialQuarticCriticalBase, Real.dist_eq] using ht
  obtain ⟨v, hv, hvrep, hvlo, hvlog⟩ := hsmooth h hh hhS b ρ hG hmin
  obtain ⟨P, ell, hprob, hell, hlift, hP⟩ := polynomial_native_chart_profile_data h
    (polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * A, h * B))
    ρ v hv hvlog hvrep hvlo hρ
  have hlift' : ∀ t : ℝ, ell (t : AngCircle) =
      (polynomialRangeLogWeight (h, h ^ 4 * σ) +
        polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * A, h * B)).val t := by
    intro t; simpa only [hs] using hlift t
  have hm := hmargin A B σ α h hA hB hσ hα hh.le hhP hnearA hnearα P ell hell hlift' hP
  rw [hprob, hr'] at hm
  refine ⟨hm, hm.trans_lt ?_⟩
  have hMpos : 0 < 2 * (M + 1) := by linarith
  have hMh := (le_div_iff₀ hMpos).mp hhM
  have hsq : h ^ 2 ≤ h := by nlinarith only [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have hαlo := (abs_le.mp hα).1
  have hαsq := mul_le_mul_of_nonneg_left hαlo (sq_nonneg h)
  have hMsq := mul_le_mul_of_nonneg_left hsq (show 0 ≤ M by linarith)
  have hrate : 0 < (scalarRate (canonical_elementary_polynomial_model h) b).toReal := by
    rw [← hr']; apply mul_pos a0_pos; nlinarith only [hMh, hαsq, hMsq, hh]
  calc
    _ < ENNReal.ofReal (scalarRate (canonical_elementary_polynomial_model h) b).toReal :=
      (ENNReal.ofReal_lt_ofReal_iff hrate).2 (sub_lt_self _ (mul_pos hc (sq_pos_of_pos hh)))
    _ ≤ _ := ENNReal.ofReal_toReal_le

end DGPS.Examples.PolynomialSpecies
