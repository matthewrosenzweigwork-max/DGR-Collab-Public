import DGPS.Examples.PolynomialSpeciesUniformOptimizerCapture
import DGPS.Examples.PolynomialSpeciesMinimizerProfileJet

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- Every ORIGINAL optimizer is uniformly captured near the two exact bases on the same graph. The compact bound is produced, not assumed. -/
theorem polynomial_scalarMinimizer_uniform_two_base_capture
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
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ)

    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ M : ℝ, 0 < δ ∧ 1 ≤ M ∧
      ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∃ A B σ α : ℝ, |A| ≤ M ∧ |B| ≤ M ∧ |σ| ≤ M ∧ |α| ≤ M ∧
        h ^ 4 * σ = root_EX054 h ∧
        a0 * (1 + h ^ 2 * α) = (scalarRate (canonical_elementary_polynomial_model h) b).toReal ∧
        polynomialScaledParameters (h, (A, B, α, σ)) ∈ U ∧
        ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h
          ((h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
            (ψ (polynomialScaledParameters (h, (A, B, α, σ))) : PeriodicC2_STR02969))).density ∧
        ∃ j : Fin 2, dist ((A, B), α) (polynomialQuarticCriticalBase j) < ε := by
  obtain ⟨δ₀, M, K, hδ₀, hM, _hK, hprofile⟩ :=
    polynomial_scalarMinimizer_absolute_profile_jet
      hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := hzero 0 0 0 h0U
  obtain ⟨δ₁, hδ₁, hcapture⟩ := polynomial_scalarMinimizer_compact_uniform_capture
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hamp
    (Metric.closedBall (0 : PolynomialScaledCoefficients) M)
    (isCompact_closedBall _ _) ε hε
  refine ⟨min δ₀ δ₁, M, lt_min hδ₀ hδ₁, hM, ?_⟩
  intro h hh hsmall b ρ hG hmin
  obtain ⟨A, B, σ, α, hA, hB, hσ, hα, hs, hr, hp, hρ, _herr⟩ :=
    hprofile h hh (hsmall.trans_le (min_le_left _ _)) b ρ hG hmin
  have hr' : a0 * (1 + h ^ 2 * α) =
      (scalarRate (canonical_elementary_polynomial_model h) b).toReal := by
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
  have hdata : PolynomialScaledOptimizerData U ψ h (A, B, α, σ) :=
    ⟨b, ρ, hs, hr', hG, hmin, hp', hρ'⟩
  have hc := hcapture h hh (hsmall.trans_le (min_le_right _ _)) (A, B, α, σ) hbox hdata
  exact ⟨A, B, σ, α, hA, hB, hσ, hα, hs, hr', hp', hρ', hc⟩

end DGPS.Examples.PolynomialSpecies
