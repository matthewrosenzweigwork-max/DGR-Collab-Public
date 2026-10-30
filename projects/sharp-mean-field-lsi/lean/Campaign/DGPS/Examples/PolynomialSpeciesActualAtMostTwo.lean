import DGPS.Examples.PolynomialSpeciesUniformBranchUniqueness
import DGPS.Examples.PolynomialSpeciesMinimizerProfileJet
import DGPS.Examples.PolynomialSpeciesTwoLawAssembly

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- At most TWO laws among all original-domain optimizers, uniformly for small positive fields. All compactness, origin exclusion and local uniqueness inputs are produced internally. -/
theorem polynomial_scalarMinimizer_at_most_two_laws
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
    :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ₁ ρ₂ ρ₃ : AbsoluteDensity 1,
      (0 < scalarGap (canonical_elementary_polynomial_model h) ρ₁ ∧
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ₁ =
          scalarRate (canonical_elementary_polynomial_model h) b) →
      (0 < scalarGap (canonical_elementary_polynomial_model h) ρ₂ ∧
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ₂ =
          scalarRate (canonical_elementary_polynomial_model h) b) →
      (0 < scalarGap (canonical_elementary_polynomial_model h) ρ₃ ∧
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ₃ =
          scalarRate (canonical_elementary_polynomial_model h) b) →
      densityMeasure ρ₁ = densityMeasure ρ₂ ∨ densityMeasure ρ₁ = densityMeasure ρ₃ ∨
        densityMeasure ρ₂ = densityMeasure ρ₃ := by
  obtain ⟨δP, M, K₀, hδP, hM, _hK₀, hprofile⟩ :=
    polynomial_scalarMinimizer_absolute_profile_jet
      hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := hzero 0 0 0 h0U
  let K : Set PolynomialScaledCoefficients := Metric.closedBall 0 M
  have hK : IsCompact K := isCompact_closedBall _ _
  have hσK : ∀ c ∈ K, |c.2.2.2| ≤ M := by
    intro c hc
    have hn : max |c.1| (max |c.2.1| (max |c.2.2.1| |c.2.2.2|)) ≤ M := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hc
    exact (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hn).2).2).2
  have hbranches := fun j : Fin 2 =>
    polynomial_scalarMinimizer_uniform_branch_unique
      hU h0U hN h0N hψ hψ0 hψN hgraph hzero hamp K hK M hσK j
  choose δj hδj huniq using hbranches
  let ε := min (δj 0) (δj 1)
  have hε : 0 < ε := lt_min (hδj 0) (hδj 1)
  have hεδ (j : Fin 2) : ε ≤ δj j := by
    fin_cases j
    · exact min_le_left _ _
    · exact min_le_right _ _
  obtain ⟨δC, hδC, hcapture⟩ := polynomial_scalarMinimizer_compact_uniform_capture
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hamp K hK ε hε
  refine ⟨min δP (min δC ε), lt_min hδP (lt_min hδC hε), ?_⟩
  intro h hh hsmall b
  let P := fun ρ : AbsoluteDensity 1 =>
    0 < scalarGap (canonical_elementary_polynomial_model h) ρ ∧
    scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b
  let chart := fun c : PolynomialScaledCoefficients => polynomialChartAbsolute h
    ((h * c.1) • cosC2_STR02915 + (h * c.2.1) • sinC2_STR02915 +
      (ψ (polynomialScaledParameters (h, c)) : PeriodicC2_STR02969))
  let C := fun (ρ : AbsoluteDensity 1) (j : Fin 2) =>
    ∃ c ∈ K, PolynomialScaledOptimizerData U ψ h c ∧
      ρ.density =ᵐ[haar 1] (chart c).density ∧
      dist ((c.1, c.2.1), c.2.2.1) (polynomialQuarticCriticalBase j) < ε
  have hcover : ∀ ρ, P ρ → ∃ j, C ρ j := by
    intro ρ hρopt
    obtain ⟨A, B, σ, α, hA, hB, hσ, hα, hs, hr, hp, hρ, _herr⟩ :=
      hprofile h hh (hsmall.trans_le (min_le_left _ _)) b ρ hρopt.1 hρopt.2
    have hr' : a0 * (1 + h ^ 2 * α) =
        (scalarRate (canonical_elementary_polynomial_model h) b).toReal := by
      rw [hr]
      field_simp [a0_pos.ne'] <;> ring
    have hp' : polynomialScaledParameters (h, (A, B, α, σ)) ∈ U := hp
    have hρ' : ρ.density =ᵐ[haar 1] (chart (A, B, α, σ)).density := by
      simpa only [chart, polynomialGapLift, polynomialGapSlice, polynomialScaledParameters] using hρ
    have hbox : (A, B, α, σ) ∈ K := by
      simp only [K, Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
      exact max_le hA (max_le hB (max_le hα hσ))
    have hdata : PolynomialScaledOptimizerData U ψ h (A, B, α, σ) :=
      ⟨b, ρ, hs, hr', hρopt.1, hρopt.2, hp', hρ'⟩
    obtain ⟨j, hj⟩ := hcapture h hh
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      (A, B, α, σ) hbox hdata
    exact ⟨j, (A, B, α, σ), hbox, hdata, hρ', hj⟩
  have hclass : ∀ ρ τ j, P ρ → P τ → C ρ j → C τ j →
      densityMeasure ρ = densityMeasure τ := by
    intro ρ τ j _hρopt _hτopt hρC hτC
    obtain ⟨c, hc, hdc, hρc, hnearC⟩ := hρC
    obtain ⟨d, hd, hdd, hτd, hnearD⟩ := hτC
    have hsmallj : h < δj j := (hsmall.trans_le
      ((min_le_right _ _).trans (min_le_right _ _))).trans_le (hεδ j)
    have he := huniq j h hh hsmallj c hc d hd hdc hdd
      (hnearC.trans_le (hεδ j)) (hnearD.trans_le (hεδ j))
    have hσeq : c.2.2.2 = d.2.2.2 := by
      obtain ⟨bc, ρc, hsc, _⟩ := hdc
      obtain ⟨bd, ρd, hsd, _⟩ := hdd
      exact mul_left_cancel₀ (pow_ne_zero 4 hh.ne') (hsc.trans hsd.symm)
    have hcd : c = d := by
      apply Prod.ext
      · exact congrArg (fun z : PolynomialFactorUnknowns => z.1.1) he
      · apply Prod.ext
        · exact congrArg (fun z : PolynomialFactorUnknowns => z.1.2) he
        · apply Prod.ext
          · exact congrArg (fun z : PolynomialFactorUnknowns => z.2) he
          · exact hσeq
    subst d
    exact Subtype.ext ((densityMeasure_eq_iff_STR02901 _ _).2 (hρc.trans hτd.symm))
  exact three_laws_collision_of_two_classes P densityMeasure C hcover hclass

end DGPS.Examples.PolynomialSpecies
