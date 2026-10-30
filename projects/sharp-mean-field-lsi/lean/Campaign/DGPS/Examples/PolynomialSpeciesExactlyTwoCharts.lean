import DGPS.Examples.PolynomialSpeciesActualAtMostTwo
import DGPS.Examples.PolynomialSpeciesReflectionCaptureBounds
import DGPS.Examples.PolynomialSpeciesChartInjectivity
import DGPS.Examples.PolynomialSpeciesReflectionGraph
import DGPS.Examples.PolynomialScalarAttainmentFactory

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- Exactly two ORIGINAL optimizer laws, represented by reflected same-graph charts. Smooth-positive and pushforward adapters remain separate explicit output work. -/
theorem polynomial_exactly_two_scalar_optimizer_charts
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
      ∃ u v : PeriodicC2_STR02969,
        (∀ t : ℝ, v.val (-t) = u.val t) ∧
        densityMeasure (polynomialChartAbsolute h u) ≠ densityMeasure (polynomialChartAbsolute h v) ∧
        (0 < scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h u) ∧
          scalarQuotient (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u) =
            scalarRate (canonical_elementary_polynomial_model h) b) ∧
        (0 < scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h v) ∧
          scalarQuotient (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h v) =
            scalarRate (canonical_elementary_polynomial_model h) b) ∧
        ∀ ρ : AbsoluteDensity 1,
          (0 < scalarGap (canonical_elementary_polynomial_model h) ρ ∧
            scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
              scalarRate (canonical_elementary_polynomial_model h) b) ↔
          densityMeasure ρ = densityMeasure (polynomialChartAbsolute h u) ∨
            densityMeasure ρ = densityMeasure (polynomialChartAbsolute h v) := by
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := hzero 0 0 0 h0U
  obtain ⟨δA, hδA, hthree⟩ := polynomial_scalarMinimizer_at_most_two_laws
    hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  obtain ⟨δE, hδE, hattain⟩ := polynomial_scalar_attainment
  obtain ⟨δC, M, hδC, hM, hcapture⟩ := polynomial_scalarMinimizer_uniform_two_base_capture
    hU h0U hN h0N hψ hψN hgraph hzero hamp henv
    (Real.sqrt ((1 + Real.sqrt 2) / 4) / 2) (by positivity)
  obtain ⟨r, hr, hreflect⟩ := polynomial_range_graph_profile_reflection
    hU h0U hN h0N hψ hψ0 hψN hgraph
  have hMp : 0 < M + 1 := by linarith
  refine ⟨min δA (min δE (min δC (min 1 (r / (M + 1))))),
    lt_min hδA (lt_min hδE (lt_min hδC (lt_min zero_lt_one (div_pos hr hMp)))), ?_⟩
  intro h hh hsmall b
  obtain ⟨hhA, hrest⟩ := lt_min_iff.mp hsmall
  obtain ⟨hhE, hrest⟩ := lt_min_iff.mp hrest
  obtain ⟨hhC, hrest⟩ := lt_min_iff.mp hrest
  obtain ⟨hh1, hhr⟩ := lt_min_iff.mp hrest
  obtain ⟨ρ₀, hG₀, hmin₀⟩ := hattain h hh hhE b
  obtain ⟨A, B, σ, α, hA, hB, hσ, hα, hs, hrate, hp, hρ, j, hnear⟩ :=
    hcapture h hh hhC b ρ₀ hG₀ hmin₀
  have hBne : B ≠ 0 := polynomial_near_base_sine_ne_zero A B α j hnear
  have hnorm : ‖polynomialScaledParameters (h, (A, B, α, σ))‖ < r := by
    have hn := polynomial_scaled_parameters_norm_bound h A B α σ M hh.le hh1.le hM hA hB hα hσ
    have hprod := (lt_div_iff₀ hMp).1 hhr
    have hMh : M * h < r := by nlinarith only [hprod, hh]
    exact hn.trans_lt hMh
  let u : PeriodicC2_STR02969 := (h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
    (ψ (polynomialScaledParameters (h, (A, B, α, σ))) : PeriodicC2_STR02969)
  let v : PeriodicC2_STR02969 := (h * A) • cosC2_STR02915 + (-(h * B)) • sinC2_STR02915 +
    (ψ (h * A, -(h * B), (h, h ^ 4 * σ), h ^ 2 * α) : PeriodicC2_STR02969)
  have huv : ∀ t : ℝ, v.val (-t) = u.val t :=
    hreflect (h * A) (h * B) h (h ^ 4 * σ) (h ^ 2 * α) hnorm
  have hρu : ρ₀.density =ᵐ[haar 1] (polynomialChartAbsolute h u).density := hρ
  obtain ⟨hgu, hqu⟩ := polynomial_same_density_gap_quotient h b ρ₀ (polynomialChartAbsolute h u) hρu
  have huopt : 0 < scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h u) ∧
      scalarQuotient (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u) =
        scalarRate (canonical_elementary_polynomial_model h) b :=
    ⟨by rw [← hgu]; exact hG₀, hqu.symm.trans hmin₀⟩
  have hvopt := polynomial_scalarMinimizer_reflected_chart h b ρ₀ hG₀ hmin₀ u v hρu huv
  have hdistinct : densityMeasure (polynomialChartAbsolute h u) ≠
      densityMeasure (polynomialChartAbsolute h v) := by
    intro he
    have hmeas := congrArg Subtype.val he
    have hab := polynomialChart_law_amplitudes_injective h (h * A) (h * B) (h * A) (-(h * B))
      (ψ (polynomialScaledParameters (h, (A, B, α, σ))))
      (ψ (h * A, -(h * B), (h, h ^ 4 * σ), h ^ 2 * α)) hmeas
    have hz : h * B = 0 := by linarith [hab.2]
    exact hBne ((mul_eq_zero.mp hz).resolve_left hh.ne')
  refine ⟨u, v, huv, hdistinct, huopt, hvopt, ?_⟩
  intro ρ
  constructor
  · intro hopt
    rcases hthree h hh hhA b (polynomialChartAbsolute h u) (polynomialChartAbsolute h v) ρ
      huopt hvopt hopt with he | he | he
    · exact False.elim (hdistinct he)
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  · intro he
    rcases he with he | he
    · have hae := (densityMeasure_eq_iff_STR02901 _ _).1 (congrArg Subtype.val he)
      obtain ⟨hg, hq⟩ := polynomial_same_density_gap_quotient h b ρ (polynomialChartAbsolute h u) hae
      exact ⟨by rw [hg]; exact huopt.1, hq.trans huopt.2⟩
    · have hae := (densityMeasure_eq_iff_STR02901 _ _).1 (congrArg Subtype.val he)
      obtain ⟨hg, hq⟩ := polynomial_same_density_gap_quotient h b ρ (polynomialChartAbsolute h v) hae
      exact ⟨by rw [hg]; exact hvopt.1, hq.trans hvopt.2⟩

end DGPS.Examples.PolynomialSpecies
