import DGPS.Examples.PolynomialSpeciesMinimizerScaledCritical
import DGPS.Examples.PolynomialHaarTrialBounds

/-! Original-domain inputs for scaled origin exclusion: no optimizer
classification, annular lower bound or rate expansion is assumed. -/
noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

private theorem assembly_same_measure_gap (A : InteractionData 1) (ρ σ : AbsoluteDensity 1)
    (hμ : (densityMeasure ρ : Measure (Torus 1)) = densityMeasure σ) :
    scalarGap A ρ = scalarGap A σ := by
  have hprob : densityMeasure ρ = densityMeasure σ := Subtype.ext hμ
  apply NNReal.coe_injective
  change densityFreeEnergy A ρ - freeEnergyMinimumReal A =
    densityFreeEnergy A σ - freeEnergyMinimumReal A
  congr 1
  apply EReal.coe_injective
  rw [coe_densityFreeEnergy, coe_densityFreeEnergy, hprob]

/-- Positive original gap rules out the exact zero amplitude in a SAME-graph
representation. This is pointwise, not a uniform annular separation claim. -/
theorem polynomial_scalarMinimizer_scaled_amplitude_ne_zero
    {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969}
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (h A B α σ : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ : AbsoluteDensity 1)
    (hp : polynomialScaledParameters (h, (A, B, α, σ)) ∈ U)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hρ : ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h
      ((h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
        (ψ (polynomialScaledParameters (h, (A, B, α, σ))) : PeriodicC2_STR02969))).density) :
    (A, B) ≠ (0 : ℝ × ℝ) := by
  intro he
  have hA : A = 0 := congrArg Prod.fst he
  have hB : B = 0 := congrArg Prod.snd he
  let u : PeriodicC2_STR02969 :=
    (h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
      (ψ (polynomialScaledParameters (h, (A, B, α, σ))) : PeriodicC2_STR02969)
  have hp0 : ((0, 0, (h, h ^ 4 * σ), h ^ 2 * α) : PolynomialRangeParameters) ∈ U := by
    simpa only [polynomialScaledParameters, hA, hB, mul_zero] using hp
  have hu : u = 0 := by
    dsimp only [u]
    simp only [polynomialScaledParameters, hA, hB, mul_zero, zero_smul, zero_add]
    rw [hzero h (h ^ 4 * σ) (h ^ 2 * α) hp0]
    rfl
  have hμ : (densityMeasure ρ : Measure (Torus 1)) = densityMeasure (polynomialChartAbsolute h u) :=
    (densityMeasure_eq_iff_STR02901 _ _).2 hρ
  have heq := assembly_same_measure_gap (canonical_elementary_polynomial_model h)
    ρ (polynomialChartAbsolute h u) hμ
  have hgap : (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) = 0 := by
    rw [heq, polynomialChartAbsolute_gap_eq_rangeGap h b u, hu, polynomialRangeGap_zero]
  have hpos : (0 : ℝ) < (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) := by
    exact_mod_cast hG
  linarith

/-- The actual Haar competitor forces the coarse scaled-rate upper bound used
in the origin Hessian. Constants precede the field, drift and scaled rate. -/
theorem polynomial_scalarRate_scaled_coefficient_upper :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (α : ℝ),
      a0 * (1 + h ^ 2 * α) =
        (scalarRate (canonical_elementary_polynomial_model h) b).toReal →
      α ≤ 5 / 48 := by
  obtain ⟨δ, hδ, hTrial⟩ := polynomial_haar_trial_strict_upper
  refine ⟨δ, hδ, ?_⟩
  intro h hh hsmall b α hα
  obtain ⟨hTG, hTQ⟩ := hTrial h hh hsmall.le b
  have hrate : scalarRate (canonical_elementary_polynomial_model h) b ≤
      ENNReal.ofReal (a0 * (1 + 5 * h ^ 2 / 48)) :=
    ((scalarRate_le_quotient _ _ _ hTG).trans_lt hTQ).le
  have hreal := ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg a0_pos.le (by positivity : 0 ≤ 1 + 5 * h ^ 2 / 48)) hrate
  rw [← hα] at hreal
  have hinner : 1 + h ^ 2 * α ≤ 1 + 5 * h ^ 2 / 48 :=
    (mul_le_mul_iff_right₀ a0_pos).1 hreal
  have hmul : h ^ 2 * α ≤ h ^ 2 * (5 / 48) := by
    nlinarith only [hinner]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hh)).1 hmul

end DGPS.Examples.PolynomialSpecies
