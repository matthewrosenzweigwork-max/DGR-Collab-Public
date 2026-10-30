import DGPS.Examples.PolynomialSpeciesRangeOrigin
import DGPS.Circle.QuantitativeLSI
import DGPS.Variational.SpeciesInclusion

/-! The strict full-domain interacting origin deficit. Only the actual zero-field
generator identity is used; no nonzero-field eigenfunction assumption occurs. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private theorem origin_reference_measure : polyEqM_EX055 0 = haar 1 := by
  rw [← polynomialRankOne_reference 0]
  change (haar 1).withDensity (fun x => ENNReal.ofReal ((polynomialRankOne 0).q x)) = _
  simp_rw [polynomial_reference_origin]
  simp

private theorem origin_entropy (ρ : AbsoluteDensity 1) :
    (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (polyEqM_EX055 0)).toReal =
      DGPS.Analysis.circleEntropy ρ := by
  rw [origin_reference_measure]
  have he : relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1) =
      homogeneousEntropy (haar 1) ρ.density := by
    rw [densityMeasure_coe]
    exact relativeEntropy_withDensity (Eventually.of_forall ρ.density_nonneg)
      ρ.integrable_density.aemeasurable
  rw [he]
  rfl

private theorem origin_fisher (ρ : AbsoluteDensity 1) :
    (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (polynomialRankOne 0).ref).toReal =
      DGPS.Analysis.circleFisherInformation ρ := by
  have hd (x : Torus 1) : (polynomialRankOne 0).dlogq x = 0 := by
    unfold RankOneModel.dlogq
    simp_rw [polynomial_reference_origin, Real.log_one]
    simp [coordPartial, Function.comp_def]
  rw [(polynomialRankOne 0).fisher_eq]
  simp_rw [hd, mul_zero, sub_zero]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  unfold DGPS.Analysis.circleFisherInformation
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 =
      4 * ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2
    rw [RankOneModel.norm_sq_tangent]
    ring

/-- Exact actual scalar identities at the Haar origin, retaining the original
absolute square-root H1 competitor and the true polynomial feature moments. -/
theorem polynomial_origin_scalar_identities
    (b : AbsoluteDrift (canonical_elementary_polynomial_model 0)) (ρ : AbsoluteDensity 1) :
    let m := ∫ x, (polynomialRankOne 0).φ x ∂(densityMeasure ρ : Measure (Torus 1))
    let J := ∫ x, (polynomialRankOne 0).dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
    (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) =
      DGPS.Analysis.circleEntropy ρ + eta / 2 * m ^ 2 ∧
    scalarDissipation (canonical_elementary_polynomial_model 0) b ρ ≠ ⊤ ∧
    (scalarDissipation (canonical_elementary_polynomial_model 0) b ρ).toReal =
      DGPS.Analysis.circleFisherInformation ρ +
        8 * eta * DGPS.Circle.AngularNormalization.a0 * m ^ 2 + eta ^ 2 * m ^ 2 * J := by
  obtain ⟨hg, hIfin, hDfin, hD⟩ := polynomial_family_gap_and_dissipation 0 b (SpeciesFamily.single ρ)
  simp only [speciesGap_single, speciesDissipation_single, densityMeasure_barycenter_single,
    sum_single_count, SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] at hg hDfin hD
  dsimp only
  refine ⟨?_, hDfin, ?_⟩
  · simpa only [origin_entropy] using hg
  · rw [origin_fisher] at hD
    simp_rw [polynomial_generator_origin] at hD
    rw [integral_const_mul] at hD
    rw [hD]
    ring

/-- Quantitative strict origin remainder on EVERY original absolute H1 density.
The positive interaction term is kept; no positive entropy premise is imposed. -/
theorem polynomial_origin_scalar_deficit_remainder
    (b : AbsoluteDrift (canonical_elementary_polynomial_model 0)) (ρ : AbsoluteDensity 1) :
    let m := ∫ x, (polynomialRankOne 0).φ x ∂(densityMeasure ρ : Measure (Torus 1))
    DGPS.Circle.AngularNormalization.a0 / 6 * DGPS.Analysis.circleEntropy ρ ^ 2 +
      7 * eta * DGPS.Circle.AngularNormalization.a0 * m ^ 2 ≤
        (scalarDissipation (canonical_elementary_polynomial_model 0) b ρ).toReal -
          2 * DGPS.Circle.AngularNormalization.a0 *
            (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) := by
  obtain ⟨hg, hDfin, hD⟩ := polynomial_origin_scalar_identities b ρ
  obtain ⟨_, _, hHaar, _⟩ := DGPS.Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ
  have hJ : 0 ≤ ∫ x, (polynomialRankOne 0).dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) :=
    integral_nonneg fun _ => sq_nonneg _
  dsimp only at hg hD ⊢
  rw [hg, hD]
  change 2 * DGPS.Circle.AngularNormalization.a0 * DGPS.Analysis.circleEntropy ρ +
    DGPS.Circle.AngularNormalization.a0 / 6 * DGPS.Analysis.circleEntropy ρ ^ 2 ≤
      DGPS.Analysis.circleFisherInformation ρ at hHaar
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg eta)
    (sq_nonneg (∫ x, (polynomialRankOne 0).φ x ∂(densityMeasure ρ : Measure (Torus 1))))) hJ]

/-- Every actual positive-gap full-domain competitor has strictly larger scalar
quotient than the Haar baseline at the origin. -/
theorem polynomial_origin_scalar_strict
    (b : AbsoluteDrift (canonical_elementary_polynomial_model 0)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model 0) ρ) :
    2 * DGPS.Circle.AngularNormalization.a0 *
        (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) <
      (scalarDissipation (canonical_elementary_polynomial_model 0) b ρ).toReal := by
  obtain ⟨hg, _, _⟩ := polynomial_origin_scalar_identities b ρ
  have hr := polynomial_origin_scalar_deficit_remainder b ρ
  have ha : 0 < DGPS.Circle.AngularNormalization.a0 := by
    unfold DGPS.Circle.AngularNormalization.a0
    positivity
  have hη := eta_pos
  have hH : 0 ≤ DGPS.Analysis.circleEntropy ρ := ENNReal.toReal_nonneg
  have hGr : 0 < (scalarGap (canonical_elementary_polynomial_model 0) ρ : ℝ) := by exact_mod_cast hG
  dsimp only at hg hr
  have hpos : 0 < DGPS.Circle.AngularNormalization.a0 / 6 * DGPS.Analysis.circleEntropy ρ ^ 2 +
      7 * eta * DGPS.Circle.AngularNormalization.a0 *
        (∫ x, (polynomialRankOne 0).φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 := by
    by_cases hHz : DGPS.Analysis.circleEntropy ρ = 0
    · have hm : 0 < (∫ x, (polynomialRankOne 0).φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 := by
        rw [hg, hHz, zero_add] at hGr
        exact pos_of_mul_pos_right hGr (by positivity : 0 ≤ eta / 2)
      positivity
    · have hHp : 0 < DGPS.Analysis.circleEntropy ρ := lt_of_le_of_ne hH (Ne.symm hHz)
      positivity
  linarith

end DGPS.Examples.PolynomialSpecies
