import DGPS.Examples.PolynomialExactGap
import DGPS.Variational.PositiveRankOne
import DGPS.Foundations.WeakContractions

/-!
# The actual polynomial model as a positive rank-one variational problem

The normalized moving equilibrium introduces an additive constant in the one-body
potential. This file keeps that constant explicit and cancels it against the actual
free-energy minimum before transporting the full finite-family identities. No exact
eigenfunction relation for the polynomial feature is asserted.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Examples.PolynomialSpecies

open DGPS.PositiveRankOne DGPS.Examples.PolynomialEquilibrium
  DGPS.Examples.PolynomialExactGap

private abbrev eqPotential (h : ℝ) := polyPot_EX055 h (root_EX054 h)
private abbrev eqMean (h : ℝ) := moment_EX054 h (root_EX054 h)

/-- The normalized actual moving reference, not the unperturbed von Mises law. -/
noncomputable def polynomialRankOne (h : ℝ) : RankOneModel where
  q := ThreeSpeciesCircle.gibbsDensity (eqPotential h)
  φ := fun x => Real.sqrt 2 * (polyFeature h x - eqMean h)
  η := eta
  q_smooth := by
    unfold ThreeSpeciesCircle.gibbsDensity
    exact ((isSmooth_polyPot_EX055 h (root_EX054 h)).neg.exp).div_const _
  q_pos := ThreeSpeciesCircle.gibbsDensity_pos (isSmooth_polyPot_EX055 h (root_EX054 h))
  q_mass := ThreeSpeciesCircle.integral_gibbsDensity (isSmooth_polyPot_EX055 h (root_EX054 h))
  φ_smooth := by
    unfold IsSmoothPeriodic
    exact contDiff_const.mul ((isSmooth_polyFeature_EX055 h).sub contDiff_const)
  φ_centered := by
    let U := eqPotential h
    have hU := isSmooth_polyPot_EX055 h (root_EX054 h)
    have hi : Integrable (fun x => ThreeSpeciesCircle.gibbsDensity U x * polyFeature h x)
        (haar 1) :=
      ((ThreeSpeciesCircle.continuous_gibbsDensity hU).mul (continuous_polyFeature h)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hq : Integrable (ThreeSpeciesCircle.gibbsDensity U) (haar 1) :=
      (ThreeSpeciesCircle.continuous_gibbsDensity hU).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hm : ∫ x, ThreeSpeciesCircle.gibbsDensity U x * polyFeature h x ∂haar 1 = eqMean h := by
      rw [← ThreeSpeciesCircle.integral_gibbsMeasure_eq hU, moment_gibbs_EX055]
    have hpt : (fun x => Real.sqrt 2 * (polyFeature h x - eqMean h) *
        ThreeSpeciesCircle.gibbsDensity U x) =
        (fun x => Real.sqrt 2 * (ThreeSpeciesCircle.gibbsDensity U x * polyFeature h x -
          eqMean h * ThreeSpeciesCircle.gibbsDensity U x)) := by funext x; ring
    rw [hpt, integral_const_mul, integral_sub hi (hq.const_mul _), integral_const_mul,
      hm, ThreeSpeciesCircle.integral_gibbsDensity hU]
    ring
  η_nonneg := eta_pos.le

/-- The rank-one reference is exactly the already constructed polynomial equilibrium. -/
theorem polynomialRankOne_reference (h : ℝ) :
    (polynomialRankOne h).ref.measure = polyEqM_EX055 h := rfl

/-- The normalization and moving centering contribute this constant to the potential. -/
noncomputable def polynomialGaugeConstant (h : ℝ) : ℝ :=
  Real.log (ThreeSpeciesCircle.gibbsZ (eqPotential h)) +
    eta * (eqMean h ^ 2 - polyCentering h ^ 2)

/-- The interaction agrees pointwise, including its zero diagonal. -/
theorem polynomialRankOne_W (h : ℝ) (x y : Torus 1) :
    (polynomialRankOne h).data.W x y = (canonical_elementary_polynomial_model h).W x y := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  change eta * ((Real.sqrt 2 * (polyFeature h x - eqMean h)) *
      (Real.sqrt 2 * (polyFeature h y - eqMean h)) -
      (Real.sqrt 2 * (polyFeature h x - eqMean h)) ^ 2 / 2 -
      (Real.sqrt 2 * (polyFeature h y - eqMean h)) ^ 2 / 2) =
    -eta * (polyFeature h x - polyFeature h y) ^ 2
  calc _ = -(eta / 2) * ((Real.sqrt 2 * (polyFeature h x - eqMean h)) -
        (Real.sqrt 2 * (polyFeature h y - eqMean h))) ^ 2 := by ring
    _ = -eta * (polyFeature h x - polyFeature h y) ^ 2 := by
      rw [show Real.sqrt 2 * (polyFeature h x - eqMean h) -
        Real.sqrt 2 * (polyFeature h y - eqMean h) =
        Real.sqrt 2 * (polyFeature h x - polyFeature h y) by ring, mul_pow, hs]
      ring

/-- The one-body potentials agree up to the explicit constant; they are not identified. -/
theorem polynomialRankOne_V (h : ℝ) (x : Torus 1) :
    (polynomialRankOne h).data.V x =
      (canonical_elementary_polynomial_model h).V x + polynomialGaugeConstant h := by
  have hZ := ThreeSpeciesCircle.gibbsZ_pos (isSmooth_polyPot_EX055 h (root_EX054 h))
  have hlog : Real.log ((polynomialRankOne h).q x) =
      -eqPotential h x - Real.log (ThreeSpeciesCircle.gibbsZ (eqPotential h)) := by
    change Real.log (Real.exp (-eqPotential h x) / ThreeSpeciesCircle.gibbsZ (eqPotential h)) = _
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr := root_equation_EX054 h
  change -Real.log ((polynomialRankOne h).q x) +
      eta / 2 * (Real.sqrt 2 * (polyFeature h x - eqMean h)) ^ 2 = _
  rw [hlog, mul_pow, hs]
  change -(-(-h * cosT 1 x + root_EX054 h * polyFeature h x) -
      Real.log (ThreeSpeciesCircle.gibbsZ (eqPotential h))) +
      eta / 2 * (2 * (polyFeature h x - eqMean h) ^ 2) =
    -h * cosT 1 x + eta * (polyFeature h x - polyCentering h) ^ 2 +
      (Real.log (ThreeSpeciesCircle.gibbsZ (eqPotential h)) + eta * (eqMean h ^ 2 - polyCentering h ^ 2))
  dsimp only [eqMean] at *
  linear_combination (polyFeature h x) * hr

private theorem polynomial_minimum_real (h : ℝ) :
    freeEnergyMinimumReal (canonical_elementary_polynomial_model h) = -polynomialGaugeConstant h := by
  apply EReal.coe_injective
  rw [coe_freeEnergyMinimumReal, freeEnergyMinimum_eq_EX055, freeEnergy_polyEq_EX055]
  congr 1
  unfold gapOffset_EX055 polynomialGaugeConstant
  rw [mean_polyEq_EX055]
  have hr := root_equation_EX054 h
  dsimp only [eqMean, eqPotential]
  linear_combination (-moment_EX054 h (root_EX054 h)) * hr

private theorem polynomial_potential_energy (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    potentialEnergy (polynomialRankOne h).data ν =
      potentialEnergy (canonical_elementary_polynomial_model h) ν + polynomialGaugeConstant h := by
  unfold potentialEnergy
  simp_rw [polynomialRankOne_V]
  rw [integral_add ((canonical_elementary_polynomial_model h).V_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  simp

/-- Gauge cancellation at the actual minimum preserves every finite-family gap. -/
theorem polynomialRankOne_speciesGap (h : ℝ) (F : SpeciesFamily 1) :
    speciesGap (polynomialRankOne h).data F = speciesGap (canonical_elementary_polynomial_model h) F := by
  apply NNReal.coe_injective
  simp only [coe_speciesGap, speciesRawGap]
  rw [(polynomialRankOne h).freeEnergyMinimumReal_eq_zero, polynomial_minimum_real,
    polynomial_potential_energy]
  have hW : interactionEnergy (polynomialRankOne h).data (densityMeasure (barycenter F)) =
      interactionEnergy (canonical_elementary_polynomial_model h) (densityMeasure (barycenter F)) := by
    unfold interactionEnergy
    congr 1
    funext p
    exact polynomialRankOne_W h p.1 p.2
  rw [hW]
  ring

private theorem weakGradientLp_add_constant {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hw : IsWeakGradientLp 1 u g) (c : ℝ) : IsWeakGradientLp 1 (fun x => u x + c) g := by
  refine ⟨hw.memLp.add (memLp_const _), hw.memLp_grad, fun φ hφ j => ?_⟩
  have hi : Integrable (fun x => u x * coordPartial j φ x) (haar 1) :=
    hw.memLp.integrable_mul (hφ.memLp_top_coordPartial j)
  have hc : Integrable (fun x : Torus 1 => c * coordPartial j φ x) (haar 1) :=
    ((hφ.memLp_top_coordPartial j).integrable le_top).const_mul c
  have hz := (isWeakGradient_const (d := 1) c).ibp φ hφ j
  simp only [PiLp.zero_apply, zero_mul, integral_zero, neg_zero] at hz
  simp_rw [add_mul]
  rw [integral_add hi hc, hw.ibp φ hφ j, hz, add_zero]

/-- A canonical polynomial drift transports with the identical force, since the gauge is constant. -/
noncomputable def polynomialRankOneDrift (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    AbsoluteDrift (polynomialRankOne h).data where
  force := b.force
  measurable_force := b.measurable_force
  weak_gradient := by
    intro ρ
    have hpot : interactionPotential (polynomialRankOne h).data ρ =
        fun x => interactionPotential (canonical_elementary_polynomial_model h) ρ x +
          polynomialGaugeConstant h := by
      funext x
      unfold interactionPotential
      rw [polynomialRankOne_V]
      simp_rw [polynomialRankOne_W]
      ring
    rw [hpot]
    exact weakGradientLp_add_constant (b.weak_gradient ρ) _

/-- The transported force gives exactly the original absolute-domain dissipation. -/
theorem polynomialRankOne_speciesDissipation (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (F : SpeciesFamily 1) :
    speciesDissipation (polynomialRankOne h).data (polynomialRankOneDrift h b) F =
      speciesDissipation (canonical_elementary_polynomial_model h) b F := rfl

/-- The genuine interacting family identities on the exact canonical polynomial model.
All finite positive-weight families and all original absolute square-root H1 species are retained. -/
theorem polynomial_family_gap_and_dissipation (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (F : SpeciesFamily 1) :
    let M := polynomialRankOne h
    (speciesGap (canonical_elementary_polynomial_model h) F : ℝ) =
        ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
          (polyEqM_EX055 h)).toReal +
        eta / 2 * (∫ x, M.φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) ^ 2 ∧
      (∀ s, ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) M.ref ≠ ⊤) ∧
      speciesDissipation (canonical_elementary_polynomial_model h) b F ≠ ⊤ ∧
      (speciesDissipation (canonical_elementary_polynomial_model h) b F).toReal =
        ∑ s, F.weight s *
            (ordinaryRelativeFisher (densityMeasure (F.density s) : Measure (Torus 1)) M.ref).toReal +
          2 * eta * (∫ x, M.φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            (∫ x, M.Aq x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          eta ^ 2 * (∫ x, M.φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) ^ 2 *
            (∫ x, M.dφ x ^ 2 ∂(densityMeasure (barycenter F) : Measure (Torus 1))) := by
  have hd := positive_rank_one_gap_and_family_dissipation (polynomialRankOne h)
    (polynomialRankOneDrift h b) F
  simp only [show (polynomialRankOne h).η = eta from rfl] at hd
  simpa only [polynomialRankOne_speciesGap, polynomialRankOne_speciesDissipation,
    polynomialRankOne_reference] using hd

end DGPS.Examples.PolynomialSpecies
