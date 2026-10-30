import DGPS.Examples.PolynomialResidualNormalization

/-! Actual zero-field data needed before the interacting range derivative can be
identified. The feature eigenfunction identity below is asserted ONLY at zero field. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.PositiveRankOne
open DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialExactGap
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Examples.PolynomialSpecies

/-- The actual unique moving-reference root at zero field. -/
theorem polynomial_root_origin : root_EX054 0 = 0 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := abs_root_le_sixth_EX054
  have hz : |root_EX054 0| ≤ 0 := by simpa using hb 0 (by simpa using hδ.le)
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

/-- The actual zero-field feature mean vanishes. -/
theorem polynomial_mean_origin : moment_EX054 0 (root_EX054 0) = 0 := by
  rw [polynomial_root_origin, moment_zero_EX054,
    DGPS.Examples.SixthOrderCentering.vonMisesCentering_eq,
    DGPS.Examples.SixthOrderCentering.besselI_two_eq, besselI1Over_zero]
  have hI : besselI 0 0 = 1 := by simp [besselI, angMode_zero]
  rw [hI]
  norm_num

/-- The actual moving reference at the origin is Haar, pointwise. -/
theorem polynomial_reference_origin (x : Torus 1) : (polynomialRankOne 0).q x = 1 := by
  change ThreeSpeciesCircle.gibbsDensity (polyPot_EX055 0 (root_EX054 0)) x = 1
  simp [ThreeSpeciesCircle.gibbsDensity, ThreeSpeciesCircle.gibbsZ, polyPot_EX055,
    polynomial_root_origin]

/-- The actual centered feature at the origin is the normalized second cosine mode. -/
theorem polynomial_feature_origin (x : Torus 1) :
    (polynomialRankOne 0).φ x = Real.sqrt 2 * cosT 2 x := by
  change Real.sqrt 2 * (polyFeature 0 x - moment_EX054 0 (root_EX054 0)) = _
  simp [polynomial_mean_origin, polyFeature]

/-- The true physical generator identity at the origin, derived from the actual residual bound.
It is not extended to nonzero fields. -/
theorem polynomial_generator_origin (x : Torus 1) :
    (polynomialRankOne 0).Aq x =
      (4 * DGPS.Circle.AngularNormalization.a0) * (polynomialRankOne 0).φ x := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := polynomial_physical_residual_bound
  have hz : |(polynomialRankOne 0).Aq x -
      (4 * DGPS.Circle.AngularNormalization.a0) * (polynomialRankOne 0).φ x| ≤ 0 := by
    simpa using hb 0 (by simpa using hδ.le) x
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

end DGPS.Examples.PolynomialSpecies
