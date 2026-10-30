import DGPS.Examples.PolynomialSpeciesRangeHalfTurn

/-! Exact moving-reference moment on the mixed field/amplitude line. The
reference centering is transported as a DIFFERENCE of normalized expectations;
it is not held fixed while the physical field varies. No graph jet is assumed. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- The actual centered feature moment for h=t,s=0 and u=t*(a*cos+b*sin). -/
def polynomialMixedFeatureMoment (a b t : ℝ) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
    (t • (a • cosC2_STR02915 + b • sinC2_STR02915))
    (e0_STR02955 (polynomialRangeFeature (t, 0)))

private theorem log_line (t : ℝ) : polynomialRangeLogWeight (t, 0) = t • cosC2_STR02915 := by
  apply Subtype.ext
  funext x
  change (polynomialRangeLogWeight (t, 0)).val x = (t • cosC2_STR02915).val x
  rw [polynomialRangeLogWeight_val_explicit, PeriodicC2_STR02969.val_smul,
    Pi.smul_apply, smul_eq_mul, cosC2_val_STR02915]
  ring

private theorem density_mass (u : PeriodicC2_STR02969) :
    meanCLM_STR02954 (eulerDensity (0 : PeriodicHolder_STR02968) u) = 1 := by
  rw [meanCLM_apply_STR02954]
  have hv : (eulerDensity (0 : PeriodicHolder_STR02968) u).val = rhoT_STR02901 0 u.val := by
    funext x
    simp only [eulerDensity, zero_add]
    exact rho_val_STR02954 (0, e0_STR02955 u) x
  rw [hv]
  exact meanT_rho_STR02950 0 u.isC2.2.1.continuous

private theorem expectation_affine (u : PeriodicC2_STR02969)
    (φ C : PeriodicHolder_STR02968) (c d : ℝ) :
    eulerMean (0 : PeriodicHolder_STR02968) u (φ - c • C - d • (1 : PeriodicHolder_STR02968)) =
      eulerMean (0 : PeriodicHolder_STR02968) u φ -
        c * eulerMean (0 : PeriodicHolder_STR02968) u C - d := by
  unfold eulerMean
  rw [sub_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, map_sub, map_sub,
    map_smul, map_smul, one_mul, density_mass]
  simp only [smul_eq_mul, mul_one]

/-- The true moving-reference centering contributes a subtracted reference
expectation. This identity is valid for all real parameters, before Taylor
expansion or restriction to any implicit graph. -/
theorem polynomialMixedFeatureMoment_identity (a b t : ℝ) :
    let v := a • cosC2_STR02915 + b • sinC2_STR02915
    let φ := e0_STR02955 (polynomialRangeFeature (0, 0))
    let C := e0_STR02955 cosC2_STR02915
    polynomialMixedFeatureMoment a b t =
      eulerMean (0 : PeriodicHolder_STR02968) (t • (cosC2_STR02915 + v)) φ -
        eulerMean (0 : PeriodicHolder_STR02968) (t • cosC2_STR02915) φ -
        (Real.sqrt 2 * t / 3) *
          (eulerMean (0 : PeriodicHolder_STR02968) (t • (cosC2_STR02915 + v)) C -
            eulerMean (0 : PeriodicHolder_STR02968) (t • cosC2_STR02915) C) := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  let φ := e0_STR02955 (polynomialRangeFeature (0, 0))
  let C := e0_STR02955 cosC2_STR02915
  let c := Real.sqrt 2 * t / 3
  let d := Real.sqrt 2 * moment_EX054 t 0
  have hm0 : moment_EX054 0 0 = 0 := by
    simpa only [polynomial_root_origin] using polynomial_mean_origin
  have hφ : e0_STR02955 (polynomialRangeFeature (t, 0)) =
      φ - c • C - d • (1 : PeriodicHolder_STR02968) := by
    apply ext_STR02954
    funext x
    simp only [e0_val_STR02955, polynomialRangeFeature_val, φ, C, c, d,
      PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_one_STR02954, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      cosC2_val_STR02915, DGPS.Examples.PolynomialCenteredResidual.feature_coe_EX057, hm0]
    ring
  have hcenter : eulerMean (0 : PeriodicHolder_STR02968) (t • cosC2_STR02915)
      (e0_STR02955 (polynomialRangeFeature (t, 0))) = 0 := by
    have hc := polynomialRangeFeature_centered (t, 0)
    simpa only [eulerMean, eulerDensity, polynomialRangeReference, log_line, zero_add] using hc
  rw [hφ, expectation_affine] at hcenter
  have hρ : eulerDensity (e0_STR02955 (polynomialRangeLogWeight (t, 0))) (t • v) =
      eulerDensity (0 : PeriodicHolder_STR02968) (t • (cosC2_STR02915 + v)) := by
    simp only [eulerDensity, log_line, map_smul, map_add, smul_add, zero_add]
  have hshift : polynomialMixedFeatureMoment a b t =
      eulerMean (0 : PeriodicHolder_STR02968) (t • (cosC2_STR02915 + v))
        (e0_STR02955 (polynomialRangeFeature (t, 0))) := by
    unfold polynomialMixedFeatureMoment eulerMean
    rw [hρ]
  rw [hshift, hφ, expectation_affine]
  change _ = eulerMean (0 : PeriodicHolder_STR02968) (t • (cosC2_STR02915 + v)) φ -
    eulerMean (0 : PeriodicHolder_STR02968) (t • cosC2_STR02915) φ - c *
      (eulerMean (0 : PeriodicHolder_STR02968) (t • (cosC2_STR02915 + v)) C -
        eulerMean (0 : PeriodicHolder_STR02968) (t • cosC2_STR02915) C)
  linear_combination hcenter

end DGPS.Examples.PolynomialSpecies
