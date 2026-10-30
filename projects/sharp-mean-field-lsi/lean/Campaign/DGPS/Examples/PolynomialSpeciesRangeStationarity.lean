import DGPS.Examples.PolynomialSpeciesRangeDeficit

/-! The actual full deficit is stationary at the centered zero chart for EVERY
independent reference and physical rate. True generator centering, not an
eigenfunction identity, removes the derivative of the m*A term. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem core_critical (L φ B j : PeriodicHolder_STR02968) (c r : ℝ)
    (G : PeriodicC2_STR02969 → ℝ) (hG : DifferentiableAt ℝ G 0)
    (hDG : fderiv ℝ G 0 = 0) (hm0 : eulerMean L 0 φ = 0) (hA0 : eulerMean L 0 B = 0) :
    fderiv ℝ (fun u : PeriodicC2_STR02969 => eulerFisher L u +
      2 * c * eulerMean L u φ * eulerMean L u B +
      c ^ 2 * (eulerMean L u φ) ^ 2 * eulerMean L u j - 2 * r * G u) 0 = 0 := by
  have hρ : ContDiff ℝ ∞ (eulerDensity L) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff))
  have hmean (f : PeriodicHolder_STR02968) : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => eulerMean L u f) :=
    meanCLM_STR02954.contDiff.comp (contDiff_const.mul hρ)
  have hIf : ContDiff ℝ ∞ (eulerFisher L) :=
    contDiff_const.mul (meanCLM_STR02954.contDiff.comp
      ((e1_STR02955.contDiff.mul e1_STR02955.contDiff).mul hρ))
  have hI := (hIf.differentiable (by simp) 0).hasFDerivAt
  have hm := ((hmean φ).differentiable (by simp) 0).hasFDerivAt
  have hA := ((hmean B).differentiable (by simp) 0).hasFDerivAt
  have hJ := ((hmean j).differentiable (by simp) 0).hasFDerivAt
  have hd := ((hI.add ((hm.const_mul (2 * c)).mul hA)).add
    (((hm.pow 2).const_mul (c ^ 2)).mul hJ)).sub (hG.hasFDerivAt.const_mul (2 * r))
  change HasFDerivAt (fun u : PeriodicC2_STR02969 => eulerFisher L u +
    2 * c * eulerMean L u φ * eulerMean L u B +
    c ^ 2 * (eulerMean L u φ) ^ 2 * eulerMean L u j - 2 * r * G u) _ 0 at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul,
    hm0, hA0, hDG, zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    show (2 : ℕ) - 1 = 1 from rfl, pow_one, zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  rw [eulerFisher_fderiv]
  simp [eulerMean, eulerCov]

private theorem curry_smooth (F : (ℝ × ℝ) × PeriodicC2_STR02969 → ℝ)
    (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => F (p, u)) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

/-- Genuine full-chart stationarity for all independent parameters and rates. -/
theorem polynomialRangeDeficit_fderiv_zero (p : ℝ × ℝ) (r : ℝ) :
    fderiv ℝ (polynomialRangeDeficit p r) 0 = 0 := by
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  have hρ : eulerDensity L 0 = polynomialRangeReference p := by
    simp only [L, eulerDensity, map_zero, add_zero, polynomialRangeReference]
  have hm : eulerMean L 0 (e0_STR02955 (polynomialRangeFeature p)) = 0 := by
    rw [eulerMean, hρ]
    exact polynomialRangeFeature_centered p
  have hA : eulerMean L 0 (polynomialRangeGenerator p) = 0 := by
    rw [eulerMean, hρ]
    exact polynomialRangeGenerator_centered p
  have hG := curry_smooth (fun x => polynomialRangeGap x.1 x.2) polynomialRangeGap_smooth p
  exact core_critical L (e0_STR02955 (polynomialRangeFeature p)) (polynomialRangeGenerator p)
    (polynomialRangeGradientSq p) eta r (polynomialRangeGap p) (hG.differentiable (by simp) 0)
    (polynomialRangeGap_fderiv_zero p) hm hA

end DGPS.Examples.PolynomialSpecies
