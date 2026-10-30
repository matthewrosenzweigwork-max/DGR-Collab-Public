import DGPS.Examples.PolynomialSpeciesRangeQuadratic

/-! Actual second normalized feature moment in first-amplitude directions at
Haar. This is a derivative of the genuine normalized density, not a chosen
polynomial range correction. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem moment_second (φ : PeriodicHolder_STR02968) (v : PeriodicC2_STR02969)
    (hφ : meanCLM_STR02954 φ = 0) (hv : meanCLM_STR02954 (e0_STR02955 v) = 0) :
    HasDerivAt (fun z : ℝ => deriv (fun y : ℝ =>
      eulerMean (0 : PeriodicHolder_STR02968) (y • v) φ) z)
      (meanCLM_STR02954 ((φ * e0_STR02955 v) * e0_STR02955 v)) 0 := by
  let V := e0_STR02955 v
  let R := fun z : ℝ => rho_STR02954 (0, z • V)
  let μ := fun (f : PeriodicHolder_STR02968) (z : ℝ) => meanCLM_STR02954 (f * R z)
  let M := fun u : PeriodicC2_STR02969 => eulerMean (0 : PeriodicHolder_STR02968) u φ
  have hρ : ContDiff ℝ ∞ (eulerDensity (0 : PeriodicHolder_STR02968)) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff))
  have hM : ContDiff ℝ ∞ M := meanCLM_STR02954.contDiff.comp (contDiff_const.mul hρ)
  have hMd (z : ℝ) : HasDerivAt (fun y : ℝ => M (y • v))
      (eulerCov (0 : PeriodicHolder_STR02968) (z • v) φ V) z := by
    have hs : HasDerivAt (fun y : ℝ => y • v) v z := by
      simpa using (hasDerivAt_id z).smul_const v
    have hd := ((hM.differentiable (by simp) (z • v)).hasFDerivAt).comp_hasDerivAt z hs
    apply hd.congr_deriv
    have he := eulerMean_fderiv (0 : PeriodicHolder_STR02968) (fun _ => φ) contDiff_const (z • v) v
    rw [fderiv_const_apply] at he
    simp only [zero_apply, eulerMean, zero_mul, map_zero, zero_add] at he
    convert he using 1 <;> rfl
  have hR0 : R 0 = 1 := by simp only [R, zero_smul, rho_zero_STR02955]
  have hV : meanCLM_STR02954 V = 0 := hv
  have hR : HasDerivAt R V 0 := by
    simpa only [zero_add, rho_zero_STR02955, mul_one, one_mul, hV, zero_smul, sub_zero] using
      hasDerivAt_rho_path_STR02949 0 (0 : PeriodicHolder_STR02968) V
  have hμ (f : PeriodicHolder_STR02968) : HasDerivAt (μ f) (meanCLM_STR02954 (f * V)) 0 := by
    have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) f).mul hR)
    convert hd using 1 <;> simp only [μ, Function.comp_def, Pi.mul_apply, zero_mul, zero_add]
  have hφ0 : μ φ 0 = 0 := by simp only [μ, hR0, mul_one, hφ]
  have hV0 : μ V 0 = 0 := by simp only [μ, hR0, mul_one, hv, V]
  have hd := (hμ (φ * V)).sub ((hμ φ).mul (hμ V))
  have hd' : HasDerivAt (fun z : ℝ => μ (φ * V) z - μ φ z * μ V z)
      (meanCLM_STR02954 ((φ * V) * V)) 0 := by
    change HasDerivAt (fun z : ℝ => μ (φ * V) z - μ φ z * μ V z) _ 0 at hd
    apply hd.congr_deriv
    simp only [hφ0, hV0, zero_mul, mul_zero, add_zero, sub_zero]
  have he : (fun z : ℝ => deriv (fun y : ℝ => M (y • v)) z) =
      fun z : ℝ => μ (φ * V) z - μ φ z * μ V z := by
    funext z
    rw [(hMd z).deriv]
    simp only [eulerCov, eulerMean, eulerDensity, map_zero, map_smul, zero_add, R, μ, V]
  rw [he]
  exact hd'

/-- The actual zero-reference feature moment has this genuine second derivative.
The remaining finite Fourier evaluation identifies its explicit a,b coefficient. -/
theorem polynomialOriginAmplitudeMoment_second (a b : ℝ) :
    HasDerivAt (fun z : ℝ => deriv (fun y : ℝ =>
      eulerMean (0 : PeriodicHolder_STR02968)
        (y • (a • cosC2_STR02915 + b • sinC2_STR02915))
        (e0_STR02955 (polynomialRangeFeature (0, 0)))) z)
      (meanCLM_STR02954
        ((e0_STR02955 (polynomialRangeFeature (0, 0)) *
          e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915)) *
          e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915))) 0 := by
  have hφ : meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0))) = 0 := by
    have h := polynomialRangeFeature_centered (0, 0)
    have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
    have hQ : polynomialRangeReference (0, 0) = 1 := by
      rw [polynomialRangeReference, hL, map_zero, rho_zero_STR02955]
    rw [hQ, mul_one] at h
    exact h
  exact moment_second _ _ hφ (polynomial_first_amplitude_centered a b)

end DGPS.Examples.PolynomialSpecies
