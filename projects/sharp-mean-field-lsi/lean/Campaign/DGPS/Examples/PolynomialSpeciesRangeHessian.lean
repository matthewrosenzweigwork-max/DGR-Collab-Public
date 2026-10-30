import DGPS.Examples.PolynomialSpeciesRangeGap

/-! The genuine Hessian of the independent-parameter gap at the Haar origin.
Normalization contributes the covariance; the centered interaction contributes
its actual feature-moment product. No generator eigenfunction identity is used. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem density_smooth (L : PeriodicHolder_STR02968) :
    ContDiff ℝ ∞ (eulerDensity L) :=
  rho_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff))

private theorem mean_smooth (L f : PeriodicHolder_STR02968) :
    ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => eulerMean L u f) :=
  meanCLM_STR02954.contDiff.comp (contDiff_const.mul (density_smooth L))

private theorem entropy_smooth (L : PeriodicHolder_STR02968) :
    ContDiff ℝ ∞ (eulerEntropy L) := by
  have hmean : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 =>
      eulerMean L u (e0_STR02955 u)) :=
    meanCLM_STR02954.contDiff.comp (e0_STR02955.contDiff.mul (density_smooth L))
  exact (hmean.sub (logZ_smooth_STR02954.comp
    (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff)))).add contDiff_const

/-- The full chart first derivative of the actual gap, including its normalized
interaction moment. -/
theorem polynomialRangeGap_fderiv (p : ℝ × ℝ) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (polynomialRangeGap p) u v =
      eulerCov (e0_STR02955 (polynomialRangeLogWeight p)) u
        (e0_STR02955 u) (e0_STR02955 v) +
      eta * eulerMean (e0_STR02955 (polynomialRangeLogWeight p)) u
        (e0_STR02955 (polynomialRangeFeature p)) *
      eulerCov (e0_STR02955 (polynomialRangeLogWeight p)) u
        (e0_STR02955 (polynomialRangeFeature p)) (e0_STR02955 v) := by
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  let φ := e0_STR02955 (polynomialRangeFeature p)
  have hH := ((entropy_smooth L).differentiable (by simp) u).hasFDerivAt
  have hm := ((mean_smooth L φ).differentiable (by simp) u).hasFDerivAt
  have hd := hH.add ((hm.pow 2).const_mul (eta / 2))
  have he : polynomialRangeGap p = fun w : PeriodicC2_STR02969 =>
      eulerEntropy L w + (eta / 2) * (eulerMean L w φ) ^ 2 := by
    funext w
    unfold polynomialRangeGap
    dsimp only [L, φ]
    ring
  change HasFDerivAt (fun w : PeriodicC2_STR02969 =>
    eulerEntropy L w + (eta / 2) * (eulerMean L w φ) ^ 2) _ u at hd
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  rw [eulerEntropy_fderiv]
  have hm' : fderiv ℝ (fun w : PeriodicC2_STR02969 => eulerMean L w φ) u v =
      eulerCov L u φ (e0_STR02955 v) := by
    simpa [eulerMean] using eulerMean_fderiv L (fun _ => φ) contDiff_const u v
  rw [hm']
  ring

private theorem origin_line (w v : PeriodicC2_STR02969) :
    HasDerivAt (fun z : ℝ => fderiv ℝ (polynomialRangeGap (0, 0)) (z • w) v)
      (meanCLM_STR02954 (e0_STR02955 w * e0_STR02955 v) -
        meanCLM_STR02954 (e0_STR02955 w) * meanCLM_STR02954 (e0_STR02955 v) +
        eta * meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0)) * e0_STR02955 w) *
          meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0)) * e0_STR02955 v)) 0 := by
  let W := e0_STR02955 w
  let V := e0_STR02955 v
  let φ := e0_STR02955 (polynomialRangeFeature (0, 0))
  let R := fun z : ℝ => rho_STR02954 (0, z • W)
  let μ := fun (f : PeriodicHolder_STR02968) (z : ℝ) => meanCLM_STR02954 (f * R z)
  let C := fun (f g : PeriodicHolder_STR02968) (z : ℝ) => μ (f * g) z - μ f z * μ g z
  have hL : polynomialRangeLogWeight (0, 0) = 0 := by simp [polynomialRangeLogWeight]
  have hR0 : R 0 = 1 := by simp only [R, zero_smul, rho_zero_STR02955]
  have hφ0 : meanCLM_STR02954 φ = 0 := by
    have h := polynomialRangeFeature_centered (0, 0)
    have hr : polynomialRangeReference (0, 0) = 1 := by
      rw [polynomialRangeReference, hL, map_zero, rho_zero_STR02955]
    rw [hr, mul_one] at h
    exact h
  have hR : HasDerivAt R (W - meanCLM_STR02954 W • (1 : PeriodicHolder_STR02968)) 0 := by
    simpa only [zero_add, rho_zero_STR02955, mul_one, one_mul] using
      hasDerivAt_rho_path_STR02949 0 (0 : PeriodicHolder_STR02968) W
  have hμ (f : PeriodicHolder_STR02968) : HasDerivAt (μ f)
      (meanCLM_STR02954 (f * (W - meanCLM_STR02954 W • (1 : PeriodicHolder_STR02968)))) 0 := by
    have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) f).mul hR)
    convert hd using 1 <;> simp only [μ, Function.comp_def, Pi.mul_apply, zero_mul, zero_add]
  have hC (f g : PeriodicHolder_STR02968) : DifferentiableAt ℝ (C f g) 0 :=
    ((hμ (f * g)).sub ((hμ f).mul (hμ g))).differentiableAt
  have hm0 : μ φ 0 = 0 := by simp only [μ, hR0, mul_one, hφ0]
  have hm' : meanCLM_STR02954
      (φ * (W - meanCLM_STR02954 W • (1 : PeriodicHolder_STR02968))) =
      meanCLM_STR02954 (φ * W) := by
    rw [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul, hφ0, smul_zero, sub_zero]
  have hd := ((hasDerivAt_id (0 : ℝ)).mul (hC W V).hasDerivAt).add
    (((hμ φ).mul (hC φ V).hasDerivAt).const_mul eta)
  have hd' : HasDerivAt (fun z : ℝ => z * C W V z + eta * (μ φ z * C φ V z))
      (meanCLM_STR02954 (W * V) - meanCLM_STR02954 W * meanCLM_STR02954 V +
        eta * meanCLM_STR02954 (φ * W) * meanCLM_STR02954 (φ * V)) 0 := by
    change HasDerivAt (fun z : ℝ => z * C W V z + eta * (μ φ z * C φ V z)) _ 0 at hd
    apply hd.congr_deriv
    simp only [id_eq, one_mul, zero_mul, add_zero, hm0, hm', C, μ, hR0, mul_one,
      hφ0, sub_zero]
    ring
  have hfun : (fun z : ℝ => fderiv ℝ (polynomialRangeGap (0, 0)) (z • w) v) =
      fun z : ℝ => z * C W V z + eta * (μ φ z * C φ V z) := by
    funext z
    rw [polynomialRangeGap_fderiv]
    simp only [hL, map_zero, map_smul, eulerCov, eulerMean, eulerDensity, zero_add,
      smul_mul_assoc, map_smul, smul_eq_mul, C, μ, W, V, φ, R]
    ring
  rw [hfun]
  exact hd'

private theorem fixed_gap_smooth (p : ℝ × ℝ) : ContDiff ℝ ∞ (polynomialRangeGap p) := by
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  let φ := e0_STR02955 (polynomialRangeFeature p)
  have he : polynomialRangeGap p = fun u : PeriodicC2_STR02969 =>
      eulerEntropy L u + (eta / 2) * (eulerMean L u φ) ^ 2 := by
    funext u
    change eulerEntropy L u + eta * (eulerMean L u φ) ^ 2 / 2 = _
    ring
  rw [he]
  exact (entropy_smooth L).add (contDiff_const.mul ((mean_smooth L φ).pow 2))

private theorem hessian_line (F : PeriodicC2_STR02969 → ℝ) (hF : ContDiff ℝ ∞ F)
    (w v : PeriodicC2_STR02969) :
    HasDerivAt (fun z : ℝ => fderiv ℝ F (z • w) v)
      (fderiv ℝ (fderiv ℝ F) 0 w v) 0 := by
  have hDF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hs : HasDerivAt (fun z : ℝ => z • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hd := (hDF 0).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hs (by simp)
  convert hd.clm_apply (hasDerivAt_const (0 : ℝ) v) using 1 <;>
    simp only [Function.comp_apply, map_zero, zero_add, add_zero]

/-- The actual mixed Haar-origin Hessian on the full C2 chart. The first term is
the Haar covariance, and the second is the genuine centered nonlocal correction. -/
theorem polynomialRangeGap_hessian_origin (w v : PeriodicC2_STR02969) :
    fderiv ℝ (fderiv ℝ (polynomialRangeGap (0, 0))) 0 w v =
      meanCLM_STR02954 (e0_STR02955 w * e0_STR02955 v) -
        meanCLM_STR02954 (e0_STR02955 w) * meanCLM_STR02954 (e0_STR02955 v) +
        eta * meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0)) * e0_STR02955 w) *
          meanCLM_STR02954 (e0_STR02955 (polynomialRangeFeature (0, 0)) * e0_STR02955 v) := by
  exact (hessian_line (polynomialRangeGap (0, 0)) (fixed_gap_smooth (0, 0)) w v).unique (origin_line w v)

end DGPS.Examples.PolynomialSpecies
