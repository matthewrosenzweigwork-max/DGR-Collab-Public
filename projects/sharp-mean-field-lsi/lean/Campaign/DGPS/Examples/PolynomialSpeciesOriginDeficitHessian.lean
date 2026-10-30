import DGPS.Examples.PolynomialSpeciesOriginPotential
import DGPS.Examples.PolynomialSpeciesRangeQuadratic
import DGPS.Examples.PolynomialSpeciesRangeStationarity
import DGPS.Examples.PolynomialSpeciesRangeGraphDerivative

/-! The actual reduced deficit has zero amplitude Hessian at the Haar origin.
The full Euler kernel is derived before the Hessian calculation; a projected
range kernel alone would not suffice. All graph transport concerns the SAME
supplied implicit correction and uses its genuinely produced first jet. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- The FULL actual centered Euler map, not only its complement projection,
has zero first derivative in every first-harmonic amplitude direction. -/
theorem polynomialOriginEuler_first_amplitude_zero (a b : ℝ) :
    HasDerivAt (fun z : ℝ => polynomialRangeEuler (0, 0)
      DGPS.Circle.AngularNormalization.a0
        (z • (a • cosC2_STR02915 + b • sinC2_STR02915))) 0 0 := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  let V := e0_STR02955 v
  let φ := e0_STR02955 polynomialOriginMode
  let j := polynomialRangeGradientSq (0, 0)
  let R := fun z : ℝ => rho_STR02954 (0, z • V)
  let m := fun z : ℝ => meanCLM_STR02954 (φ * R z)
  let J := fun z : ℝ => meanCLM_STR02954 (j * R z)
  let c := fun z : ℝ => 2 * eta * (7 * DGPS.Circle.AngularNormalization.a0 + eta * J z)
  have hR : ContDiff ℝ ∞ R := rho_smooth_STR02954.comp
    (contDiff_const.prodMk (contDiff_id.smul contDiff_const))
  have hJ : ContDiff ℝ ∞ J := meanCLM_STR02954.contDiff.comp (contDiff_const.mul hR)
  have hc : ContDiff ℝ ∞ c := contDiff_const.mul (contDiff_const.add (contDiff_const.mul hJ))
  have hm0 : m 0 = 0 := by
    simpa only [m, R, zero_smul, rho_zero_STR02955, mul_one, φ] using polynomialOriginFeature_mean_zero
  have hR1 : HasDerivAt R V 0 := by
    simpa only [zero_add, rho_zero_STR02955, mul_one, one_mul, V, v,
      polynomial_first_amplitude_centered a b, zero_smul, sub_zero] using
      hasDerivAt_rho_path_STR02949 0 (0 : PeriodicHolder_STR02968) V
  have hm1 : HasDerivAt m 0 0 := by
    have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) φ).mul hR1)
    have hz : meanCLM_STR02954 (φ * V) = 0 := by
      simpa only [φ, V, v, ← polynomialOriginFeature_eq] using
        polynomial_first_amplitude_feature_moment a b
    convert hd using 1 <;>
      simp only [m, Function.comp_def, Pi.mul_apply, zero_mul, zero_add, hz]
  let K := fun z : ℝ => (-DGPS.Circle.AngularNormalization.a0 * z ^ 2) •
    (e1_STR02955 v * e1_STR02955 v) + (c z * m z) • φ + (eta ^ 2 * m z ^ 2) • j
  have hK0 : K 0 = 0 := by
    simp only [K, hm0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_smul, zero_add, add_zero]
  have hK1 : HasDerivAt K 0 0 := by
    have hz : HasDerivAt (fun z : ℝ => -DGPS.Circle.AngularNormalization.a0 * z ^ 2) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (-DGPS.Circle.AngularNormalization.a0)
    have hd := ((hz.smul_const (e1_STR02955 v * e1_STR02955 v)).add
      (((hc.differentiable (by simp) 0).hasDerivAt.mul hm1).smul_const φ)).add
        (((hm1.pow 2).const_mul (eta ^ 2)).smul_const j)
    change HasDerivAt K _ 0 at hd
    simpa only [hm0, zero_mul, mul_zero, zero_add, zero_smul, add_zero,
      pow_one, mul_one] using hd
  have hR0 : R 0 = 1 := by simp only [R, zero_smul, rho_zero_STR02955]
  have hN := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK1.mul hR1)
  simp only [Function.comp_def, hK0, hR0, zero_mul, zero_add, add_zero, mul_one, map_zero] at hN
  have hd := hR1.mul (hK1.sub (hN.smul_const (1 : PeriodicHolder_STR02968)))
  change HasDerivAt (fun z : ℝ => R z *
    (K z - meanCLM_STR02954 (K z * R z) • (1 : PeriodicHolder_STR02968))) _ 0 at hd
  simp only [Pi.sub_apply, Pi.mul_apply, hK0, hR0, zero_mul, map_zero, zero_smul, sub_zero, mul_zero, zero_add, one_mul, add_zero] at hd
  have hK (z : ℝ) : polynomialRangeEulerPotential (0, 0)
      DGPS.Circle.AngularNormalization.a0 (z • v) = K z := by
    rw [polynomialOriginPotential_amplitude]
    simp only [K, c, m, J, R, eulerMean, eulerDensity, map_smul, zero_add, φ, j, v, V]
  have he : (fun z : ℝ => polynomialRangeEuler (0, 0)
      DGPS.Circle.AngularNormalization.a0 (z • v)) =
      fun z : ℝ => R z * (K z - meanCLM_STR02954 (K z * R z) • 1) := by
    funext z
    simp only [polynomialRangeEuler, eulerMean, eulerDensity,
      show polynomialRangeLogWeight (0, 0) = 0 by simp [polynomialRangeLogWeight],
      map_zero, map_smul, zero_add, R, V, hK]
  change HasDerivAt (fun z : ℝ => polynomialRangeEuler (0, 0)
    DGPS.Circle.AngularNormalization.a0 (z • v)) 0 0
  rw [he]
  exact hd

private def originDeficit : PeriodicC2_STR02969 → ℝ :=
  polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0

private theorem originDeficit_smooth : ContDiff ℝ ∞ originDeficit := by
  let V : PolynomialEulerInput → ℝ := fun q => polynomialRangeDeficit q.1 q.2.1 q.2.2
  let q : PeriodicC2_STR02969 → PolynomialEulerInput := fun u =>
    ((0,0), DGPS.Circle.AngularNormalization.a0, u)
  have hV : ContDiff ℝ ∞ V := polynomialRangeDeficit_smooth
  have hq : ContDiff ℝ ∞ q := contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have he : originDeficit = V ∘ q := rfl
  rw [he]
  exact hV.comp hq

private theorem originDeficit_pairing (u w : PeriodicC2_STR02969) :
    fderiv ℝ originDeficit u w = meanCLM_STR02954
      (polynomialRangeEuler (0, 0) DGPS.Circle.AngularNormalization.a0 u * e0_STR02955 w) := by
  have hF : originDeficit = polynomialChartDeficit 0 DGPS.Circle.AngularNormalization.a0 := by
    funext q
    change polynomialRangeDeficit (0,0) DGPS.Circle.AngularNormalization.a0 q = _
    simpa only [polynomial_root_origin] using
      polynomialRangeDeficit_actual 0 DGPS.Circle.AngularNormalization.a0 q
  have hE := polynomialRangeEuler_actual 0 DGPS.Circle.AngularNormalization.a0 u
  rw [polynomial_root_origin] at hE
  rw [hF, polynomialChartDeficit_fderiv_strong, hE]

/-- The actual full physical deficit Hessian kills every first harmonic
against EVERY chart direction. No Hessian or quartic coefficient is a premise. -/
theorem polynomialRangeDeficit_first_amplitude_hessian_zero (a b : ℝ)
    (w : PeriodicC2_STR02969) :
    fderiv ℝ (fderiv ℝ (polynomialRangeDeficit (0, 0)
      DGPS.Circle.AngularNormalization.a0)) 0
      (a • cosC2_STR02915 + b • sinC2_STR02915) w = 0 := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  have hDF : DifferentiableAt ℝ (fderiv ℝ originDeficit) 0 :=
    ((originDeficit_smooth.fderiv_right (m := 1) (by simp)).differentiable (by simp)) 0
  have hv : HasDerivAt (fun z : ℝ => z • v) v 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hd := (hDF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hv (by simp)).clm_apply
    (hasDerivAt_const (0 : ℝ) w)
  have he := polynomialOriginEuler_first_amplitude_zero a b
  have hp := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (he.mul (hasDerivAt_const (0 : ℝ) (e0_STR02955 w)))
  have hfun : (fun z : ℝ => fderiv ℝ originDeficit (z • v) w) =
      fun z : ℝ => meanCLM_STR02954
        (polynomialRangeEuler (0, 0) DGPS.Circle.AngularNormalization.a0 (z • v) * e0_STR02955 w) :=
    funext fun z => originDeficit_pairing (z • v) w
  change HasDerivAt (fun z : ℝ => fderiv ℝ originDeficit (z • v) w) _ 0 at hd
  have hp0 : HasDerivAt (fun z : ℝ => fderiv ℝ originDeficit (z • v) w) 0 0 := by
    rw [hfun]
    simpa only [Function.comp_def, Pi.mul_apply, v, zero_mul, mul_zero, add_zero, zero_add, map_zero] using hp
  change fderiv ℝ (fderiv ℝ originDeficit) 0 v w = 0
  simpa only [ContinuousLinearMap.comp_apply, Function.comp_apply, map_zero, zero_add, add_zero] using
    hd.unique hp0

private theorem critical_second_chain (G : PeriodicC2_STR02969 → ℝ)
    (hG : ContDiff ℝ ∞ G) (hDG : fderiv ℝ G 0 = 0)
    (L : ℝ × ℝ → PeriodicC2_STR02969) (W : Set (ℝ × ℝ))
    (hW : IsOpen W) (h0W : (0 : ℝ × ℝ) ∈ W)
    (hL : ContDiffOn ℝ ∞ L W) (hL0 : L 0 = 0) (x y : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (G ∘ L)) 0 x y =
      fderiv ℝ (fderiv ℝ G) 0 (fderiv ℝ L 0 x) (fderiv ℝ L 0 y) := by
  have hLd := (hL.contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hDFG : DifferentiableAt ℝ (fderiv ℝ G) (L 0) :=
    ((hG.fderiv_right (m := 1) (by simp)).differentiable (by simp)) _
  have hDL : DifferentiableAt ℝ (fderiv ℝ L) 0 :=
    (((hL.fderiv_of_isOpen hW (m := 1) (by simp)).contDiffAt
      (hW.mem_nhds h0W)).differentiableAt (by simp))
  have he : fderiv ℝ (G ∘ L) =ᶠ[𝓝 0]
      (fun z => (fderiv ℝ G (L z)).comp (fderiv ℝ L z)) := by
    filter_upwards [hW.mem_nhds h0W] with z hz
    exact fderiv_comp z (hG.differentiable (by simp) _)
      ((hL.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp))
  have hc := hDFG.hasFDerivAt.comp 0 hLd.hasFDerivAt
  have hd := hc.clm_comp hDL.hasFDerivAt
  change HasFDerivAt (fun z => (fderiv ℝ G (L z)).comp (fderiv ℝ L z)) _ 0 at hd
  rw [he.fderiv_eq, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, Function.comp_apply, hL0, hDG,
    ContinuousLinearMap.zero_apply, zero_add]

/-- The SAME graph supplied by the actual IFT has zero reduced amplitude
Hessian at the actual origin. The first-jet facts here are supplied by
`exists_polynomial_common_range_graph`; no reduced Hessian, radial estimate,
quartic bound, selected-root derivative or cos3-model identity is assumed. -/
theorem polynomialReducedDeficit_amplitude_hessian_origin_zero
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ =>
      polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0
        (x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915 +
          (ψ (x.1, x.2, (0, 0), 0) : PeriodicC2_STR02969)))) 0 = 0 := by
  let q := fun x : ℝ × ℝ => ((x.1, x.2, (0, 0), 0) : PolynomialRangeParameters)
  let W := q ⁻¹' U
  let L := fun x : ℝ × ℝ => x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915 +
    (ψ (q x) : PeriodicC2_STR02969)
  let A : (ℝ × ℝ) →L[ℝ] PeriodicC2_STR02969 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cosC2_STR02915 +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight sinC2_STR02915
  have hq : ContDiff ℝ ∞ q := by dsimp only [q]; fun_prop
  have hq0 : q 0 = 0 := by ext <;> rfl
  have hW : IsOpen W := hU.preimage hq.continuous
  have h0W : (0 : ℝ × ℝ) ∈ W := by change q 0 ∈ U; rw [hq0]; exact h0U
  have hΦ : ContDiffOn ℝ ∞ (fun x => ψ (q x)) W :=
    hψ.comp hq.contDiffOn (fun _ hx => hx)
  have hlin : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915) := by fun_prop
  have hL : ContDiffOn ℝ ∞ L W :=
    hlin.contDiffOn.add (E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ)
  have hL0 : L 0 = 0 := by
    dsimp only [L]
    rw [hq0, hψ0]
    simp
  have hχd := (hΦ.contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hEc := E_STR02969.subtypeL.hasFDerivAt.comp 0 hχd.hasFDerivAt
  have hχ : fderiv ℝ (fun x => ψ (q x)) 0 = 0 := hamp
  rw [hχ] at hEc
  have hDL : fderiv ℝ L 0 = A := by
    have hd := A.hasFDerivAt.add hEc
    simp only [ContinuousLinearMap.comp_zero, add_zero] at hd
    exact hd.fderiv
  have hfun : (fun x : ℝ × ℝ =>
      polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0
        (x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915 +
          (ψ (x.1, x.2, (0, 0), 0) : PeriodicC2_STR02969))) = originDeficit ∘ L := rfl
  rw [hfun]
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  change fderiv ℝ (fderiv ℝ (originDeficit ∘ L)) 0 x y = 0
  rw [critical_second_chain originDeficit originDeficit_smooth
    (polynomialRangeDeficit_fderiv_zero (0, 0) DGPS.Circle.AngularNormalization.a0)
    L W hW h0W hL hL0, hDL]
  exact polynomialRangeDeficit_first_amplitude_hessian_zero x.1 x.2 (A y)

end DGPS.Examples.PolynomialSpecies
