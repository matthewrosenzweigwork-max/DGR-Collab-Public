import DGPS.Examples.PolynomialSpeciesEuler

/-! Spatial differentiation and periodic integration by parts for the actual
moving polynomial logarithmic chart. No unperturbed drift is substituted. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.PositiveRankOne
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux

namespace DGPS.Examples.PolynomialSpecies

private theorem logReference_smooth (h : ℝ) :
    ContDiff ℝ ∞ (polynomialLogReference h).val := by
  change IsSmoothAngular (fun θ => Real.log ((polynomialRankOne h).q (angEquiv.symm θ)))
  apply (isSmoothPeriodic_comp_iff _).1
  convert (polynomialRankOne h).log_smooth using 1
  ext x
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]

private theorem logDerivative_holder (h : ℝ) :
    IsPerHolder_STR02968 (1 / 2) (deriv (polynomialLogReference h).val) := by
  have hs := (contDiff_infty_iff_deriv.1 (logReference_smooth h)).2
  have hp := DGPS.Circle.StationaryFlux.periodic_deriv (polynomialLogReference h).isPerHolder.1
  have hb := bdd_of_periodic_continuous_STR02953
    (DGPS.Circle.StationaryFlux.periodic_deriv hp)
    ((contDiff_infty_iff_deriv.1 hs).2).continuous
  exact mkHolder_STR02955 (c0_of_deriv_STR02953 half_pos_STR02968 (by norm_num)
    hp (hs.differentiable (by simp)) hb).1

/-- Actual angular logarithmic derivative of the moving reference. -/
def polynomialLogDerivative (h : ℝ) : PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (deriv (polynomialLogReference h).val) (logDerivative_holder h)

/-- Spatial derivative of the actual normalized chart density. -/
theorem polynomialEuler_density_hasDerivAt (h : ℝ) (u : PeriodicC2_STR02969) (t : ℝ) :
    HasDerivAt (eulerDensity (polynomialLogReference h) u).val
      ((eulerDensity (polynomialLogReference h) u).val t *
        ((polynomialLogDerivative h).val t + deriv u.val t)) t := by
  let L := polynomialLogReference h
  have hl := ((logReference_smooth h).differentiable (by simp) t).hasDerivAt
  have hd := ((hl.add (u.isC2.2.1 t).hasDerivAt).exp).div_const
    (Z_STR02954 (0, L + e0_STR02955 u))
  have he : (eulerDensity L u).val = fun s =>
      Real.exp (L.val s + u.val s) / Z_STR02954 (0, L + e0_STR02955 u) := by
    funext s
    rw [eulerDensity, rho_val_STR02954]
    simp only [rhoT_STR02901, zero_mul, zero_add, PeriodicHolder_STR02968.val_add,
      Pi.add_apply, e0_val_STR02955, Z_eq_meanT_STR02954]
  rw [he]
  convert hd using 1
  change Real.exp (L.val t + u.val t) / _ *
    (deriv L.val t + deriv u.val t) = _
  dsimp only [L, Pi.add_apply]
  ring

/-- A spatial derivative has zero periodic Haar mean, in the actual chart density. -/
theorem polynomialEuler_weighted_ibp (h : ℝ) (u v : PeriodicC2_STR02969) :
    meanCLM_STR02954
      (e2_STR02955 u * e0_STR02955 v * eulerDensity (polynomialLogReference h) u +
        e1_STR02955 u * e1_STR02955 v * eulerDensity (polynomialLogReference h) u +
        e1_STR02955 u * e0_STR02955 v * (eulerDensity (polynomialLogReference h) u *
          (polynomialLogDerivative h + e1_STR02955 u))) = 0 := by
  let R := eulerDensity (polynomialLogReference h) u
  let K := e2_STR02955 u * e0_STR02955 v * R +
    e1_STR02955 u * e1_STR02955 v * R +
    e1_STR02955 u * e0_STR02955 v * (R * (polynomialLogDerivative h + e1_STR02955 u))
  have hd : ∀ t, HasDerivAt (fun s => deriv u.val s * v.val s * R.val s) (K.val t) t := by
    intro t
    have hd := (((u.isC2.2.2.1 t).hasDerivAt.mul (v.isC2.2.1 t).hasDerivAt).mul
      (polynomialEuler_density_hasDerivAt h u t))
    convert hd using 1
    simp only [K, R, PeriodicHolder_STR02968.val_add, val_mul_STR02954,
      Pi.add_apply, Pi.mul_apply, e0_val_STR02955, e1_val_STR02955, e2_val_STR02955]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 2 * Real.pi) (fun t _ => hd t)
    (K.isPerHolder.2.1.intervalIntegrable _ _)
  have hpu : deriv u.val (2 * Real.pi) = deriv u.val 0 := by
    simpa using (DGPS.Circle.StationaryFlux.periodic_deriv u.isC2.1) 0
  have hpv : v.val (2 * Real.pi) = v.val 0 := by simpa using v.isC2.1 0
  have hpR : R.val (2 * Real.pi) = R.val 0 := by simpa using R.isPerHolder.1 0
  change meanT_STR02901 K.val = 0
  unfold meanT_STR02901
  rw [hint, hpu, hpv, hpR]
  simp

/-- The true differential Euler potential, in physical units. -/
def polynomialEulerPotential (h r : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  let L := polynomialLogReference h
  let m := eulerMean L u (polynomialEulerFeature h)
  let A := eulerMean L u (polynomialEulerGenerator h)
  let J := eulerMean L u (polynomialEulerGradientSq h)
  DGPS.Circle.AngularNormalization.a0 •
    ((-2 : ℝ) • e2_STR02955 u - (2 : ℝ) • (polynomialLogDerivative h * e1_STR02955 u) -
      e1_STR02955 u * e1_STR02955 u) - (2 * r) • e0_STR02955 u +
    (2 * eta * (A + eta * m * J - r * m)) • polynomialEulerFeature h +
    (2 * eta * m) • polynomialEulerGenerator h +
    (eta ^ 2 * m ^ 2) • polynomialEulerGradientSq h

/-- The centered Euler gradient with respect to the unweighted angular Haar pairing. -/
def polynomialEulerGradient (h r : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  let L := polynomialLogReference h
  eulerDensity L u * (polynomialEulerPotential h r u -
    eulerMean L u (polynomialEulerPotential h r u) • (1 : PeriodicHolder_STR02968))

private theorem weighted_ibp_one (h : ℝ) (u : PeriodicC2_STR02969) :
    meanCLM_STR02954 (e2_STR02955 u * eulerDensity (polynomialLogReference h) u +
      e1_STR02955 u * (eulerDensity (polynomialLogReference h) u *
        (polynomialLogDerivative h + e1_STR02955 u))) = 0 := by
  let R := eulerDensity (polynomialLogReference h) u
  let K := e2_STR02955 u * R + e1_STR02955 u * (R * (polynomialLogDerivative h + e1_STR02955 u))
  have hd : ∀ t, HasDerivAt (fun s => deriv u.val s * R.val s) (K.val t) t := by
    intro t
    convert ((u.isC2.2.2.1 t).hasDerivAt.mul (polynomialEuler_density_hasDerivAt h u t)) using 1
    simp only [K, R, PeriodicHolder_STR02968.val_add, val_mul_STR02954, Pi.add_apply,
      Pi.mul_apply, e1_val_STR02955, e2_val_STR02955]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 2 * Real.pi) (fun t _ => hd t) (K.isPerHolder.2.1.intervalIntegrable _ _)
  have hpu : deriv u.val (2 * Real.pi) = deriv u.val 0 := by
    simpa using (DGPS.Circle.StationaryFlux.periodic_deriv u.isC2.1) 0
  have hpR : R.val (2 * Real.pi) = R.val 0 := by simpa using R.isPerHolder.1 0
  change meanT_STR02901 K.val = 0
  unfold meanT_STR02901
  rw [hint, hpu, hpR]
  simp

private def expectationCLM (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969) :
    PeriodicHolder_STR02968 →L[ℝ] ℝ :=
  meanCLM_STR02954.comp ((ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968).flip (eulerDensity L u))

private theorem expectationCLM_apply (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (f : PeriodicHolder_STR02968) : expectationCLM L u f = eulerMean L u f := rfl

private theorem mean_add (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (f g : PeriodicHolder_STR02968) : eulerMean L u (f + g) = eulerMean L u f + eulerMean L u g :=
  (expectationCLM L u).map_add f g
private theorem mean_sub (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (f g : PeriodicHolder_STR02968) : eulerMean L u (f - g) = eulerMean L u f - eulerMean L u g :=
  (expectationCLM L u).map_sub f g
private theorem mean_smul (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (c : ℝ) (f : PeriodicHolder_STR02968) : eulerMean L u (c • f) = c * eulerMean L u f :=
  (expectationCLM L u).map_smul c f

private theorem cov_add (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (f g v : PeriodicHolder_STR02968) :
    eulerCov L u (f + g) v = eulerCov L u f v + eulerCov L u g v := by
  unfold eulerCov
  rw [add_mul, mean_add, mean_add]
  ring
private theorem cov_sub (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (f g v : PeriodicHolder_STR02968) :
    eulerCov L u (f - g) v = eulerCov L u f v - eulerCov L u g v := by
  unfold eulerCov
  rw [sub_mul, mean_sub, mean_sub]
  ring
private theorem cov_smul (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (c : ℝ) (f v : PeriodicHolder_STR02968) :
    eulerCov L u (c • f) v = c * eulerCov L u f v := by
  unfold eulerCov
  rw [smul_mul_assoc, mean_smul, mean_smul]
  ring

private theorem ibp_covariance_algebra (E : PeriodicHolder_STR02968 →L[ℝ] ℝ)
    (l d dd v w : PeriodicHolder_STR02968)
    (hb : E (dd * v + d * w + d * v * (l + d)) = 0)
    (hb1 : E (dd + d * (l + d)) = 0) :
    2 * E (d * w) + (E ((d * d) * v) - E (d * d) * E v) =
      E (((-2 : ℝ) • dd - (2 : ℝ) • (l * d) - d * d) * v) -
        E ((-2 : ℝ) • dd - (2 : ℝ) • (l * d) - d * d) * E v := by
  have e1 : dd * v + d * w + d * v * (l + d) =
      dd * v + d * w + (l * d) * v + (d * d) * v := by ring
  have e2 : dd + d * (l + d) = dd + l * d + d * d := by ring
  rw [e1] at hb
  rw [e2] at hb1
  simp only [map_add] at hb hb1
  simp only [sub_mul, smul_mul_assoc, map_sub, map_smul, smul_eq_mul]
  nlinarith [congrArg (fun z : ℝ => z * E v) hb1]

private theorem fisher_covariance (h : ℝ) (u v : PeriodicC2_STR02969) :
    2 * eulerMean (polynomialLogReference h) u (e1_STR02955 u * e1_STR02955 v) +
      eulerCov (polynomialLogReference h) u (e1_STR02955 u * e1_STR02955 u) (e0_STR02955 v) =
    eulerCov (polynomialLogReference h) u
      ((-2 : ℝ) • e2_STR02955 u - (2 : ℝ) • (polynomialLogDerivative h * e1_STR02955 u) -
        e1_STR02955 u * e1_STR02955 u) (e0_STR02955 v) := by
  let L := polynomialLogReference h
  let R := eulerDensity L u
  have hb := polynomialEuler_weighted_ibp h u v
  have hb1 := weighted_ibp_one h u
  have he : (e2_STR02955 u * e0_STR02955 v + e1_STR02955 u * e1_STR02955 v +
      e1_STR02955 u * e0_STR02955 v * (polynomialLogDerivative h + e1_STR02955 u)) * R =
      e2_STR02955 u * e0_STR02955 v * R + e1_STR02955 u * e1_STR02955 v * R +
      e1_STR02955 u * e0_STR02955 v * (R * (polynomialLogDerivative h + e1_STR02955 u)) := by ring
  have he1 : (e2_STR02955 u + e1_STR02955 u * (polynomialLogDerivative h + e1_STR02955 u)) * R =
      e2_STR02955 u * R + e1_STR02955 u * (R * (polynomialLogDerivative h + e1_STR02955 u)) := by ring
  have hE := ibp_covariance_algebra (expectationCLM L u) (polynomialLogDerivative h)
    (e1_STR02955 u) (e2_STR02955 u) (e0_STR02955 v) (e1_STR02955 v)
    (by change meanCLM_STR02954 (_ * R) = 0; rw [he]; exact hb)
    (by change meanCLM_STR02954 (_ * R) = 0; rw [he1]; exact hb1)
  exact hE

/-- The explicit weak Euler variation is pairing with the centered true differential gradient. -/
theorem polynomialEuler_eq_strong_pairing (h r : ℝ) (u v : PeriodicC2_STR02969) :
    polynomialEuler h r u v = meanCLM_STR02954 (polynomialEulerGradient h r u * e0_STR02955 v) := by
  have hc : meanCLM_STR02954 (polynomialEulerGradient h r u * e0_STR02955 v) =
      eulerCov (polynomialLogReference h) u (polynomialEulerPotential h r u) (e0_STR02955 v) := by
    let L := polynomialLogReference h
    let K := polynomialEulerPotential h r u
    let R := eulerDensity L u
    have he : R * (K - eulerMean L u K • (1 : PeriodicHolder_STR02968)) * e0_STR02955 v =
        (K * e0_STR02955 v) * R - eulerMean L u K • (e0_STR02955 v * R) := by
      apply ext_STR02954
      funext t
      simp only [PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
        val_mul_STR02954, val_one_STR02954, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      ring
    change meanCLM_STR02954 (R * (K - eulerMean L u K • (1 : PeriodicHolder_STR02968)) *
      e0_STR02955 v) = _
    rw [he, map_sub, map_smul]
    rfl
  rw [hc]
  unfold polynomialEulerPotential
  simp only [cov_add, cov_sub, cov_smul]
  have hf := fisher_covariance h u v
  simp only [cov_sub, cov_smul] at hf
  unfold polynomialEuler
  dsimp only
  rw [hf]

/-- The full Frechet derivative is the unweighted angular pairing with the actual centered Euler map. -/
theorem polynomialChartDeficit_fderiv_strong (h r : ℝ) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (polynomialChartDeficit h r) u v =
      meanCLM_STR02954 (polynomialEulerGradient h r u * e0_STR02955 v) := by
  rw [polynomialChartDeficit_fderiv, polynomialEuler_eq_strong_pairing]

end DGPS.Examples.PolynomialSpecies
