import DGPS.Examples.PolynomialSpeciesResidualBound
import DGPS.Frontier.STR029.T48
import DGPS.Frontier.STR029.T55
import DGPS.Circle.StationaryFlux

/-! First variation of the actual interacting polynomial functional in the normalized
logarithmic chart. The reference and the generator observable move with the actual
polynomial equilibrium. No feature eigenfunction identity is used. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.PositiveRankOne
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux

namespace DGPS.Examples.PolynomialSpecies

private theorem smoothAngular_holder {f : AngCircle → ℝ} (hf : IsSmoothAngular f) :
    IsPerHolder_STR02968 (1 / 2) (lift f) := by
  have hd : Differentiable ℝ (lift f) := hf.differentiable (by simp)
  have hdc : Continuous (deriv (lift f)) := ((contDiff_infty_iff_deriv.1 hf).2).continuous
  have hb := bdd_of_periodic_continuous_STR02953
    (DGPS.Circle.StationaryFlux.periodic_deriv (lift_periodic f)) hdc
  exact mkHolder_STR02955 (c0_of_deriv_STR02953 half_pos_STR02968 (by norm_num)
    (lift_periodic f) hd hb).1

private def torusHolder (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) :
    PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (lift (f ∘ angEquiv.symm)) (by
    apply smoothAngular_holder
    apply (isSmoothPeriodic_comp_iff _).1
    convert hf using 1
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply])

/-- The logarithm of the actual moving equilibrium, in the existing angular Holder carrier. -/
def polynomialLogReference (h : ℝ) : PeriodicHolder_STR02968 :=
  torusHolder _ (polynomialRankOne h).log_smooth

/-- The actual centered feature, without an eigenfunction replacement. -/
def polynomialEulerFeature (h : ℝ) : PeriodicHolder_STR02968 :=
  torusHolder _ (polynomialRankOne h).φ_smooth

private theorem rankOne_Aq_smooth (M : RankOneModel) : IsSmoothPeriodic M.Aq := by
  exact (M.dφ_smooth.isSmoothPeriodic_coordPartial 0).neg.sub
    ((M.log_smooth.isSmoothPeriodic_coordPartial 0).mul M.dφ_smooth)

/-- The true physical weighted generator of the actual feature. -/
def polynomialEulerGenerator (h : ℝ) : PeriodicHolder_STR02968 :=
  torusHolder _ (rankOne_Aq_smooth (polynomialRankOne h))

/-- The squared physical feature gradient. -/
def polynomialEulerGradientSq (h : ℝ) : PeriodicHolder_STR02968 :=
  torusHolder (fun x => (polynomialRankOne h).dφ x ^ 2)
    ((polynomialRankOne h).dφ_smooth.pow 2)

/-- Normalized density for an arbitrary fixed logarithmic reference in the same carrier.
For the polynomial model the reference is `polynomialLogReference h`. -/
def eulerDensity (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969) :
    PeriodicHolder_STR02968 := rho_STR02954 (0, L + e0_STR02955 u)

def eulerMean (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (f : PeriodicHolder_STR02968) : ℝ := meanCLM_STR02954 (f * eulerDensity L u)

def eulerCov (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (f g : PeriodicHolder_STR02968) : ℝ :=
  eulerMean L u (f * g) - eulerMean L u f * eulerMean L u g

/-- Pointwise identification with the actual normalized log-density chart. -/
theorem polynomialEuler_density_val (h : ℝ) (u : PeriodicC2_STR02969) (t : ℝ) :
    (eulerDensity (polynomialLogReference h) u).val t =
      ((polynomialRankOne h).q (angEquiv.symm (t : AngCircle)) * Real.exp (u.val t)) /
        meanT_STR02901 (fun s => (polynomialRankOne h).q (angEquiv.symm (s : AngCircle)) *
          Real.exp (u.val s)) := by
  rw [eulerDensity, rho_val_STR02954]
  unfold rhoT_STR02901
  simp only [zero_mul, zero_add, PeriodicHolder_STR02968.val_add, Pi.add_apply,
    e0_val_STR02955]
  change Real.exp (Real.log ((polynomialRankOne h).q (angEquiv.symm (t : AngCircle))) +
      u.val t) / meanT_STR02901 (fun s => Real.exp
        (Real.log ((polynomialRankOne h).q (angEquiv.symm (s : AngCircle))) + u.val s)) = _
  simp_rw [Real.exp_add, Real.exp_log ((polynomialRankOne h).q_pos _)]

private theorem density_smooth (L : PeriodicHolder_STR02968) :
    ContDiff ℝ ∞ (eulerDensity L) :=
  rho_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff))

private theorem mean_smooth (L : PeriodicHolder_STR02968)
    (F : PeriodicC2_STR02969 → PeriodicHolder_STR02968) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun u => eulerMean L u (F u)) :=
  meanCLM_STR02954.contDiff.comp (hF.mul (density_smooth L))

private theorem density_fderiv (L : PeriodicHolder_STR02968) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (eulerDensity L) u v = eulerDensity L u *
      (e0_STR02955 v - eulerMean L u (e0_STR02955 v) • (1 : PeriodicHolder_STR02968)) := by
  have hd := (hasFDerivAt_rho_STR02948 0 (L + e0_STR02955 u)).comp u
    (e0_STR02955.hasFDerivAt.const_add L)
  change HasFDerivAt (eulerDensity L) _ u at hd
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  rw [← (hasFDerivAt_rho_STR02948 0 (L + e0_STR02955 u)).fderiv,
    (str029_48_derivative_normalized_density 0 (L + e0_STR02955 u) (e0_STR02955 v)).2]
  rfl

/-- Differentiation of normalized expectation includes the covariance term. -/
theorem eulerMean_fderiv (L : PeriodicHolder_STR02968)
    (F : PeriodicC2_STR02969 → PeriodicHolder_STR02968) (hF : ContDiff ℝ ∞ F)
    (u v : PeriodicC2_STR02969) :
    fderiv ℝ (fun w => eulerMean L w (F w)) u v =
      eulerMean L u (fderiv ℝ F u v) + eulerCov L u (F u) (e0_STR02955 v) := by
  have hd := meanCLM_STR02954.hasFDerivAt.comp u
    (((hF.differentiable (by simp) u).hasFDerivAt).mul
      (((density_smooth L).differentiable (by simp) u).hasFDerivAt))
  change HasFDerivAt (fun w => eulerMean L w (F w)) _ u at hd
  rw [hd.fderiv]
  change meanCLM_STR02954 (F u * fderiv ℝ (eulerDensity L) u v +
    eulerDensity L u * fderiv ℝ F u v) = _
  rw [density_fderiv]
  have he : F u * (eulerDensity L u *
        (e0_STR02955 v - eulerMean L u (e0_STR02955 v) • (1 : PeriodicHolder_STR02968))) +
      eulerDensity L u * fderiv ℝ F u v =
      fderiv ℝ F u v * eulerDensity L u +
        (F u * e0_STR02955 v) * eulerDensity L u -
          eulerMean L u (e0_STR02955 v) • (F u * eulerDensity L u) := by
    apply ext_STR02954
    funext t
    simp only [PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [he, map_sub, map_add, map_smul]
  unfold eulerCov eulerMean
  simp only [smul_eq_mul]
  ring

private theorem mean_const_fderiv (L f : PeriodicHolder_STR02968)
    (u v : PeriodicC2_STR02969) :
    fderiv ℝ (fun w => eulerMean L w f) u v = eulerCov L u f (e0_STR02955 v) := by
  simpa [eulerMean] using eulerMean_fderiv L (fun _ => f) contDiff_const u v

/-- Relative entropy in the normalized logarithmic chart. -/
def eulerEntropy (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969) : ℝ :=
  eulerMean L u (e0_STR02955 u) - Real.log (Z_STR02954 (0, L + e0_STR02955 u)) +
    Real.log (Z_STR02954 (0, L))

private theorem entropy_smooth (L : PeriodicHolder_STR02968) :
    ContDiff ℝ ∞ (eulerEntropy L) := by
  exact ((mean_smooth L _ e0_STR02955.contDiff).sub
    (logZ_smooth_STR02954.comp (contDiff_const.prodMk
      (contDiff_const.add e0_STR02955.contDiff)))).add contDiff_const

/-- Entropy differentiation cancels the derivative of the normalizing partition function. -/
theorem eulerEntropy_fderiv (L : PeriodicHolder_STR02968) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (eulerEntropy L) u v = eulerCov L u (e0_STR02955 u) (e0_STR02955 v) := by
  have hE := (mean_smooth L _ e0_STR02955.contDiff).differentiable (by simp) u
  have hZ : DifferentiableAt ℝ (fun w : PeriodicC2_STR02969 =>
      Real.log (Z_STR02954 (0, L + e0_STR02955 w))) u :=
    (logZ_smooth_STR02954.comp (contDiff_const.prodMk
      (contDiff_const.add e0_STR02955.contDiff))).differentiable (by simp) u
  have hd := (hasFDerivAt_logZ_STR02948 0 (L + e0_STR02955 u)).comp u
    (e0_STR02955.hasFDerivAt.const_add L)
  change HasFDerivAt (fun w : PeriodicC2_STR02969 =>
    Real.log (Z_STR02954 (0, L + e0_STR02955 w))) _ u at hd
  have he : fderiv ℝ (fun w : PeriodicC2_STR02969 =>
      Real.log (Z_STR02954 (0, L + e0_STR02955 w))) u v =
      eulerMean L u (e0_STR02955 v) := by
    rw [hd.fderiv, ContinuousLinearMap.comp_apply,
      ← (hasFDerivAt_logZ_STR02948 0 (L + e0_STR02955 u)).fderiv,
      (str029_48_derivative_normalized_density 0 (L + e0_STR02955 u) (e0_STR02955 v)).1]
    rfl
  unfold eulerEntropy
  rw [fderiv_add_const, fderiv_fun_sub hE hZ, ContinuousLinearMap.sub_apply,
    eulerMean_fderiv L _ e0_STR02955.contDiff, he]
  simp

/-- Physical relative Fisher information: the chart derivative is angular. -/
def eulerFisher (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969) : ℝ :=
  DGPS.Circle.AngularNormalization.a0 * eulerMean L u (e1_STR02955 u * e1_STR02955 u)

private theorem fisher_smooth (L : PeriodicHolder_STR02968) : ContDiff ℝ ∞ (eulerFisher L) :=
  contDiff_const.mul (mean_smooth L _ (e1_STR02955.contDiff.mul e1_STR02955.contDiff))

theorem eulerFisher_fderiv (L : PeriodicHolder_STR02968) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (eulerFisher L) u v = DGPS.Circle.AngularNormalization.a0 *
      (2 * eulerMean L u (e1_STR02955 u * e1_STR02955 v) +
        eulerCov L u (e1_STR02955 u * e1_STR02955 u) (e0_STR02955 v)) := by
  have hF := mean_smooth L _ (e1_STR02955.contDiff.mul e1_STR02955.contDiff)
  unfold eulerFisher
  rw [fderiv_const_mul (hF.differentiable (by simp) u), ContinuousLinearMap.smul_apply,
    eulerMean_fderiv L _ (e1_STR02955.contDiff.mul e1_STR02955.contDiff)]
  have hd := (e1_STR02955.hasFDerivAt (x := u)).mul e1_STR02955.hasFDerivAt
  change HasFDerivAt (fun w : PeriodicC2_STR02969 => e1_STR02955 w * e1_STR02955 w) _ u at hd
  rw [hd.fderiv]
  change _ * (eulerMean L u (e1_STR02955 u * e1_STR02955 v +
    e1_STR02955 u * e1_STR02955 v) + _) = _
  unfold eulerMean
  rw [add_mul, map_add]
  ring

/-- The actual nonlocal deficit, with the true generator and squared-gradient observables. -/
def polynomialChartDeficit (h r : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  let L := polynomialLogReference h
  let m := eulerMean L u (polynomialEulerFeature h)
  let A := eulerMean L u (polynomialEulerGenerator h)
  let J := eulerMean L u (polynomialEulerGradientSq h)
  eulerFisher L u + 2 * eta * m * A + eta ^ 2 * m ^ 2 * J -
    2 * r * (eulerEntropy L u + eta * m ^ 2 / 2)

/-- The weak Euler map. Every normalizing covariance and nonlocal term is retained. -/
def polynomialEuler (h r : ℝ) (u v : PeriodicC2_STR02969) : ℝ :=
  let L := polynomialLogReference h
  let p := polynomialEulerFeature h
  let B := polynomialEulerGenerator h
  let j := polynomialEulerGradientSq h
  let m := eulerMean L u p
  let A := eulerMean L u B
  let J := eulerMean L u j
  DGPS.Circle.AngularNormalization.a0 *
    (2 * eulerMean L u (e1_STR02955 u * e1_STR02955 v) +
      eulerCov L u (e1_STR02955 u * e1_STR02955 u) (e0_STR02955 v)) -
    2 * r * eulerCov L u (e0_STR02955 u) (e0_STR02955 v) +
    2 * eta * (A + eta * m * J - r * m) * eulerCov L u p (e0_STR02955 v) +
    2 * eta * m * eulerCov L u B (e0_STR02955 v) +
    eta ^ 2 * m ^ 2 * eulerCov L u j (e0_STR02955 v)

/-- Genuine Frechet first variation on the existing periodic C2 Banach space. -/
theorem polynomialChartDeficit_fderiv (h r : ℝ) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (polynomialChartDeficit h r) u v = polynomialEuler h r u v := by
  let L := polynomialLogReference h
  let m := fun w => eulerMean L w (polynomialEulerFeature h)
  let A := fun w => eulerMean L w (polynomialEulerGenerator h)
  let J := fun w => eulerMean L w (polynomialEulerGradientSq h)
  have hm := ((mean_smooth L (fun _ => polynomialEulerFeature h) contDiff_const).differentiable (by simp) u).hasFDerivAt
  have hA := ((mean_smooth L (fun _ => polynomialEulerGenerator h) contDiff_const).differentiable (by simp) u).hasFDerivAt
  have hJ := ((mean_smooth L (fun _ => polynomialEulerGradientSq h) contDiff_const).differentiable (by simp) u).hasFDerivAt
  have hI := ((fisher_smooth L).differentiable (by simp) u).hasFDerivAt
  have hH := ((entropy_smooth L).differentiable (by simp) u).hasFDerivAt
  have hd := ((hI.add ((hm.const_mul (2 * eta)).mul hA)).add
    (((hm.pow 2).const_mul (eta ^ 2)).mul hJ)).sub
      ((hH.add ((hm.pow 2).const_mul (eta / 2))).const_mul (2 * r))
  change fderiv ℝ (fun w => eulerFisher L w + 2 * eta * m w * A w +
    eta ^ 2 * m w ^ 2 * J w - 2 * r * (eulerEntropy L w + eta * m w ^ 2 / 2)) u v = _
  have he : (fun w => eulerFisher L w + 2 * eta * m w * A w +
      eta ^ 2 * m w ^ 2 * J w - 2 * r * (eulerEntropy L w + eta * m w ^ 2 / 2)) =
      (fun w => eulerFisher L w + (2 * eta * m w) * A w +
        (eta ^ 2 * m w ^ 2) * J w - (2 * r) * (eulerEntropy L w + (eta / 2) * m w ^ 2)) := by
    funext w; ring
  change HasFDerivAt (fun w => eulerFisher L w + (2 * eta * m w) * A w +
    (eta ^ 2 * m w ^ 2) * J w - (2 * r) * (eulerEntropy L w + (eta / 2) * m w ^ 2)) _ u at hd
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [eulerFisher_fderiv, eulerEntropy_fderiv]
  simp only [mean_const_fderiv]
  unfold polynomialEuler
  dsimp only [L, m, A, J]
  ring

private theorem mean_torusHolder (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) :
    meanCLM_STR02954 (torusHolder f hf) = ∫ x, f x ∂haar 1 := by
  change meanT_STR02901 (lift (f ∘ angEquiv.symm)) = _
  unfold meanT_STR02901
  rw [integral_lift_period]
  have he : ∫ x, f x ∂haar 1 = ∫ θ, f (angEquiv.symm θ) ∂angHaar := by
    simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
      integral_comp_angEquiv (f ∘ angEquiv.symm)
  rw [he]
  field_simp <;> rfl

/-- At zero chart displacement the density is the actual moving reference, for every field. -/
theorem polynomialEuler_density_zero (h : ℝ) :
    eulerDensity (polynomialLogReference h) 0 =
      torusHolder (polynomialRankOne h).q (polynomialRankOne h).q_smooth := by
  let M := polynomialRankOne h
  have he : exp (polynomialLogReference h) = torusHolder M.q M.q_smooth := by
    apply ext_STR02954
    funext t
    rw [exp_val_STR02954]
    change Real.exp (Real.log (M.q (angEquiv.symm (t : AngCircle)))) = _
    exact Real.exp_log (M.q_pos _)
  have hZ : Z_STR02954 (0, polynomialLogReference h) = 1 := by
    simp only [Z_STR02954, zero_smul, zero_add, he]
    rw [mean_torusHolder, M.q_mass]
  simp only [eulerDensity, map_zero, add_zero, rho_STR02954, zero_smul, zero_add,
    hZ, inv_one, one_smul, he]
  rfl

private theorem mean_polynomial_zero (h : ℝ) (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) :
    eulerMean (polynomialLogReference h) 0 (torusHolder f hf) =
      ∫ x, f x ∂(polynomialRankOne h).ref.measure := by
  rw [eulerMean, polynomialEuler_density_zero]
  have he : torusHolder f hf * torusHolder (polynomialRankOne h).q
      (polynomialRankOne h).q_smooth =
      torusHolder (fun x => f x * (polynomialRankOne h).q x)
        (hf.mul (polynomialRankOne h).q_smooth) := by
    apply ext_STR02954
    funext t
    rfl
  rw [he, mean_torusHolder, LocalGaussianEndpoint.integral_ref_eq]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => mul_comm _ _

private theorem polynomial_feature_mean_zero (h : ℝ) :
    eulerMean (polynomialLogReference h) 0 (polynomialEulerFeature h) = 0 := by
  rw [polynomialEulerFeature, mean_polynomial_zero, LocalGaussianEndpoint.integral_ref_eq]
  exact (integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).trans
    (polynomialRankOne h).φ_centered

private theorem polynomial_generator_mean_zero (h : ℝ) :
    eulerMean (polynomialLogReference h) 0 (polynomialEulerGenerator h) = 0 := by
  rw [polynomialEulerGenerator, mean_polynomial_zero]
  simpa using polynomial_residual_centered h 0

/-- The moving equilibrium solves the full interacting weak Euler equation for EVERY rate.
This is the zero-amplitude statement needed for a subsequent quadratic-amplitude reduction. -/
theorem polynomialEuler_zero (h r : ℝ) (v : PeriodicC2_STR02969) :
    polynomialEuler h r 0 v = 0 := by
  simp only [polynomialEuler, polynomial_feature_mean_zero, polynomial_generator_mean_zero]
  simp [eulerCov, eulerMean]

/-- The actual deficit and its full Frechet derivative vanish at zero displacement. -/
theorem polynomialChartDeficit_zero (h r : ℝ) :
    polynomialChartDeficit h r 0 = 0 ∧ fderiv ℝ (polynomialChartDeficit h r) 0 = 0 := by
  constructor
  · simp only [polynomialChartDeficit, polynomial_feature_mean_zero]
    simp [eulerFisher, eulerEntropy, eulerMean]
  · ext v
    rw [polynomialChartDeficit_fderiv, polynomialEuler_zero]
    rfl

end DGPS.Examples.PolynomialSpecies
