import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Examples.PolynomialRates
import DGPS.Circle.FirstClusterPerturbation

/-! Exact physical normalization of the moving polynomial generator residual. -/

noncomputable section
open MeasureTheory Filter
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Examples.PolynomialSpecies
open DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialExactGap
  DGPS.Examples.PolynomialCenteredResidual DGPS.Circle.FirstClusterPerturbation
  DGPS.PositiveRankOne DGPS.Circle.StationaryFlux

/-- The actual centered physical feature is the previously defined angular feature. -/
theorem polynomial_feature_angular (h : ℝ) :
    (polynomialRankOne h).φ = phi_EX057 h ∘ angEquiv := by
  funext x
  change Real.sqrt 2 * (polyFeature h x - moment_EX054 h (root_EX054 h)) = _
  simp only [Function.comp_apply, phi_EX057, feature_model_EX054]

/-- The physical weighted generator residual is exactly `DGPS.Circle.AngularNormalization.a0` times EX057's angular residual. -/
theorem polynomial_residual_physical_eq (h : ℝ) (x : Torus 1) :
    (polynomialRankOne h).Aq x - (4 * DGPS.Circle.AngularNormalization.a0) * (polynomialRankOne h).φ x =
      DGPS.Circle.AngularNormalization.a0 * resid_EX057 h (angEquiv x) := by
  let M := polynomialRankOne h
  let s := root_EX054 h
  let m := moment_EX054 h s
  let Z := ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h s)
  let ell : AngCircle → ℝ := fun θ => h * angCos θ - s * feature_EX054 h θ - Real.log Z
  let ψ : AngCircle → ℝ := phi_EX057 h
  have hZ : 0 < Z := ThreeSpeciesCircle.gibbsZ_pos (isSmooth_polyPot_EX055 h s)
  have hlog : (fun x => Real.log (M.q x)) = ell ∘ angEquiv := by
    funext y
    change Real.log (Real.exp (-polyPot_EX055 h s y) / Z) = _
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
    dsimp only [Function.comp_apply, ell, polyPot_EX055]
    rw [feature_model_EX054, DGPS.Circle.VonMisesSmallField.ex010_angCos]
    simp only [cosT, ThreeSpeciesCircle.cosHarm]
    ring
  have hfeature : M.φ = ψ ∘ angEquiv := polynomial_feature_angular h
  have hell : IsSmoothAngular ell := by
    apply (isSmoothPeriodic_comp_iff ell).1
    rw [← hlog]
    exact M.log_smooth
  have hψ : IsSmoothAngular ψ := by
    apply (isSmoothPeriodic_comp_iff ψ).1
    rw [← hfeature]
    exact M.φ_smooth
  have hgen : ∀ y, M.Aq y = physicalGenerator_EX009 ell ψ y := by
    intro y
    unfold RankOneModel.Aq RankOneModel.dlogq RankOneModel.dφ physicalGenerator_EX009
    rw [hfeature, hlog]
    ring
  have helllift : (fun t : ℝ => ell (t : AngCircle)) =
      fun t => logW_EX057 h s t - Real.log Z := by
    funext t
    dsimp only [ell, logW_EX057]
    rw [angCos_coe_EX057, feature_coe_EX057]
  have hψlift : (fun t : ℝ => ψ (t : AngCircle)) = Phi_EX057 h m := by
    funext t
    exact phi_coe_EX057 h t
  have hdψ : deriv (Phi_EX057 h m) = fun t => Real.sqrt 2 * Pd_EX057 h t :=
    funext fun t => (hasDerivAt_Phi_EX057 h m t).deriv
  have hddψ : deriv (fun t => Real.sqrt 2 * Pd_EX057 h t) =
      fun t => Real.sqrt 2 * Pdd_EX057 h t :=
    funext fun t => (hasDerivAt_sqrtPd_EX057 h t).deriv
  have hdell : deriv (fun t => logW_EX057 h s t - Real.log Z) =
      fun t => -h * Real.sin t - s * Pd_EX057 h t :=
    funext fun t => ((hasDerivAt_logW_EX057 h s t).sub_const _).deriv
  obtain ⟨t, rfl⟩ := exists_lift x
  rw [hgen, physical_generator_formula_EX009 ell ψ hell hψ]
  have hφt : M.φ (torusLift (fun _ : Fin 1 => t)) = Phi_EX057 h m (2 * Real.pi * t) := by
    rw [hfeature]
    change (ψ ∘ angEquiv) (torusLift (fun _ : Fin 1 => t)) = _
    rw [comp_angEquiv_liftT]
    exact phi_coe_EX057 h _
  have hRt : resid_EX057 h (angEquiv (torusLift (fun _ : Fin 1 => t))) =
      resid_EX057 h ((2 * Real.pi * t : ℝ) : AngCircle) :=
    comp_angEquiv_liftT (resid_EX057 h) (fun _ : Fin 1 => t)
  rw [hφt, hRt, helllift, hψlift]
  unfold negativeGenerator_EX009
  rw [hdψ, hddψ, hdell, resid_formula_EX057]
  dsimp only [Phi_EX057, Pdd_EX057, s, m]
  ring

/-- A genuine uniform first-order bound for the actual physical generator residual. -/
theorem polynomial_physical_residual_bound :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ → ∀ x : Torus 1,
      |(polynomialRankOne h).Aq x - (4 * DGPS.Circle.AngularNormalization.a0) * (polynomialRankOne h).φ x| ≤ C * |h| := by
  obtain ⟨C, δ, hC, hδ, hbound⟩ := polynomial_centered_residual 0
  refine ⟨DGPS.Circle.AngularNormalization.a0 * C, δ, mul_pos DGPS.Circle.AngularNormalization.a0_pos hC, hδ, fun h hh x => ?_⟩
  have hR : ∀ θ : AngCircle, |resid_EX057 h θ| ≤ C * |h| := by
    intro θ
    induction θ using QuotientAddGroup.induction_on with
    | _ t =>
      simpa only [iteratedDeriv_zero, lift] using (hbound h hh).2 0 le_rfl t
  rw [polynomial_residual_physical_eq, abs_mul, abs_of_pos DGPS.Circle.AngularNormalization.a0_pos]
  exact (mul_le_mul_of_nonneg_left (hR (angEquiv x)) DGPS.Circle.AngularNormalization.a0_pos.le).trans_eq (by ring)

end DGPS.Examples.PolynomialSpecies
