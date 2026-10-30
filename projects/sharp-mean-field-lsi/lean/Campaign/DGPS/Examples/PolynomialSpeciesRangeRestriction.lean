import DGPS.Examples.PolynomialSpeciesRangeMap
import DGPS.Examples.PolynomialSpeciesEulerCanonical

/-! Exact restriction of the independent-parameter Euler family to the frozen moving
reference. The parameter extension is a calculation device; no reference is replaced. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.PositiveRankOne
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux
open DGPS.Circle.FirstClusterPerturbation DGPS.Circle.BesselMoments
open DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private theorem canonical_density_angular (h : ℝ) (θ : AngCircle) :
    (polynomialRankOne h).q (angEquiv.symm θ) = density_EX054 h (root_EX054 h) θ := by
  let s := root_EX054 h
  have hw (x : Torus 1) : Real.exp (-polyPot_EX055 h s x) = weight_EX054 h s (angEquiv x) := by
    simp only [polyPot_EX055, weight_EX054, feature_model_EX054,
      DGPS.Circle.VonMisesSmallField.ex010_angCos, cosT, ThreeSpeciesCircle.cosHarm]
    congr 1
    ring
  have hZ : ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h s) = partition_EX054 h s := by
    unfold ThreeSpeciesCircle.gibbsZ partition_EX054
    simp_rw [hw]
    exact integral_comp_angEquiv _
  change Real.exp (-polyPot_EX055 h s (angEquiv.symm θ)) /
    ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h s) = _
  rw [hw, MeasurableEquiv.apply_symm_apply, hZ]
  rfl

/-- Both constructions use exactly the same actual normalized reference. -/
theorem polynomialRangeReference_actual (h : ℝ) :
    polynomialRangeReference (h, root_EX054 h) = eulerDensity (polynomialLogReference h) 0 := by
  rw [polynomialEuler_density_zero]
  apply ext_STR02954
  funext t
  rw [polynomialRangeReference_val]
  change _ = (polynomialRankOne h).q (angEquiv.symm (t : AngCircle))
  exact (canonical_density_angular h _).symm

private theorem logReference_eq (h : ℝ) :
    polynomialLogReference h = e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h)) -
      Real.log (Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h)))) •
        (1 : PeriodicHolder_STR02968) := by
  apply ext_STR02954
  funext t
  have hQ : (polynomialRangeReference (h, root_EX054 h)).val t =
      (polynomialRankOne h).q (angEquiv.symm (t : AngCircle)) := by
    rw [polynomialRangeReference_val]
    exact (canonical_density_angular h _).symm
  change Real.log ((polynomialRankOne h).q (angEquiv.symm (t : AngCircle))) = _
  rw [← hQ, polynomialRangeReference, rho_val_STR02954]
  simp only [rhoT_STR02901, zero_mul, zero_add, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_one_STR02954, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, e0_val_STR02955, mul_one]
  have hZ : 0 < meanT_STR02901 (fun s =>
      Real.exp ((polynomialRangeLogWeight (h, root_EX054 h)).val s)) := by
    simpa only [Z_eq_meanT_STR02954, zero_mul, zero_add, e0_val_STR02955] using
      Z_pos_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h)))
  rw [Z_eq_meanT_STR02954]
  simp only [zero_mul, zero_add, e0_val_STR02955]
  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]

/-- The angular logarithmic drift is the actual frozen drift after restriction. -/
theorem polynomialRangeLogDerivative_actual (h : ℝ) :
    e1_STR02955 (polynomialRangeLogWeight (h, root_EX054 h)) = polynomialLogDerivative h := by
  apply ext_STR02954
  funext t
  change deriv (polynomialRangeLogWeight (h, root_EX054 h)).val t =
    deriv (polynomialLogReference h).val t
  have he : (polynomialLogReference h).val = fun s =>
      (polynomialRangeLogWeight (h, root_EX054 h)).val s -
      Real.log (Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h)))) := by
    rw [logReference_eq]
    funext s
    simp only [PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_one_STR02954, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0_val_STR02955, mul_one]
  rw [he]
  exact (((polynomialRangeLogWeight (h, root_EX054 h)).isC2.2.1 t).hasDerivAt.sub_const _).deriv.symm

private theorem lift_point (t : ℝ) :
    torusLift (fun _ : Fin 1 => t / (2 * Real.pi)) = angEquiv.symm (t : AngCircle) := by
  apply angEquiv.injective
  rw [MeasurableEquiv.apply_symm_apply]
  rw [angEquiv_apply]
  change angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) = (t : AngCircle)
  rw [angRescale_mk]
  congr 1
  field_simp [Real.pi_ne_zero]

private theorem physical_first (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) (t : ℝ) :
    coordPartial 0 f (angEquiv.symm (t : AngCircle)) =
      (2 * Real.pi) * deriv (fun s : ℝ => f (angEquiv.symm (s : AngCircle))) t := by
  let ψ : AngCircle → ℝ := f ∘ angEquiv.symm
  have hs : IsSmoothAngular ψ := by
    apply (isSmoothPeriodic_comp_iff ψ).1
    convert hf using 1
    ext x
    simp only [ψ, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have he : ψ ∘ angEquiv = f := by ext x; simp [ψ]
  have h := physical_first_derivative_EX009 ψ hs (t / (2 * Real.pi))
  rw [he, lift_point] at h
  have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp [Real.pi_ne_zero]
  simpa only [ht, ψ, Function.comp_apply] using h

private theorem physical_second (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) (t : ℝ) :
    coordPartial 0 (coordPartial 0 f) (angEquiv.symm (t : AngCircle)) =
      DGPS.Circle.AngularNormalization.a0 *
        deriv (deriv (fun s : ℝ => f (angEquiv.symm (s : AngCircle)) )) t := by
  let ψ : AngCircle → ℝ := f ∘ angEquiv.symm
  have hs : IsSmoothAngular ψ := by
    apply (isSmoothPeriodic_comp_iff ψ).1
    convert hf using 1
    ext x
    simp only [ψ, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have he : ψ ∘ angEquiv = f := by ext x; simp [ψ]
  have h := physical_second_derivative_EX009 ψ hs (t / (2 * Real.pi))
  rw [he, lift_point] at h
  have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp [Real.pi_ne_zero]
  simpa only [ht, ψ, Function.comp_apply] using h

private theorem feature_val_actual (h : ℝ) :
    (polynomialRangeFeature (h, root_EX054 h)).val =
      fun t : ℝ => (polynomialRankOne h).φ (angEquiv.symm (t : AngCircle)) := by
  have hφ := congrArg PeriodicHolder_STR02968.val (polynomialRangeFeature_actual h)
  funext t
  have ht := congrFun hφ t
  rw [e0_val_STR02955] at ht
  change (polynomialRangeFeature (h, root_EX054 h)).val t =
    (polynomialRankOne h).φ (angEquiv.symm (t : AngCircle)) at ht
  exact ht

/-- The true weighted generator agrees in physical units; no eigenfunction equation is used. -/
theorem polynomialRangeGenerator_actual (h : ℝ) :
    polynomialRangeGenerator (h, root_EX054 h) = polynomialEulerGenerator h := by
  apply ext_STR02954
  funext t
  have hφ := feature_val_actual h
  have hdφ := physical_first (polynomialRankOne h).φ (polynomialRankOne h).φ_smooth t
  have hddφ := physical_second (polynomialRankOne h).φ (polynomialRankOne h).φ_smooth t
  have hdlog := physical_first (fun x => Real.log ((polynomialRankOne h).q x))
    (polynomialRankOne h).log_smooth t
  rw [← hφ] at hdφ hddφ
  unfold polynomialRangeGenerator
  rw [polynomialRangeLogDerivative_actual]
  simp only [PeriodicHolder_STR02968.val_smul, PeriodicHolder_STR02968.val_sub,
    val_mul_STR02954, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul,
    e1_val_STR02955, e2_val_STR02955]
  change DGPS.Circle.AngularNormalization.a0 *
    (-deriv (deriv (polynomialRangeFeature (h, root_EX054 h)).val) t -
      deriv (polynomialLogReference h).val t * deriv (polynomialRangeFeature (h, root_EX054 h)).val t) =
    (polynomialRankOne h).Aq (angEquiv.symm (t : AngCircle))
  unfold RankOneModel.Aq RankOneModel.dφ RankOneModel.dlogq
  rw [hdφ, hddφ, hdlog]
  change _ = -(DGPS.Circle.AngularNormalization.a0 * _ ) -
    (2 * Real.pi * deriv (polynomialLogReference h).val t) *
      (2 * Real.pi * deriv (polynomialRangeFeature (h, root_EX054 h)).val t)
  unfold DGPS.Circle.AngularNormalization.a0
  ring

/-- The feature-gradient square has exactly the same physical normalization. -/
theorem polynomialRangeGradientSq_actual (h : ℝ) :
    polynomialRangeGradientSq (h, root_EX054 h) = polynomialEulerGradientSq h := by
  apply ext_STR02954
  funext t
  have hd := physical_first (polynomialRankOne h).φ (polynomialRankOne h).φ_smooth t
  rw [← feature_val_actual h] at hd
  change DGPS.Circle.AngularNormalization.a0 *
    (deriv (polynomialRangeFeature (h, root_EX054 h)).val t *
      deriv (polynomialRangeFeature (h, root_EX054 h)).val t) =
    ((polynomialRankOne h).dφ (angEquiv.symm (t : AngCircle))) ^ 2
  unfold RankOneModel.dφ
  rw [hd]
  unfold DGPS.Circle.AngularNormalization.a0
  ring

private theorem density_shift (L : PeriodicHolder_STR02968) (c : ℝ) (u : PeriodicC2_STR02969) :
    eulerDensity (L - c • (1 : PeriodicHolder_STR02968)) u = eulerDensity L u := by
  apply ext_STR02954
  funext t
  have he : ∀ s : ℝ, Real.exp (((L - c • (1 : PeriodicHolder_STR02968)) + e0_STR02955 u).val s) =
      Real.exp (-c) * Real.exp ((L + e0_STR02955 u).val s) := by
    intro s
    simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
      PeriodicHolder_STR02968.val_smul, val_one_STR02954, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, mul_one, e0_val_STR02955]
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [eulerDensity, rho_val_STR02954, rhoT_STR02901, zero_mul, zero_add]
  simp_rw [he]
  rw [show (fun s : ℝ => Real.exp (-c) * Real.exp ((L + e0_STR02955 u).val s)) =
    (Real.exp (-c)) • (fun s : ℝ => Real.exp ((L + e0_STR02955 u).val s)) from rfl,
    meanT_smul_STR02953]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

/-- The full normalized chart density is unchanged by restriction to the actual reference. -/
theorem polynomialRangeDensity_actual (h : ℝ) (u : PeriodicC2_STR02969) :
    eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u =
      eulerDensity (polynomialLogReference h) u := by
  rw [logReference_eq, density_shift]

/-- The analytic extension restricts to the actual full nonlocal Euler map, with the same
moving reference, physical generator and physical Fisher scale. -/
theorem polynomialRangeEuler_actual (h r : ℝ) (u : PeriodicC2_STR02969) :
    polynomialRangeEuler (h, root_EX054 h) r u = polynomialEulerGradient h r u := by
  have hK : polynomialRangeEulerPotential (h, root_EX054 h) r u = polynomialEulerPotential h r u := by
    unfold polynomialRangeEulerPotential polynomialEulerPotential eulerMean
    rw [polynomialRangeFeature_actual, polynomialRangeGenerator_actual,
      polynomialRangeGradientSq_actual, polynomialRangeLogDerivative_actual]
    simp_rw [polynomialRangeDensity_actual]
  unfold polynomialRangeEuler polynomialEulerGradient eulerMean
  simp_rw [hK, polynomialRangeDensity_actual]

end DGPS.Examples.PolynomialSpecies
