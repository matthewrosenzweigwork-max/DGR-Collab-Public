import DGPS.Examples.PolynomialVaryingLimits
import DGPS.Examples.PolynomialResidualNormalization
import DGPS.Examples.SixthOrderCentering

/-! The genuine Haar competitor in the original absolute H1 domain. Its actual
canonical polynomial gap and dissipation are computed exactly, retaining the
moving normalization and using the root equation only for the force cancellation. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open DGPS.PositiveRankOne DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialExactGap
open DGPS.Examples.PolynomialCenteredResidual DGPS.Examples.ThreeSpeciesCircle
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments
open DGPS.Circle.FirstClusterFourierEX009 DGPS.Circle.StationaryFlux

namespace DGPS.Examples.PolynomialSpecies

/-- One fixed original-domain competitor, with square root literally one. -/
def polynomialHaarTrial : AbsoluteDensity 1 where
  sqrt := fun _ => 1
  sqrt_mem := by rw [mem_H1Haar]; exact ⟨0, isWeakGradient_const 1⟩
  sqrt_nonneg := Eventually.of_forall fun _ => zero_le_one
  mass_one := by simp

theorem polynomialHaarTrial_measure : (densityMeasure polynomialHaarTrial : Measure (Torus 1)) = haar 1 := by
  change (haar 1).withDensity (fun _ => ENNReal.ofReal ((1 : ℝ) ^ 2)) = haar 1
  simp

private theorem mode_eq (k : ℕ) (θ : AngCircle) : angMode k θ = cosMode_EX009 (k : ℤ) θ := by
  induction θ using QuotientAddGroup.induction_on with
  | H t => rw [angMode_coe, cosMode_coe_EX009]; simp

private theorem cos_as_mode (k : ℕ) (x : Torus 1) : cosT k x = angMode k (angEquiv x) := by
  obtain ⟨t, rfl⟩ := exists_lift x
  rw [cosT_lift]
  change Real.cos (2 * Real.pi * (k : ℝ) * t) =
    (angMode k ∘ angEquiv) (torusLift (fun _ : Fin 1 => t))
  rw [comp_angEquiv_liftT (angMode k), angMode_coe]
  congr 1
  ring

private theorem cos_mean (k : ℕ) (hk : k ≠ 0) : (∫ x, cosT k x ∂haar 1) = 0 := by
  simp_rw [cos_as_mode]
  rw [integral_comp_angEquiv (angMode k)]
  simp_rw [mode_eq]
  rw [cosMode_mean_EX009]
  have hki : (k : ℤ) ≠ 0 := by exact_mod_cast hk
  simp [hk, hki]

private theorem feature_mean (h : ℝ) : (∫ x, polyFeature h x ∂haar 1) = 0 := by
  unfold polyFeature
  rw [integral_sub (integrable_of_continuous_torus (continuous_cosT 2))
    ((integrable_of_continuous_torus (continuous_cosT 1)).const_mul _), integral_const_mul,
    cos_mean 2 (by norm_num), cos_mean 1 (by norm_num)]
  ring

private theorem actual_partition (h : ℝ) :
    gibbsZ (polyPot_EX055 h (root_EX054 h)) = partition_EX054 h (root_EX054 h) := by
  have hw (x : Torus 1) : Real.exp (-polyPot_EX055 h (root_EX054 h) x) =
      weight_EX054 h (root_EX054 h) (angEquiv x) := by
    simp only [polyPot_EX055, weight_EX054, feature_model_EX054,
      DGPS.Circle.VonMisesSmallField.ex010_angCos, cosT, ThreeSpeciesCircle.cosHarm]
    congr 1
    ring
  unfold gibbsZ partition_EX054
  simp_rw [hw]
  exact integral_comp_angEquiv (weight_EX054 h (root_EX054 h))

private theorem log_q (h : ℝ) (x : Torus 1) :
    Real.log ((polynomialRankOne h).q x) = h * cosT 1 x - root_EX054 h * polyFeature h x -
      Real.log (partition_EX054 h (root_EX054 h)) := by
  change Real.log (Real.exp (-polyPot_EX055 h (root_EX054 h) x) /
    gibbsZ (polyPot_EX055 h (root_EX054 h))) = _
  rw [Real.log_div (Real.exp_pos _).ne' (gibbsZ_pos (isSmooth_polyPot_EX055 h (root_EX054 h))).ne',
    Real.log_exp, actual_partition]
  unfold polyPot_EX055
  ring

private theorem moment_haar (h : ℝ) :
    (∫ x, (polynomialRankOne h).φ x ∂haar 1) = -Real.sqrt 2 * moment_EX054 h (root_EX054 h) := by
  change (∫ x, Real.sqrt 2 * (polyFeature h x - moment_EX054 h (root_EX054 h)) ∂haar 1) = _
  rw [integral_const_mul, integral_sub (integrable_of_continuous_torus (continuous_polyFeature h))
    (integrable_const _), feature_mean]
  simp <;> ring

private theorem score_haar (h : ℝ) (x : Torus 1) :
    -(polynomialRankOne h).dlogq x +
      (eta * ∫ y, (polynomialRankOne h).φ y ∂haar 1) * (polynomialRankOne h).dφ x =
    (2 * Real.pi) * (h * (1 + eta * h ^ 2 / 36) * sinMode_EX009 1 (angEquiv x) -
      eta * h ^ 2 / 6 * sinMode_EX009 2 (angEquiv x)) := by
  let M := polynomialRankOne h
  let s := root_EX054 h
  let m := moment_EX054 h s
  let z := Real.log (partition_EX054 h s)
  let F := fun x => -Real.log (M.q x) + (eta * (-Real.sqrt 2 * m)) * M.φ x
  have hF : IsSmoothPeriodic F := M.log_smooth.neg.add (contDiff_const.mul M.φ_smooth)
  have hs : s - 2 * eta * m = eta * h ^ 2 / 12 := by
    have he := root_equation_EX054 h
    dsimp only [polyCentering] at he
    dsimp only [s, m]
    linarith
  have hv (y : Torus 1) : F y = -h * (1 + eta * h ^ 2 / 36) * cosT 1 y +
      eta * h ^ 2 / 12 * cosT 2 y + (z + 2 * eta * m ^ 2) := by
    change -Real.log (M.q y) + (eta * (-Real.sqrt 2 * m)) *
      (Real.sqrt 2 * (polyFeature h y - m)) = _
    have he : (eta * (-Real.sqrt 2 * m)) * (Real.sqrt 2 * (polyFeature h y - m)) =
        -2 * eta * m * (polyFeature h y - m) := by
      calc
        _ = -eta * m * Real.sqrt 2 ^ 2 * (polyFeature h y - m) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
    rw [he, log_q]
    change -(h * cosT 1 y - s * polyFeature h y - z) +
      (-2 * eta * m * (polyFeature h y - m)) = _
    calc
      _ = -h * cosT 1 y + (s - 2 * eta * m) * polyFeature h y + (z + 2 * eta * m ^ 2) := by ring
      _ = _ := by rw [hs]; unfold polyFeature; ring
  have hcoord : coordPartial 0 F x = -M.dlogq x +
      (eta * (-Real.sqrt 2 * m)) * M.dφ x := by
    simpa only [F, RankOneModel.dlogq, RankOneModel.dφ, zero_add, add_zero, one_mul, neg_one_mul] using
      RankOneModel.coordPartial_lin M.log_smooth M.φ_smooth (-1) (eta * (-Real.sqrt 2 * m)) 0 x
  rw [moment_haar]
  change -M.dlogq x + (eta * (-Real.sqrt 2 * m)) * M.dφ x = _
  rw [← hcoord]
  obtain ⟨t, rfl⟩ := exists_lift x
  have he : (fun t : ℝ => F (pt t)) = fun t =>
      -h * (1 + eta * h ^ 2 / 36) * Real.cos ((2 * Real.pi) * t) +
      eta * h ^ 2 / 12 * Real.cos ((4 * Real.pi) * t) + (z + 2 * eta * m ^ 2) := by
    funext t
    rw [hv, cosT_lift, cosT_lift]
    congr 2 <;> ring
  have hd := (((((hasDerivAt_id t).const_mul (2 * Real.pi)).cos).const_mul
    (-h * (1 + eta * h ^ 2 / 36))).add
      ((((hasDerivAt_id t).const_mul (4 * Real.pi)).cos).const_mul (eta * h ^ 2 / 12))).add_const
        (z + 2 * eta * m ^ 2)
  simp only [Pi.add_apply, id_eq, mul_one] at hd
  rw [← he] at hd
  have hc := circ_coordPartial_pt hF t
  rw [hc.unique hd]
  rw [show sinMode_EX009 1 (angEquiv (torusLift (fun _ : Fin 1 => t))) =
      Real.sin ((2 * Real.pi) * t) from by
        change (sinMode_EX009 1 ∘ angEquiv) (torusLift (fun _ : Fin 1 => t)) = _
        rw [comp_angEquiv_liftT (sinMode_EX009 1), sinMode_coe_EX009]; norm_num]
  rw [show sinMode_EX009 2 (angEquiv (torusLift (fun _ : Fin 1 => t))) =
      Real.sin ((4 * Real.pi) * t) from by
        change (sinMode_EX009 2 ∘ angEquiv) (torusLift (fun _ : Fin 1 => t)) = _
        rw [comp_angEquiv_liftT (sinMode_EX009 2), sinMode_coe_EX009]; congr 1 <;> norm_num <;> ring]
  ring

private theorem two_mode_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ)
    (hff : Integrable (fun x => f x * f x) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hgg : Integrable (fun x => g x * g x) μ)
    (h11 : (∫ x, f x * f x ∂μ) = 1 / 2)
    (h12 : (∫ x, f x * g x ∂μ) = 0)
    (h22 : (∫ x, g x * g x ∂μ) = 1 / 2) (A B : ℝ) :
    (∫ x, (A * f x + B * g x) ^ 2 ∂μ) = (A ^ 2 + B ^ 2) / 2 := by
  have he : (fun x => (A * f x + B * g x) ^ 2) =
      fun x => A ^ 2 * (f x * f x) + (2 * A * B) * (f x * g x) + B ^ 2 * (g x * g x) := by
    funext x
    ring
  rw [he]
  calc
    _ = (∫ x, A ^ 2 * (f x * f x) + (2 * A * B) * (f x * g x) ∂μ) +
        ∫ x, B ^ 2 * (g x * g x) ∂μ :=
      integral_add ((hff.const_mul _).add (hfg.const_mul _)) (hgg.const_mul _)
    _ = ((∫ x, A ^ 2 * (f x * f x) ∂μ) +
        ∫ x, (2 * A * B) * (f x * g x) ∂μ) + ∫ x, B ^ 2 * (g x * g x) ∂μ := by
      congr 1
      exact integral_add (hff.const_mul _) (hfg.const_mul _)
    _ = _ := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul, h11, h12, h22]
      ring

private theorem sine_energy (A B : ℝ) :
    (∫ θ, (A * sinMode_EX009 1 θ + B * sinMode_EX009 2 θ) ^ 2 ∂angHaar) = (A ^ 2 + B ^ 2) / 2 := by
  have hi (i j : ℤ) : Integrable (fun θ => sinMode_EX009 i θ * sinMode_EX009 j θ) angHaar :=
    ((continuous_sinMode_EX009 i).mul (continuous_sinMode_EX009 j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact two_mode_energy angHaar (sinMode_EX009 1) (sinMode_EX009 2)
    (hi 1 1) (hi 1 2) (hi 2 2)
    (by rw [sinMode_inner_EX009]; norm_num)
    (by rw [sinMode_inner_EX009]; norm_num)
    (by rw [sinMode_inner_EX009]; norm_num) A B

/-- Exact canonical full-domain Haar trial identities. Finite native
Dissipation follows from the displayed ofReal expression before any conversion. -/
theorem polynomial_haar_trial_gap_dissipation (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    (scalarGap (canonical_elementary_polynomial_model h) polynomialHaarTrial : ℝ) =
      Real.log (partition_EX054 h (root_EX054 h)) + eta * (moment_EX054 h (root_EX054 h)) ^ 2 ∧
    scalarDissipation (canonical_elementary_polynomial_model h) b polynomialHaarTrial =
      ENNReal.ofReal (a0 / 2 * (h ^ 2 * (1 + eta * h ^ 2 / 36) ^ 2 + eta ^ 2 * h ^ 4 / 36)) := by
  let M := polynomialRankOne h
  have hm := moment_haar h
  have hlog : (∫ x, Real.log (M.q x) ∂haar 1) = -Real.log (partition_EX054 h (root_EX054 h)) := by
    change (∫ x, Real.log ((polynomialRankOne h).q x) ∂haar 1) = _
    simp_rw [log_q]
    calc
      _ = (∫ x, h * cosT 1 x - root_EX054 h * polyFeature h x ∂haar 1) -
          ∫ _x : Torus 1, Real.log (partition_EX054 h (root_EX054 h)) ∂haar 1 :=
        integral_sub (((integrable_of_continuous_torus (continuous_cosT 1)).const_mul _).sub
          ((integrable_of_continuous_torus (continuous_polyFeature h)).const_mul _)) (integrable_const _)
      _ = ((∫ x, h * cosT 1 x ∂haar 1) -
          ∫ x, root_EX054 h * polyFeature h x ∂haar 1) -
          ∫ _x : Torus 1, Real.log (partition_EX054 h (root_EX054 h)) ∂haar 1 := by
        congr 1
        exact integral_sub ((integrable_of_continuous_torus (continuous_cosT 1)).const_mul _)
          ((integrable_of_continuous_torus (continuous_polyFeature h)).const_mul _)
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, cos_mean 1 (by norm_num), feature_mean]
        simp
  have hH := M.entropy_ref_eq (densityMeasure polynomialHaarTrial) (by rw [polynomialHaarTrial_measure, relativeEntropy_self]; simp)
  rw [polynomialHaarTrial_measure, relativeEntropy_self, ENNReal.toReal_zero, hlog] at hH
  constructor
  · have hg := (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single polynomialHaarTrial)).1
    have hG : (scalarGap (canonical_elementary_polynomial_model h) polynomialHaarTrial : ℝ) =
        (relativeEntropy (densityMeasure polynomialHaarTrial : Measure (Torus 1)) M.ref.measure).toReal +
          eta / 2 * (∫ x, M.φ x ∂haar 1) ^ 2 := by
      change (scalarGap (canonical_elementary_polynomial_model h) polynomialHaarTrial : ℝ) =
        (relativeEntropy (densityMeasure polynomialHaarTrial : Measure (Torus 1))
          (polynomialRankOne h).ref.measure).toReal +
          eta / 2 * (∫ x, (polynomialRankOne h).φ x ∂haar 1) ^ 2
      rw [polynomialRankOne_reference, polynomialHaarTrial_measure]
      simpa only [speciesGap_single, densityMeasure_barycenter_single, sum_single_count,
        SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul,
        polynomialRankOne_reference, polynomialHaarTrial_measure] using hg
    rw [hG, polynomialHaarTrial_measure, hH, hm]
    rw [mul_pow, neg_sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · rw [polynomial_scalar_score_square, polynomialHaarTrial_measure]
    have hg := weakGradient_ae_eq (isWeakGradient_const (d := 1) 1)
    congr 1
    calc
      _ = ∫ x, ((2 * Real.pi) * (h * (1 + eta * h ^ 2 / 36) * sinMode_EX009 1 (angEquiv x) -
          eta * h ^ 2 / 6 * sinMode_EX009 2 (angEquiv x))) ^ 2 ∂haar 1 := by
        apply integral_congr_ae
        filter_upwards [hg] with x hx
        change (2 * weakGradient polynomialHaarTrial.sqrt polynomialHaarTrial.sqrt_mem x 0 -
          1 * M.dlogq x + (eta * ∫ y, M.φ y ∂haar 1) * (1 * M.dφ x)) ^ 2 = _
        have hz : weakGradient polynomialHaarTrial.sqrt polynomialHaarTrial.sqrt_mem x 0 = 0 := by
          have hh := congrArg (fun v : Tangent 1 => v 0) hx
          exact hh
        rw [hz, mul_zero, zero_sub, one_mul, one_mul, score_haar]
      _ = a0 * ∫ θ, (h * (1 + eta * h ^ 2 / 36) * sinMode_EX009 1 θ +
          (-eta * h ^ 2 / 6) * sinMode_EX009 2 θ) ^ 2 ∂angHaar := by
        rw [← integral_comp_angEquiv (fun θ => (h * (1 + eta * h ^ 2 / 36) * sinMode_EX009 1 θ +
          (-eta * h ^ 2 / 6) * sinMode_EX009 2 θ) ^ 2)]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by unfold a0; ring
      _ = _ := by rw [sine_energy]; ring

end DGPS.Examples.PolynomialSpecies
