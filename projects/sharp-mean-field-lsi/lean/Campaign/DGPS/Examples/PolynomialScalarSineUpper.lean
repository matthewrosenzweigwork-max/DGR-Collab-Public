import DGPS.Examples.PolynomialUniformData
import DGPS.Examples.EngineeredUniqueness
import DGPS.Lipschitz.T01ScalarGaussian

/-! A genuine sine tilt bounds the actual polynomial scalar rate near the
Haar field. The exact Rayleigh numerator is retained. No optimizer graph,
regularity, inverse-Hessian bound, or desired rate comparison is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open DGPS.PositiveRankOne DGPS.Examples.EngineeredUniqueness
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments
open DGPS.Circle.StationaryFlux DGPS.Examples.PolynomialEquilibrium
open DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private def sine : AngCircle → ℝ := Real.Angle.sin
private def cosine : AngCircle → ℝ := Real.Angle.cos

private theorem sine_neg (θ : AngCircle) : sine (-θ) = -sine θ := Real.Angle.sin_neg θ

private theorem smooth_sine : IsSmoothAngular sine := by
  change ContDiff ℝ ∞ (Real.sin : ℝ → ℝ)
  exact Real.contDiff_sin

private theorem smooth_cosine : IsSmoothAngular cosine := by
  change ContDiff ℝ ∞ (Real.cos : ℝ → ℝ)
  exact Real.contDiff_cos

private theorem cosine_eq (θ : AngCircle) : cosine θ = angCos θ := by
  unfold cosine
  induction θ using Real.Angle.induction_on with
  | _ t =>
    rw [Real.Angle.cos_coe]
    exact ((angMode_coe 1 t).trans (by simp)).symm

private theorem sine_derivative (θ : AngCircle) : angDeriv sine θ = cosine θ := by
  change deriv Real.sin (angSec θ) = cosine θ
  rw [Real.deriv_sin]
  have he : cosine (((angSec θ : ℝ) : AngCircle)) = Real.cos (angSec θ) := Real.Angle.cos_coe _
  have hs : ((angSec θ : ℝ) : AngCircle) = θ := by
    unfold angSec
    exact AddCircle.coe_equivIoc
  rw [hs] at he
  exact he.symm

private theorem angular_q (h : ℝ) (θ : AngCircle) :
    (polynomialRankOne h).q (angEquiv.symm θ) = density_EX054 h (root_EX054 h) θ := by
  have hw (x : Torus 1) : Real.exp (-polyPot_EX055 h (root_EX054 h) x) =
      weight_EX054 h (root_EX054 h) (angEquiv x) := by
    simp only [polyPot_EX055, weight_EX054, feature_model_EX054,
      DGPS.Circle.VonMisesSmallField.ex010_angCos, cosT, DGPS.Examples.ThreeSpeciesCircle.cosHarm]
    congr 1
    ring
  have hZ : DGPS.Examples.ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h (root_EX054 h)) =
      partition_EX054 h (root_EX054 h) := by
    unfold DGPS.Examples.ThreeSpeciesCircle.gibbsZ partition_EX054
    simp_rw [hw]
    exact integral_comp_angEquiv _
  change Real.exp (-polyPot_EX055 h (root_EX054 h) (angEquiv.symm θ)) /
    DGPS.Examples.ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h (root_EX054 h)) = _
  rw [hw, MeasurableEquiv.apply_symm_apply, hZ]
  rfl

private theorem odd_integral_zero (F : AngCircle → ℝ) (hF : ∀ θ, F (-θ) = -F θ) :
    ∫ θ, F θ ∂angHaar = 0 := by
  have hi := integral_neg_eq_self F angHaar
  rw [show (fun θ => F (-θ)) = (fun θ => -F θ) from funext hF, integral_neg] at hi
  linarith

private theorem haar_squares :
    (∫ x, cosine (angEquiv x) ^ 2 ∂haar 1) = 1 / 2 ∧
    (∫ x, sine (angEquiv x) ^ 2 ∂haar 1) = 1 / 2 := by
  have hc : (∫ x, cosine (angEquiv x) ^ 2 ∂haar 1) = 1 / 2 := by
    rw [integral_comp_angEquiv (fun θ => cosine θ ^ 2)]
    simp_rw [cosine_eq]
    change cosAvg 2 = 1 / 2
    have hh := cosAvg_even 1
    norm_num at hh
    exact hh
  refine ⟨hc, ?_⟩
  have he : (fun x : Torus 1 => sine (angEquiv x) ^ 2) =
      fun x => 1 - cosine (angEquiv x) ^ 2 := by
    funext x
    have hh := Real.Angle.cos_sq_add_sin_sq (angEquiv x)
    change cosine (angEquiv x) ^ 2 + sine (angEquiv x) ^ 2 = 1 at hh
    linarith
  have hcos := ((isSmoothPeriodic_comp_iff _).2 smooth_cosine).continuous_torus
  have hi : Integrable (fun x : Torus 1 => cosine (angEquiv x) ^ 2) (haar 1) :=
    (hcos.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [he, integral_sub (f := fun _ : Torus 1 => (1 : ℝ))
    (g := fun x => cosine (angEquiv x) ^ 2) (integrable_const _) hi, hc]
  norm_num

/-- True moving-reference moments converge to Haar moments. Constants for
bounded domination follow from the actual uniform log-reference estimate. -/
theorem polynomial_reference_moment_tendsto (g : Torus 1 → ℝ) (hg : Continuous g) :
    Tendsto (fun h : ℝ => ∫ x, g x ∂(polynomialRankOne h).ref.measure) (𝓝 0)
      (𝓝 (∫ x, g x ∂haar 1)) := by
  obtain ⟨ε, hε, hb⟩ := polynomial_uniform_data_at_origin
  have hlog (h : ℝ) (x : Torus 1) : |Real.log ((polynomialRankOne h).q x)| ≤ ε h := by
    have hh := hb h x
    nlinarith [abs_nonneg ((polynomialRankOne h).φ x - (polynomialRankOne 0).φ x),
      abs_nonneg ((polynomialRankOne h).Aq x - (polynomialRankOne 0).Aq x),
      abs_nonneg ((polynomialRankOne h).dlogq x),
      abs_nonneg ((polynomialRankOne h).dφ x - (polynomialRankOne 0).dφ x)]
  have hq (x : Torus 1) : Tendsto (fun h : ℝ => (polynomialRankOne h).q x) (𝓝 0) (𝓝 1) := by
    have ht : Tendsto (fun h : ℝ => Real.log ((polynomialRankOne h).q x)) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm (fun h => by simpa only [Real.norm_eq_abs] using hlog h x) hε
    simpa only [Function.comp_def, Real.exp_log ((polynomialRankOne _).q_pos x), Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp ht
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0 (Set.mem_univ 0))
  have hsmall : ∀ᶠ h : ℝ in 𝓝 0, ε h ≤ 1 := hε.eventually (ge_mem_nhds (by norm_num))
  have ht : Tendsto (fun h : ℝ => ∫ x, (polynomialRankOne h).q x * g x ∂haar 1) (𝓝 0)
      (𝓝 (∫ x, g x ∂haar 1)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ : Torus 1 => Real.exp 1 * B)
      (Eventually.of_forall fun h => ((polynomialRankOne h).q_cont.mul hg).aestronglyMeasurable)
      ?_ (integrable_const _) (Eventually.of_forall fun x => by simpa using (hq x).mul_const (g x))
    filter_upwards [hsmall] with h hh
    refine Eventually.of_forall fun x => ?_
    have hqe : (polynomialRankOne h).q x ≤ Real.exp 1 := by
      rw [← Real.exp_log ((polynomialRankOne h).q_pos x)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans ((hlog h x).trans hh))
    rw [norm_mul, Real.norm_of_nonneg ((polynomialRankOne h).q_pos x).le]
    exact mul_le_mul hqe (hB x (Set.mem_univ x)) (norm_nonneg _) (Real.exp_pos 1).le
  simpa only [integral_ref] using ht

/-- An actual sine tilt gives the EXACT moving-reference Rayleigh upper
bound. Positivity of its variance is proved on the actual reference. -/
theorem polynomial_scalarRate_le_sine_rayleigh (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    scalarRate (canonical_elementary_polynomial_model h) b ≤ ENNReal.ofReal
      ((a0 * ∫ x, cosine (angEquiv x) ^ 2 ∂(polynomialRankOne h).ref.measure) /
        (∫ x, sine (angEquiv x) ^ 2 ∂(polynomialRankOne h).ref.measure)) := by
  let M := polynomialRankOne h
  let A := canonical_elementary_polynomial_model h
  let μ := rankOneRef M
  let S : C(Torus 1, ℝ) := ⟨sine ∘ angEquiv, ((isSmoothPeriodic_comp_iff _).2 smooth_sine).continuous_torus⟩
  have hS : IsSmoothPeriodic (fun x => S x) := (isSmoothPeriodic_comp_iff _).2 smooth_sine
  have hval (x : Torus 1) : S x = sine (angEquiv x) := rfl
  have hq (x : Torus 1) : M.q x = density_EX054 h (root_EX054 h) (angEquiv x) := by
    simpa only [MeasurableEquiv.symm_apply_apply] using angular_q h (angEquiv x)
  have hfeature (x : Torus 1) : M.φ x = Real.sqrt 2 *
      (feature_EX054 h (angEquiv x) - moment_EX054 h (root_EX054 h)) := by
    change Real.sqrt 2 * (polyFeature h x - moment_EX054 h (root_EX054 h)) = _
    rw [feature_model_EX054]
  have hmean : ∫ x, S x ∂(μ : Measure (Torus 1)) = 0 := by
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl, integral_ref]
    simp_rw [hq]
    change (∫ x, density_EX054 h (root_EX054 h) (angEquiv x) * sine (angEquiv x) ∂haar 1) = 0
    rw [integral_comp_angEquiv (fun θ => density_EX054 h (root_EX054 h) θ * sine θ)]
    apply odd_integral_zero
    intro θ
    rw [density_reflection_EX054]
    rw [sine_neg]
    ring
  have hφsin : ∫ x, M.φ x * S x ∂(μ : Measure (Torus 1)) = 0 := by
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl, integral_ref]
    simp_rw [hq, hfeature]
    change (∫ x, density_EX054 h (root_EX054 h) (angEquiv x) *
      (Real.sqrt 2 * (feature_EX054 h (angEquiv x) - moment_EX054 h (root_EX054 h)) * sine (angEquiv x)) ∂haar 1) = 0
    rw [integral_comp_angEquiv (fun θ => density_EX054 h (root_EX054 h) θ *
      (Real.sqrt 2 * (feature_EX054 h θ - moment_EX054 h (root_EX054 h)) * sine θ))]
    apply odd_integral_zero
    intro θ
    rw [density_reflection_EX054, feature_reflection_EX054]
    rw [sine_neg]
    ring
  have hQ : 0 < ∫ x, S x * S x ∂(μ : Measure (Torus 1)) := by
    obtain ⟨x0, _, hminq⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty M.q_cont.continuousOn
    have hi := integral_mono (μ := haar 1)
      (((hS.continuous_torus.pow 2).const_mul (M.q x0)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((M.q_cont.mul (hS.continuous_torus.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (fun x =>
          mul_le_mul_of_nonneg_right (hminq (Set.mem_univ x)) (sq_nonneg (S x)))
    change (∫ x, M.q x0 * S x ^ 2 ∂haar 1) ≤ (∫ x, M.q x * S x ^ 2 ∂haar 1) at hi
    rw [integral_const_mul, show (∫ x, S x ^ 2 ∂haar 1) = 1 / 2 from haar_squares.2] at hi
    have hp := (mul_pos (M.q_pos x0) (by norm_num : (0 : ℝ) < 1 / 2)).trans_le hi
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl, integral_ref]
    simpa only [pow_two] using hp
  have hW : M.data.W = A.W := funext fun x => funext fun y => polynomialRankOne_W h x y
  have hkernel (x y : Torus 1) : DGPS.Lipschitz.centeredKernel A (μ : Measure (Torus 1)) x y =
      DGPS.Lipschitz.centeredKernel M.data (μ : Measure (Torus 1)) x y := by
    simp only [DGPS.Lipschitz.centeredKernel, DGPS.Lipschitz.interactionConvolution, interactionEnergy, ← hW]
  have hOp (x : Torus 1) : DGPS.Lipschitz.centeredOperatorC A (μ : Measure (Torus 1)) S x = 0 := by
    change DGPS.Lipschitz.Tcont A (μ : Measure (Torus 1)) (ContinuousMap.toLp 2 (μ : Measure (Torus 1)) ℝ S) x = 0
    rw [DGPS.Lipschitz.Tcont_apply]
    calc
      _ = ∫ y, M.η * (M.φ x * M.φ y) * S y ∂(μ : Measure (Torus 1)) := by
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus 1))) (𝕜 := ℝ) S] with y hy
        rw [hy, hkernel]
        have hk := rankOne_centeredKernel M x y
        change DGPS.Lipschitz.centeredKernel M.data (μ : Measure (Torus 1)) x y = _ at hk
        rw [hk]
      _ = (M.η * M.φ x) * ∫ y, M.φ y * S y ∂(μ : Measure (Torus 1)) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun y => by ring)
      _ = 0 := by rw [hφsin]; ring
  have hmin : ∀ ν : ProbabilityMeasure (Torus 1), freeEnergy A μ ≤ freeEnergy A ν := by
    have hμ : μ = polyEq_EX055 h := by apply Subtype.ext; rfl
    rw [hμ, ← freeEnergyMinimum_eq_EX055]
    intro ν
    exact iInf_le (fun ν => freeEnergy A ν) ν
  obtain ⟨L, _, hLip⟩ := DGPS.Lipschitz.exists_smooth_lipschitz hS
  have ht := DGPS.Lipschitz.scalarRate_le_continuous_tilt A (lipschitzData_canonical_model h)
    b μ hmin S S hLip hLip hmean (fun x => by rw [hOp, add_zero]) hQ
  have hE (x : Torus 1) : ‖smoothGrad (fun y => S y) x‖ ^ 2 = a0 * cosine (angEquiv x) ^ 2 := by
    rw [RankOneModel.norm_sq_tangent, smoothGrad_apply]
    change (coordPartial 0 (sine ∘ angEquiv) x) ^ 2 = _
    rw [coordPartial_comp_angEquiv (ψ := sine) smooth_sine x, sine_derivative]
    unfold a0
    ring
  have hnum : (∫ x, ‖smoothGrad (fun y => S y) x‖ ^ 2 ∂(μ : Measure (Torus 1))) =
      a0 * (∫ x, cosine (angEquiv x) ^ 2 ∂M.ref.measure) := by
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl]
    simp_rw [hE]
    rw [integral_const_mul]
  have hden : (∫ x, S x * S x ∂(μ : Measure (Torus 1))) =
      ∫ x, sine (angEquiv x) ^ 2 ∂M.ref.measure := by
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change S x * S x = sine (angEquiv x) ^ 2
      rw [hval x]
      ring
  rw [hnum, hden] at ht
  exact ht

/-- A genuine actual rate upper bound near zero field, uniform over every
actual drift. This supplies the near-baseline input for minimizer capture. -/
theorem polynomial_scalarRate_eventual_upper (t : ℝ) (ht : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
        scalarRate (canonical_elementary_polynomial_model h) b ≤ ENNReal.ofReal (a0 + t) := by
  have hC := polynomial_reference_moment_tendsto (fun x => cosine (angEquiv x) ^ 2)
    (((isSmoothPeriodic_comp_iff _).2 smooth_cosine).continuous_torus.pow 2)
  have hS := polynomial_reference_moment_tendsto (fun x => sine (angEquiv x) ^ 2)
    (((isSmoothPeriodic_comp_iff _).2 smooth_sine).continuous_torus.pow 2)
  rw [haar_squares.1] at hC
  rw [haar_squares.2] at hS
  have hR : Tendsto (fun h : ℝ => (a0 * ∫ x, cosine (angEquiv x) ^ 2 ∂(polynomialRankOne h).ref.measure) /
      (∫ x, sine (angEquiv x) ^ 2 ∂(polynomialRankOne h).ref.measure)) (𝓝 0) (𝓝 a0) := by
    convert (hC.const_mul a0).div hS (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1 <;> ring
  have he := hR.eventually (ge_mem_nhds (by linarith : a0 < a0 + t))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 he
  refine ⟨δ, hδ, fun h hh b => (polynomial_scalarRate_le_sine_rayleigh h b).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact hb (by simpa only [Real.dist_eq, sub_zero] using hh)

/-- Exact angular-coordinate transport of moments on the actual moving
reference. This exports the coordinate dictionary without exposing private modes. -/
theorem polynomial_reference_moment_angular (h : ℝ) (g : AngCircle → ℝ) :
    (∫ x, g (angEquiv x) ∂(polynomialRankOne h).ref.measure) =
      ∫ θ, density_EX054 h (root_EX054 h) θ * g θ ∂angHaar := by
  rw [integral_ref]
  have he (x : Torus 1) : (polynomialRankOne h).q x =
      density_EX054 h (root_EX054 h) (angEquiv x) := by
    simpa only [MeasurableEquiv.symm_apply_apply] using angular_q h (angEquiv x)
  simp_rw [he]
  exact integral_comp_angEquiv (fun θ => density_EX054 h (root_EX054 h) θ * g θ)

/-- Public physical Rayleigh upper bound in the standard angle sine/cosine
functions; the native scalar rate and exact numerator are unchanged. -/
theorem polynomial_scalarRate_le_angle_sine_rayleigh (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    scalarRate (canonical_elementary_polynomial_model h) b ≤ ENNReal.ofReal
      ((a0 * ∫ x, Real.Angle.cos (angEquiv x) ^ 2 ∂(polynomialRankOne h).ref.measure) /
        (∫ x, Real.Angle.sin (angEquiv x) ^ 2 ∂(polynomialRankOne h).ref.measure)) := by
  simpa only [cosine, sine] using polynomial_scalarRate_le_sine_rayleigh h b

/-- The same exact actual scalar Rayleigh upper bound on the normalized
angular Haar space with the actual moving-reference density. -/
theorem polynomial_scalarRate_le_angular_sine_rayleigh (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    scalarRate (canonical_elementary_polynomial_model h) b ≤ ENNReal.ofReal
      ((a0 * ∫ θ, density_EX054 h (root_EX054 h) θ * Real.Angle.cos θ ^ 2 ∂angHaar) /
        (∫ θ, density_EX054 h (root_EX054 h) θ * Real.Angle.sin θ ^ 2 ∂angHaar)) := by
  have ht := polynomial_scalarRate_le_angle_sine_rayleigh h b
  rw [polynomial_reference_moment_angular h (fun θ => Real.Angle.cos θ ^ 2),
    polynomial_reference_moment_angular h (fun θ => Real.Angle.sin θ ^ 2)] at ht
  exact ht

end DGPS.Examples.PolynomialSpecies
