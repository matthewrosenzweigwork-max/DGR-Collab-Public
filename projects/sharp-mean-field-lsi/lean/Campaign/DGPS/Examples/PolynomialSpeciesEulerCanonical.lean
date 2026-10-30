import DGPS.Examples.PolynomialSpeciesEuler
import DGPS.Frontier.STR029.T62
import DGPS.Variational.SpeciesInclusion

/-! Transport of the actual moving-reference C2 logarithmic chart to the original
absolute square-root H1 domain. No positivity of the gap or optimizer assumption occurs. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open DGPS.Frontier.STR029 DGPS.PositiveRankOne
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux

namespace DGPS.Examples.PolynomialSpecies

/-- Actual partition function, with the moving normalized reference included. -/
def polynomialChartPartition (h : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  Z_STR02954 (0, polynomialLogReference h + e0_STR02955 u)

private theorem partition_pos (h : ℝ) (u : PeriodicC2_STR02969) :
    0 < polynomialChartPartition h u := Z_pos_STR02954 _

/-- Relative square root of the normalized density with respect to the actual qhat. -/
def polynomialChartRoot (h : ℝ) (u : PeriodicC2_STR02969) (θ : AngCircle) : ℝ :=
  Real.exp ((u.val (angSec θ) - Real.log (polynomialChartPartition h u)) / 2)

private def rootDerivative (h : ℝ) (u : PeriodicC2_STR02969) (θ : AngCircle) : ℝ :=
  polynomialChartRoot h u θ * deriv u.val (angSec θ) / 2

private theorem root_weak (h : ℝ) (u : PeriodicC2_STR02969) :
    IsAngularWeakDeriv (polynomialChartRoot h u) (rootDerivative h u) := by
  apply isAngularWeakDeriv_lift_STR02962
    (f := fun t => Real.exp ((u.val t - Real.log (polynomialChartPartition h u)) / 2))
    (f' := fun t => Real.exp ((u.val t - Real.log (polynomialChartPartition h u)) / 2) *
      deriv u.val t / 2)
  · intro t
    convert (((u.isC2.2.1 t).hasDerivAt.sub_const
      (Real.log (polynomialChartPartition h u))).div_const 2).exp using 1
    ring
  · have hc := u.isC2.2.1.continuous
    have hdc := u.isC2.2.2.1.continuous
    fun_prop
  · intro t
    change Real.exp ((u.val (t + 2 * Real.pi) - Real.log (polynomialChartPartition h u)) / 2) =
      Real.exp ((u.val t - Real.log (polynomialChartPartition h u)) / 2)
    rw [u.isC2.1 t]

private theorem root_sq (h : ℝ) (u : PeriodicC2_STR02969) (θ : AngCircle) :
    polynomialChartRoot h u θ ^ 2 = Real.exp (u.val (angSec θ)) / polynomialChartPartition h u := by
  unfold polynomialChartRoot
  rw [sq, ← Real.exp_add, add_halves, Real.exp_sub, Real.exp_log (partition_pos h u)]

private theorem root_sq_density (h : ℝ) (u : PeriodicC2_STR02969) (θ : AngCircle) :
    polynomialChartRoot h u θ ^ 2 * (polynomialRankOne h).q (angEquiv.symm θ) =
      (eulerDensity (polynomialLogReference h) u).val (angSec θ) := by
  rw [root_sq, polynomialEuler_density_val]
  have hq : (polynomialRankOne h).q (angEquiv.symm ((angSec θ : ℝ) : AngCircle)) =
      (polynomialRankOne h).q (angEquiv.symm θ) := by rw [coe_angSec]
  have hZ : meanT_STR02901 (fun s => (polynomialRankOne h).q (angEquiv.symm (s : AngCircle)) *
      Real.exp (u.val s)) = polynomialChartPartition h u := by
    rw [polynomialChartPartition, Z_eq_meanT_STR02954]
    simp only [zero_mul, zero_add, PeriodicHolder_STR02968.val_add, Pi.add_apply,
      e0_val_STR02955]
    change _ = meanT_STR02901 (fun s => Real.exp
      (Real.log ((polynomialRankOne h).q (angEquiv.symm (s : AngCircle))) + u.val s))
    simp_rw [Real.exp_add, Real.exp_log ((polynomialRankOne h).q_pos _)]
  rw [hq, hZ]
  ring

private theorem root_mass (h : ℝ) (u : PeriodicC2_STR02969) :
    ∫ x, polynomialChartRoot h u (angEquiv x) ^ 2 * (polynomialRankOne h).q x ∂haar 1 = 1 := by
  have he : (fun x => polynomialChartRoot h u (angEquiv x) ^ 2 * (polynomialRankOne h).q x) =
      (fun θ => (eulerDensity (polynomialLogReference h) u).val (angSec θ)) ∘ angEquiv := by
    funext x
    simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using root_sq_density h u (angEquiv x)
  rw [he]
  change (∫ x, (eulerDensity (polynomialLogReference h) u).val (angSec (angEquiv x)) ∂haar 1) = 1
  rw [integral_comp_angEquiv (fun θ => (eulerDensity (polynomialLogReference h) u).val (angSec θ)),
    integral_angSec_STR02962 (eulerDensity (polynomialLogReference h) u).val]
  change meanT_STR02901 (eulerDensity (polynomialLogReference h) u).val = 1
  have heR : (eulerDensity (polynomialLogReference h) u).val =
      rhoT_STR02901 0 (polynomialLogReference h + e0_STR02955 u).val :=
    funext (rho_val_STR02954 _)
  rw [heR]
  exact meanT_rho_STR02950 0 (polynomialLogReference h + e0_STR02955 u).isPerHolder.2.1

/-- Each actual C2 log chart is an original absolute-admissible density. -/
def polynomialChartAbsolute (h : ℝ) (u : PeriodicC2_STR02969) : AbsoluteDensity 1 where
  sqrt := fun x => polynomialChartRoot h u (angEquiv x) * Real.sqrt ((polynomialRankOne h).q x)
  sqrt_mem := by
    have hw := (isWeakGradient_comp_iff _ _).1 (root_weak h u)
    have hw' := RelativeFisher.mul_rpow_isWeakGradient (polynomialRankOne h).ref_lip
      (r := (1 / 2 : ℝ)) (by norm_num) hw
    rw [mem_H1Haar]
    convert (show MemH1 (fun x => polynomialChartRoot h u (angEquiv x) *
      (polynomialRankOne h).q x ^ (1 / 2 : ℝ)) from ⟨_, hw'⟩) using 1
    ext x
    rw [Real.sqrt_eq_rpow]
  sqrt_nonneg := Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  mass_one := by
    simp_rw [mul_pow, Real.sq_sqrt ((polynomialRankOne h).q_pos _).le]
    exact root_mass h u

/-- The original absolute density has the exact normalized moving-reference density. -/
theorem polynomialChartAbsolute_density (h : ℝ) (u : PeriodicC2_STR02969) (x : Torus 1) :
    (polynomialChartAbsolute h u).density x =
      (eulerDensity (polynomialLogReference h) u).val (angSec (angEquiv x)) := by
  change (polynomialChartRoot h u (angEquiv x) * Real.sqrt ((polynomialRankOne h).q x)) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt ((polynomialRankOne h).q_pos x).le]
  simpa only [MeasurableEquiv.symm_apply_apply] using root_sq_density h u (angEquiv x)

/-- Integration of any chart observable agrees with normalized expectation. -/
theorem polynomialChartAbsolute_integral (h : ℝ) (u : PeriodicC2_STR02969)
    (f : PeriodicHolder_STR02968) :
    ∫ x, f.val (angSec (angEquiv x)) ∂(densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1)) =
      eulerMean (polynomialLogReference h) u f := by
  rw [RankOneModel.integral_densityMeasure]
  simp_rw [polynomialChartAbsolute_density]
  rw [integral_comp_angEquiv (fun θ => (eulerDensity (polynomialLogReference h) u).val (angSec θ) *
    f.val (angSec θ))]
  change (∫ θ, (fun t => (eulerDensity (polynomialLogReference h) u).val t * f.val t)
    (angSec θ) ∂angHaar) = _
  rw [integral_angSec_STR02962 (fun t => (eulerDensity (polynomialLogReference h) u).val t * f.val t)]
  change meanT_STR02901 (fun t => (eulerDensity (polynomialLogReference h) u).val t * f.val t) = _
  unfold eulerMean
  rw [meanCLM_apply_STR02954]
  congr 1
  funext t
  rw [val_mul_STR02954, Pi.mul_apply, mul_comm]

private theorem observable_val (h : ℝ) (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f)
    (F : PeriodicHolder_STR02968)
    (hF : ∀ t, F.val t = f (angEquiv.symm (t : AngCircle)))
    (u : PeriodicC2_STR02969) :
    ∫ x, f x ∂(densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1)) =
      eulerMean (polynomialLogReference h) u F := by
  rw [← polynomialChartAbsolute_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change f x = F.val (angSec (angEquiv x))
    rw [hF, coe_angSec, MeasurableEquiv.symm_apply_apply]

private theorem root_measure (h : ℝ) (u : PeriodicC2_STR02969) :
    (densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1)) =
      (polynomialRankOne h).ref.measure.withDensity
        (fun x => ENNReal.ofReal (polynomialChartRoot h u (angEquiv x) ^ 2)) := by
  let M := polynomialRankOne h
  let f := fun x => polynomialChartRoot h u (angEquiv x)
  have hw := (isWeakGradient_comp_iff _ _).1 (root_weak h u)
  have hf : AEMeasurable (fun x => ENNReal.ofReal (f x ^ 2)) (haar 1) :=
    (hw.memLp.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  change (haar 1).withDensity (fun x => ENNReal.ofReal ((f x * Real.sqrt (M.q x)) ^ 2)) =
    ((haar 1).withDensity (fun x => ENNReal.ofReal (M.q x))).withDensity _
  rw [← withDensity_mul₀ M.q_cont.measurable.ennreal_ofReal.aemeasurable hf]
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => by
    change ENNReal.ofReal ((f x * Real.sqrt (M.q x)) ^ 2) =
      ENNReal.ofReal (M.q x) * ENNReal.ofReal (f x ^ 2)
    rw [mul_pow, Real.sq_sqrt (M.q_pos x).le, ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_comm _ _

private theorem relative_root_ae (h : ℝ) (u : PeriodicC2_STR02969) :
    relativeSqrt (densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1))
      (polynomialRankOne h).ref =ᵐ[haar 1] fun x => polynomialChartRoot h u (angEquiv x) := by
  let P := (polynomialRankOne h).ref
  have hw := (isWeakGradient_comp_iff _ _).1 (root_weak h u)
  have hp := (isWeightedWeakGradient_iff P).2 hw
  have hRN := Measure.rnDeriv_withDensity₀ P.measure
    (hp.memLp.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hRN' := P.haar_ac_measure.ae_eq hRN
  filter_upwards [hRN'] with x hx
  unfold relativeSqrt
  rw [root_measure]
  change Real.sqrt (((P.measure.withDensity (fun y => ENNReal.ofReal
    (polynomialChartRoot h u (angEquiv y) ^ 2))).rnDeriv P.measure x).toReal) = _
  change (P.measure.withDensity (fun y => ENNReal.ofReal
    (polynomialChartRoot h u (angEquiv y) ^ 2))).rnDeriv P.measure x =
      ENNReal.ofReal (polynomialChartRoot h u (angEquiv x) ^ 2) at hx
  rw [hx, ENNReal.toReal_ofReal (sq_nonneg _)]
  exact Real.sqrt_sq (show 0 ≤ polynomialChartRoot h u (angEquiv x) from (Real.exp_pos _).le)

private theorem mean_lift_physical (f : Torus 1 → ℝ) :
    meanT_STR02901 (fun t => f (angEquiv.symm (t : AngCircle))) = ∫ x, f x ∂haar 1 := by
  change (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi, f (angEquiv.symm (t : AngCircle))) = _
  rw [← integral_angSec_STR02962]
  simp_rw [coe_angSec]
  symm
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
    integral_comp_angEquiv (fun θ => f (angEquiv.symm θ))

private theorem reference_partition_one (h : ℝ) :
    Z_STR02954 (0, polynomialLogReference h) = 1 := by
  rw [Z_eq_meanT_STR02954]
  simp only [zero_mul, zero_add]
  change meanT_STR02901 (fun t => Real.exp (Real.log
    ((polynomialRankOne h).q (angEquiv.symm (t : AngCircle))))) = 1
  simp_rw [Real.exp_log ((polynomialRankOne h).q_pos _)]
  rw [mean_lift_physical, (polynomialRankOne h).q_mass]

private theorem density_log (h : ℝ) (u : PeriodicC2_STR02969) (x : Torus 1) :
    Real.log ((polynomialChartAbsolute h u).density x) =
      Real.log ((polynomialRankOne h).q x) + u.val (angSec (angEquiv x)) -
        Real.log (polynomialChartPartition h u) := by
  change Real.log ((polynomialChartRoot h u (angEquiv x) * Real.sqrt ((polynomialRankOne h).q x)) ^ 2) = _
  rw [mul_pow, Real.sq_sqrt ((polynomialRankOne h).q_pos x).le, root_sq,
    Real.log_mul (div_pos (Real.exp_pos _) (partition_pos h u)).ne' ((polynomialRankOne h).q_pos x).ne',
    Real.log_div (Real.exp_pos _).ne' (partition_pos h u).ne', Real.log_exp]
  ring

/-- The actual relative entropy is exactly the chart entropy. No entropy-positive assumption is needed. -/
theorem polynomialChartAbsolute_entropy (h : ℝ) (u : PeriodicC2_STR02969) :
    (relativeEntropy (densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1))
      (polynomialRankOne h).ref.measure).toReal = eulerEntropy (polynomialLogReference h) u := by
  let M := polynomialRankOne h
  let ρ := polynomialChartAbsolute h u
  let c := Real.log (polynomialChartPartition h u)
  have hi := (absoluteDensity_entropy_finite ρ).1
  have hq := RankOneModel.integrable_density_mul ρ M.log_smooth.continuous_torus
  have huI : Integrable (fun x => ρ.density x * u.val (angSec (angEquiv x))) (haar 1) := by
    convert (hi.sub hq).add (ρ.integrable_density.const_mul c) using 1
    ext x
    have hl := density_log h u x
    change ρ.density x * u.val (angSec (angEquiv x)) =
      ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (M.q x) + c * ρ.density x
    change Real.log (ρ.density x) = Real.log (M.q x) + u.val (angSec (angEquiv x)) - c at hl
    rw [hl]
    ring
  rw [M.entropy_ref_eq _ (absoluteDensity_entropy_finite ρ).2.2.1,
    ← circleEntropy_eq_relativeEntropy, ThreeSpeciesCircle.circleEntropy_eq,
    RankOneModel.integral_densityMeasure]
  calc (∫ x, ρ.density x * Real.log (ρ.density x) ∂haar 1) -
      (∫ x, ρ.density x * Real.log (M.q x) ∂haar 1) =
      (∫ x, ρ.density x * u.val (angSec (angEquiv x)) ∂haar 1) - c := by
        rw [← integral_sub hi hq]
        have he : (fun x => ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (M.q x)) =
            fun x => ρ.density x * u.val (angSec (angEquiv x)) - c * ρ.density x := by
          ext x
          have hl := density_log h u x
          change Real.log (ρ.density x) = Real.log (M.q x) + u.val (angSec (angEquiv x)) - c at hl
          rw [hl]
          ring
        rw [he, integral_sub huI (ρ.integrable_density.const_mul c), integral_const_mul,
          ρ.integral_density, mul_one]
    _ = eulerMean (polynomialLogReference h) u (e0_STR02955 u) - c := by
        rw [← polynomialChartAbsolute_integral, RankOneModel.integral_densityMeasure]
        rfl
    _ = eulerEntropy (polynomialLogReference h) u := by
        simp only [eulerEntropy, reference_partition_one, Real.log_one, add_zero]
        rfl

private theorem lintegral_enorm_sq {α : Type*} [MeasurableSpace α] {P : Measure α}
    {g : α → ℝ} (hg : MemLp g 2 P) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ x, g x ^ 2 ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- Ordinary relative Fisher information has exactly the physical chart normalization. -/
theorem polynomialChartAbsolute_fisher (h : ℝ) (u : PeriodicC2_STR02969) :
    ordinaryRelativeFisher (densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1))
      (polynomialRankOne h).ref = ENNReal.ofReal (eulerFisher (polynomialLogReference h) u) := by
  let M := polynomialRankOne h
  let P := M.ref
  let ρ := polynomialChartAbsolute h u
  let g := rootDerivative h u
  have hw := (isWeakGradient_comp_iff _ _).1 (root_weak h u)
  have hwr := hw.congr_ae (relative_root_ae h u).symm (EventuallyEq.refl _ _)
  have hac : (densityMeasure ρ : Measure (Torus 1)) ≪ P.measure := by
    rw [root_measure]
    exact withDensity_absolutelyContinuous _ _
  have hg : MemLp (g ∘ angEquiv) 2 P.measure :=
    (memLp_physGrad_iff P.measure g).1 (((isWeightedWeakGradient_iff P).2 hw).memLp_grad)
  have hm := polynomialChartAbsolute_integral h u (e1_STR02955 u * e1_STR02955 u)
  rw [RankOneModel.integral_densityMeasure] at hm
  have hJ : ∫ x, g (angEquiv x) ^ 2 ∂P.measure =
      (1 / 4 : ℝ) * eulerMean (polynomialLogReference h) u (e1_STR02955 u * e1_STR02955 u) := by
    rw [LocalGaussianEndpoint.integral_ref_eq]
    rw [← hm, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change M.q x * (polynomialChartRoot h u (angEquiv x) * deriv u.val (angSec (angEquiv x)) / 2) ^ 2 = _
      change _ = (1 / 4 : ℝ) * ((polynomialChartRoot h u (angEquiv x) * Real.sqrt (M.q x)) ^ 2 *
        (deriv u.val (angSec (angEquiv x)) * deriv u.val (angSec (angEquiv x))))
      rw [mul_pow, Real.sq_sqrt (M.q_pos x).le]
      ring
  rw [ordinaryRelativeFisher_eq hac hwr]
  simp_rw [enorm_physGrad_sq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change 4 * (ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 *
    ∫⁻ x, ‖g (angEquiv x)‖ₑ ^ 2 ∂P.measure) = _
  rw [lintegral_enorm_sq (show MemLp (fun x => g (angEquiv x)) 2 P.measure from hg), hJ]
  change 4 * (ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * ENNReal.ofReal _) = _
  rw [← ENNReal.ofReal_mul DGPS.Circle.AngularNormalization.a0_pos.le,
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  unfold eulerFisher
  ring

/-- Gap and dissipation for the original canonical scalar model coincide with the actual
moving-reference chart quantities. All original absolute drifts are retained. -/
theorem polynomialChartAbsolute_gap_and_dissipation (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (u : PeriodicC2_STR02969) :
    let L := polynomialLogReference h
    let m := eulerMean L u (polynomialEulerFeature h)
    let A := eulerMean L u (polynomialEulerGenerator h)
    let J := eulerMean L u (polynomialEulerGradientSq h)
    (scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h u) : ℝ) =
        eulerEntropy L u + eta * m ^ 2 / 2 ∧
      scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u) ≠ ⊤ ∧
      (scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u)).toReal =
        eulerFisher L u + 2 * eta * m * A + eta ^ 2 * m ^ 2 * J := by
  let M := polynomialRankOne h
  let ρ := polynomialChartAbsolute h u
  have ht := DGPS.Examples.positive_rank_one_scalar_case M (polynomialRankOneDrift h b) ρ
  rw [polynomialRankOne_speciesGap, polynomialRankOne_speciesDissipation,
    speciesGap_single, speciesDissipation_single] at ht
  have hp := observable_val h M.φ M.φ_smooth (polynomialEulerFeature h) (fun _ => rfl) u
  have hA := observable_val h M.Aq (by
    exact (M.dφ_smooth.isSmoothPeriodic_coordPartial 0).neg.sub
      ((M.log_smooth.isSmoothPeriodic_coordPartial 0).mul M.dφ_smooth))
    (polynomialEulerGenerator h) (fun _ => rfl) u
  have hJ := observable_val h (fun x => M.dφ x ^ 2) (M.dφ_smooth.pow 2)
    (polynomialEulerGradientSq h) (fun _ => rfl) u
  have hIf : (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal =
      eulerFisher (polynomialLogReference h) u := by
    rw [polynomialChartAbsolute_fisher, ENNReal.toReal_ofReal]
    unfold eulerFisher
    apply mul_nonneg DGPS.Circle.AngularNormalization.a0_pos.le
    rw [← polynomialChartAbsolute_integral]
    apply integral_nonneg
    intro x
    change 0 ≤ deriv u.val (angSec (angEquiv x)) * deriv u.val (angSec (angEquiv x))
    exact mul_self_nonneg _
  change (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) = _ at hp
  change (∫ x, M.Aq x ∂(densityMeasure ρ : Measure (Torus 1))) = _ at hA
  change (∫ x, M.dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) = _ at hJ
  have hEnt : (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal =
      eulerEntropy (polynomialLogReference h) u := polynomialChartAbsolute_entropy h u
  simp only [show M.η = eta from rfl, hp, hA, hJ, hEnt, hIf] at ht
  exact ⟨by linarith [ht.1], ht.2.2.1, ht.2.2.2⟩

/-- The canonical scalar deficit is precisely the functional differentiated by the Euler leaf. -/
theorem polynomialChartAbsolute_deficit (h r : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (u : PeriodicC2_STR02969) :
    (scalarDissipation (canonical_elementary_polynomial_model h) b (polynomialChartAbsolute h u)).toReal -
      2 * r * (scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h u) : ℝ) =
        polynomialChartDeficit h r u := by
  obtain ⟨hG, hDfin, hD⟩ := polynomialChartAbsolute_gap_and_dissipation h b u
  rw [hG, hD]
  unfold polynomialChartDeficit
  ring

end DGPS.Examples.PolynomialSpecies
