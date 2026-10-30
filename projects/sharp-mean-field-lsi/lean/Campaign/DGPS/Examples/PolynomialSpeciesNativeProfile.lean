import DGPS.Examples.PolynomialSmooth
import DGPS.Examples.PolynomialSpeciesRangeRestriction
import DGPS.Circle.FirstClusterPerturbation

/-! Factual native probability and smooth logarithmic representative of the
SAME actual minimizer chart. The original stored root keeps its AE convention.
This adapter assumes only the genuine smooth representative and exact chart
identification supplied by their owning producers, never a spectral margin. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
open DGPS.Circle.FirstClusterPerturbation

namespace DGPS.Examples.PolynomialSpecies

private theorem native_chart_density (h : ℝ) (u : PeriodicC2_STR02969) (x : Torus 1) :
    (polynomialChartAbsolute h u).density x = rhoT_STR02901 0
      (polynomialRangeLogWeight (h, PolynomialEquilibrium.root_EX054 h) + u).val (angSec (angEquiv x)) := by
  rw [polynomialChartAbsolute_density, ← polynomialRangeDensity_actual]
  simp only [eulerDensity, rho_val_STR02954, PeriodicHolder_STR02968.val_add,
    e0_val_STR02955, PeriodicC2_STR02969.val_add, Pi.add_apply]

private theorem native_chart_continuous (h : ℝ) (u : PeriodicC2_STR02969) :
    Continuous (polynomialChartAbsolute h u).density := by
  let F := polynomialRangeLogWeight (h, PolynomialEquilibrium.root_EX054 h) + u
  have hp := periodic_rho_STR02950 0 F.isC2.1
  have hc : Continuous (fun θ : AngCircle => rhoT_STR02901 0 F.val (angSec θ)) := by
    change Continuous (AddCircle.liftIoc (2 * Real.pi) 0 (rhoT_STR02901 0 F.val))
    exact AddCircle.liftIoc_zero_continuous (by simpa using (hp 0).symm)
      (continuous_rho_STR02950 0 F.isC2.2.1.continuous).continuousOn
  have ha : Continuous (angEquiv : Torus 1 → AngCircle) := by
    change Continuous (fun x : Torus 1 => angHomeo (x 0))
    exact angHomeo.continuous.comp (continuous_apply 0)
  have he : (polynomialChartAbsolute h u).density =
      fun x => rhoT_STR02901 0 F.val (angSec (angEquiv x)) := funext (native_chart_density h u)
  rw [he]
  exact hc.comp ha

/-- The same native probability has an actual bounded positive reference and
a smooth angular UNNORMALIZED log profile equal to the retained chart. No
pointwise claim about the original chosen root or its gradient is made. -/
theorem polynomial_native_chart_profile_data (h : ℝ) (u : PeriodicC2_STR02969)
    (ρ : AbsoluteDensity 1) (v : Torus 1 → ℝ) (hv : IsSmoothPeriodic v)
    (hlog : IsSmoothPeriodic (fun x => Real.log (v x ^ 2)))
    (hrep : ρ.sqrt =ᵐ[haar 1] v) (hlo : ∀ x, (1 / 2 : ℝ) ≤ v x)
    (hchart : ρ.density =ᵐ[haar 1] (polynomialChartAbsolute h u).density) :
    ∃ (P : BoundedPositiveReference 1) (ell : AngCircle → ℝ),
      (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) = densityMeasure ρ ∧
      IsSmoothAngular ell ∧
      (∀ t : ℝ, ell (t : AngCircle) =
        (polynomialRangeLogWeight (h, PolynomialEquilibrium.root_EX054 h) + u).val t) ∧
      P.density = angularGibbs_EX009 ell := by
  have hvc : Continuous v := hv.continuous_torus
  have hvpos (x : Torus 1) : 0 < v x := lt_of_lt_of_le (by norm_num) (hlo x)
  have hv2 : Continuous (fun x => v x ^ 2) := hvc.pow 2
  have hvrep : ρ.density =ᵐ[haar 1] (fun x => v x ^ 2) := by
    filter_upwards [hrep] with x hx
    change ρ.sqrt x ^ 2 = v x ^ 2
    rw [hx]
  have hmass : ∫ x, v x ^ 2 ∂haar 1 = 1 := by
    rw [← integral_congr_ae hvrep]
    exact ρ.mass_one
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hv2.continuousOn
  let P : BoundedPositiveReference 1 :=
    { density := fun x => v x ^ 2
      measurable_density := hv2.measurable
      lower := 1 / 4
      upper := v xmax ^ 2
      lower_pos := by norm_num
      lower_le := Eventually.of_forall fun x => by nlinarith only [hlo x]
      le_upper := Eventually.of_forall fun x => hxmax (Set.mem_univ x)
      mass_one := hmass }
  have hPm : P.measure = (densityMeasure ρ : Measure (Torus 1)) := by
    apply withDensity_congr_ae
    filter_upwards [hvrep] with x hx
    change ENNReal.ofReal (v x ^ 2) = ENNReal.ofReal (ρ.density x)
    rw [hx]
  have hprob : (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      densityMeasure ρ := ProbabilityMeasure.toMeasure_injective hPm
  let F := polynomialRangeLogWeight (h, PolynomialEquilibrium.root_EX054 h) + u
  let Z := meanT_STR02901 (fun s => Real.exp (F.val s))
  have hZ : 0 < Z := meanT_pos_STR02901
    (Real.continuous_exp.comp F.isC2.2.1.continuous) (fun s => Real.exp_pos _)
  let ell : AngCircle → ℝ := fun θ => Real.log (v (angEquiv.symm θ) ^ 2) + Real.log Z
  have hell : IsSmoothAngular ell := by
    apply (isSmoothPeriodic_comp_iff ell).1
    have heq : ell ∘ (angEquiv : Torus 1 → AngCircle) =
        (fun x : Torus 1 => Real.log (v x ^ 2) + Real.log Z) := by
      funext x
      simp only [ell, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    rw [heq]
    change ContDiff ℝ ∞ (fun x => Real.log (v (torusLift x) ^ 2) + Real.log Z)
    exact hlog.add contDiff_const
  have hpoint : (fun x => v x ^ 2) = (polynomialChartAbsolute h u).density :=
    Measure.eq_of_ae_eq (hvrep.symm.trans hchart) hv2 (native_chart_continuous h u)
  have hlift (t : ℝ) : ell (t : AngCircle) = F.val t := by
    have he := congrFun hpoint (angEquiv.symm (t : AngCircle))
    rw [native_chart_density, MeasurableEquiv.apply_symm_apply] at he
    have hper := periodic_rho_STR02950 0 F.isC2.1
    have hr : rhoT_STR02901 0 F.val (angSec (t : AngCircle)) = rhoT_STR02901 0 F.val t := by
      calc
        _ = hper.lift ((angSec (t : AngCircle) : ℝ) : AngCircle) := (hper.lift_coe _).symm
        _ = hper.lift (t : AngCircle) := by rw [coe_angSec_STR02962]
        _ = _ := hper.lift_coe t
    have ht := gate_str029_01_bind_common_optimizer_witness_absolute_variational_positive_log
      0 F.isC2.2.1.continuous t
    dsimp only [ell]
    rw [he, hr, ht.2]
    simp only [zero_mul, zero_add, Z]
    ring
  have hexp (x : Torus 1) : Real.exp (ell (angEquiv x)) = Z * v x ^ 2 := by
    simp only [ell, MeasurableEquiv.symm_apply_apply, Real.exp_add,
      Real.exp_log (sq_pos_of_pos (hvpos x)), Real.exp_log hZ]
    ring
  have hGibbs : P.density = angularGibbs_EX009 ell := by
    funext x
    change v x ^ 2 = Real.exp (-(-ell (angEquiv x))) /
      (∫ y, Real.exp (-(-ell (angEquiv y))) ∂haar 1)
    simp only [neg_neg]
    simp_rw [hexp]
    rw [integral_const_mul, hmass, mul_one]
    field_simp [hZ.ne']
  exact ⟨P, ell, hprob, hell, hlift, hGibbs⟩

end DGPS.Examples.PolynomialSpecies
