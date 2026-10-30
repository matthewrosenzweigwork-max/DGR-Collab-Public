import DGPS.Examples.PolynomialSpeciesReflectionOptimizers

/-! Probability-law injectivity for the actual centered polynomial chart and
its exact cosine/sine coordinates. No chosen representative of an arbitrary
absolute density is asserted pointwise equal. -/
noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

theorem polynomialChartAbsolute_injective_meanZero (h : ℝ) (u v : PeriodicC2_STR02969)
    (hu : meanT_STR02901 u.val = 0) (hv : meanT_STR02901 v.val = 0)
    (hμ : (densityMeasure (polynomialChartAbsolute h u) : Measure (Torus 1)) =
      densityMeasure (polynomialChartAbsolute h v)) : u = v := by
  let du := eulerDensity (polynomialLogReference h) u
  let dv := eulerDensity (polynomialLogReference h) v
  have angular_cont (d : PeriodicHolder_STR02968) :
      Continuous (fun θ : AngCircle => d.val (angSec θ)) := by
    change Continuous (AddCircle.liftIoc (2 * Real.pi) 0 d.val)
    exact AddCircle.liftIoc_zero_continuous (by simpa using (d.isPerHolder.1 0).symm)
      d.isPerHolder.2.1.continuousOn
  have ha : Continuous (angEquiv : Torus 1 → AngCircle) := by
    change Continuous (fun x : Torus 1 => angHomeo (x 0))
    exact angHomeo.continuous.comp (continuous_apply 0)
  have heae : (fun x : Torus 1 => du.val (angSec (angEquiv x))) =ᵐ[haar 1]
      fun x => dv.val (angSec (angEquiv x)) := by
    have hd := (densityMeasure_eq_iff_STR02901 (polynomialChartAbsolute h u)
      (polynomialChartAbsolute h v)).1 hμ
    filter_upwards [hd] with x hx
    rw [polynomialChartAbsolute_density, polynomialChartAbsolute_density] at hx
    exact hx
  have he := MeasureTheory.Measure.eq_of_ae_eq heae ((angular_cont du).comp ha) ((angular_cont dv).comp ha)
  have hval (t : ℝ) : du.val t = dv.val t := by
    have ht := congrFun he (angEquiv.symm (t : AngCircle))
    simp only [MeasurableEquiv.apply_symm_apply] at ht
    have lift_eval (d : PeriodicHolder_STR02968) : d.val (angSec (t : AngCircle)) = d.val t := by
      calc
        _ = d.isPerHolder.1.lift (t : AngCircle) := by
          rw [← d.isPerHolder.1.lift_coe (angSec (t : AngCircle)), coe_angSec_STR02962]
        _ = _ := d.isPerHolder.1.lift_coe t
    simpa only [lift_eval du, lift_eval dv] using ht
  let cu := -Real.log (meanT_STR02901 (fun s => Real.exp ((polynomialLogReference h).val s + u.val s)))
  let cv := -Real.log (meanT_STR02901 (fun s => Real.exp ((polynomialLogReference h).val s + v.val s)))
  have hfun : (fun t => u.val t + cu) = fun t => v.val t + cv := by
    funext t
    have ht := congrArg Real.log (hval t)
    change Real.log ((rho_STR02954 (0, polynomialLogReference h + e0_STR02955 u)).val t) =
      Real.log ((rho_STR02954 (0, polynomialLogReference h + e0_STR02955 v)).val t) at ht
    rw [rho_val_STR02954, rho_val_STR02954] at ht
    simp only [rhoT_STR02901, zero_mul, zero_add, PeriodicHolder_STR02968.val_add,
      Pi.add_apply, e0_val_STR02955] at ht
    have hZu : 0 < meanT_STR02901 (fun s => Real.exp ((polynomialLogReference h).val s + u.val s)) :=
      meanT_pos_STR02901
        (Real.continuous_exp.comp ((polynomialLogReference h).isPerHolder.2.1.add (continuous_val_STR02924 u)))
        (fun s => Real.exp_pos _)
    have hZv : 0 < meanT_STR02901 (fun s => Real.exp ((polynomialLogReference h).val s + v.val s)) :=
      meanT_pos_STR02901
        (Real.continuous_exp.comp ((polynomialLogReference h).isPerHolder.2.1.add (continuous_val_STR02924 v)))
        (fun s => Real.exp_pos _)
    rw [Real.log_div (Real.exp_pos _).ne' hZu.ne',
      Real.log_div (Real.exp_pos _).ne' hZv.ne', Real.log_exp, Real.log_exp] at ht
    dsimp only [cu, cv]
    linarith only [ht]
  have hm := congrArg meanT_STR02901 hfun
  have hc : cu = cv := by
    change meanT_STR02901 (u.val + fun _ => cu) = meanT_STR02901 (v.val + fun _ => cv) at hm
    rw [meanT_add_STR02953 (continuous_val_STR02924 u) continuous_const,
      meanT_add_STR02953 (continuous_val_STR02924 v) continuous_const, hu, hv] at hm
    simpa [meanT_STR02901] using hm
  apply Subtype.ext
  funext t
  have ht := congrFun hfun t
  rw [hc] at ht
  change u.val t = v.val t
  exact add_right_cancel ht

/-- The genuine range correction has zero constant and first harmonic
coordinates, so the displayed amplitudes are recoverable exactly. -/
theorem polynomialChart_amplitude_coordinates (a b : ℝ) (w : E_STR02969) :
    let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)
    meanT_STR02901 u.val = 0 ∧
      pair_STR02953 Real.cos u.val = a / 2 ∧ pair_STR02953 Real.sin u.val = b / 2 := by
  let L0 := c2Data_STR02969.pairCLM (fun _ => 1) continuous_const (fun _ => by simp)
  let Lc := c2Data_STR02969.pairCLM Real.cos Real.continuous_cos Real.abs_cos_le_one
  let Ls := c2Data_STR02969.pairCLM Real.sin Real.continuous_sin Real.abs_sin_le_one
  have hM (u : PeriodicC2_STR02969) : L0 u = meanT_STR02901 u.val := by
    change pair_STR02953 (fun _ => 1) u.val = _
    simp [pair_STR02953]
  have hw := (c2Data_STR02969.mem_sub_iff (w : PeriodicC2_STR02969)).1 w.property
  have hw0 : L0 (w : PeriodicC2_STR02969) = 0 := (hM _).trans hw.1
  have hwc : Lc (w : PeriodicC2_STR02969) = 0 := hw.2.1
  have hws : Ls (w : PeriodicC2_STR02969) = 0 := hw.2.2
  have h0c : L0 cosC2_STR02915 = 0 := (hM _).trans meanT_cos_STR02955
  have h0s : L0 sinC2_STR02915 = 0 := (hM _).trans meanT_sin_STR02955
  have hcc : Lc cosC2_STR02915 = 1 / 2 := meanT_cc_STR02955
  have hcs : Lc sinC2_STR02915 = 0 := meanT_sc_STR02955
  have hsc : Ls cosC2_STR02915 = 0 := by
    change meanT_STR02901 (fun t => Real.cos t * Real.sin t) = 0
    simpa only [mul_comm] using meanT_sc_STR02955
  have hss : Ls sinC2_STR02915 = 1 / 2 := meanT_ss_STR02955
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [← hM, map_add, map_add, map_smul, map_smul, h0c, h0s, hw0]
    simp
  · change Lc (a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)) = a / 2
    rw [map_add, map_add, map_smul, map_smul, hcc, hcs, hwc]
    simp [smul_eq_mul, div_eq_mul_inv]
  · change Ls (a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)) = b / 2
    rw [map_add, map_add, map_smul, map_smul, hsc, hss, hws]
    simp [smul_eq_mul, div_eq_mul_inv]

/-- Equal actual probability laws force equal displayed first-harmonic
amplitudes, regardless of which retained range corrections represent them. -/
theorem polynomialChart_law_amplitudes_injective (h a b a' b' : ℝ)
    (w w' : E_STR02969)
    (hμ : (densityMeasure (polynomialChartAbsolute h
      (a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969))) : Measure (Torus 1)) =
      densityMeasure (polynomialChartAbsolute h
        (a' • cosC2_STR02915 + b' • sinC2_STR02915 + (w' : PeriodicC2_STR02969)))) :
    a = a' ∧ b = b' := by
  have hu := polynomialChart_amplitude_coordinates a b w
  have hv := polynomialChart_amplitude_coordinates a' b' w'
  have he := polynomialChartAbsolute_injective_meanZero h _ _ hu.1 hv.1 hμ
  have hc := congrArg (fun u : PeriodicC2_STR02969 => pair_STR02953 Real.cos u.val) he
  have hs := congrArg (fun u : PeriodicC2_STR02969 => pair_STR02953 Real.sin u.val) he
  rw [hu.2.1, hv.2.1] at hc
  rw [hu.2.2, hv.2.2] at hs
  constructor <;> linarith

end DGPS.Examples.PolynomialSpecies
