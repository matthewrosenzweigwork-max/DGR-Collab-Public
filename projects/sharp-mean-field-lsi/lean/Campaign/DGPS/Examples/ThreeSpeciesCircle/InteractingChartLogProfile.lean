import DGPS.Examples.ThreeSpeciesCircle.InteractingChartResidual

/-! AE chart laws identify the genuine continuous root's logarithmic profile
pointwise. No pointwise assertion is made about the original stored root. -/

noncomputable section
open MeasureTheory Filter
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem angular_point (t : ℝ) :
    angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  congr 1
  field_simp

/-- A genuine continuous AE representative has exactly the actual angular
chart log-profile, including its physical reference-normalization constant. -/
theorem interactingChart_continuous_logProfile (h : ℝ) (u : PeriodicC2_STR02969)
    (ρ : AbsoluteDensity 1) {v : Torus 1 → ℝ} (hv : Continuous v)
    (hvrep : ρ.sqrt =ᵐ[haar 1] v)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ)) :
    (fun t : ℝ => Real.log (v (pt (t / (2 * Real.pi))) ^ 2) -
      ellT h (pt (t / (2 * Real.pi)))) =
        fun t => u.val t + elementaryChartLogConstant h u := by
  have hp := periodic_rho_STR02950 h u.isC2.1
  have hc : Continuous (fun θ : AngCircle => rhoT_STR02901 h u.val (angSec θ)) := by
    change Continuous (AddCircle.liftIoc (2 * Real.pi) 0 (rhoT_STR02901 h u.val))
    exact AddCircle.liftIoc_zero_continuous (by simpa using (hp 0).symm)
      (continuous_rho_STR02950 h u.isC2.2.1.continuous).continuousOn
  have ha : Continuous (angEquiv : Torus 1 → AngCircle) := by
    change Continuous (fun x : Torus 1 => angHomeo (x 0))
    exact angHomeo.continuous.comp (continuous_apply 0)
  have hρH : ∀ᵐ x ∂haar 1,
      ρ.density x = rhoT_STR02901 h u.val (angSec (angEquiv x)) := by
    have ht := (ae_comp_angEquiv_iff (p := fun θ =>
      ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))).2 hρ
    simpa only [MeasurableEquiv.symm_apply_apply] using ht
  have heae : (fun x => v x ^ 2) =ᵐ[haar 1]
      fun x => rhoT_STR02901 h u.val (angSec (angEquiv x)) := by
    filter_upwards [hρH, hvrep] with x hx hvx
    rw [← hvx]
    exact hx
  have he := MeasureTheory.Measure.eq_of_ae_eq heae (hv.pow 2) (hc.comp ha)
  have hv2 (t : ℝ) : v (pt (t / (2 * Real.pi))) ^ 2 = rhoT_STR02901 h u.val t := by
    rw [← angular_point]
    have ht := congrFun he (angEquiv.symm (t : AngCircle))
    simp only [MeasurableEquiv.apply_symm_apply] at ht
    calc
      _ = rhoT_STR02901 h u.val (angSec (t : AngCircle)) := ht
      _ = hp.lift (t : AngCircle) := by
        rw [← hp.lift_coe (angSec (t : AngCircle)), coe_angSec_STR02962]
      _ = _ := hp.lift_coe t
  funext t
  rw [hv2]
  have hlog := (gate_str029_01_bind_common_optimizer_witness_absolute_variational_positive_log
    h u.isC2.2.1.continuous t).2
  rw [hlog, ellT_lift]
  have hangle : 2 * Real.pi * ((3 : ℕ) : ℝ) * (t / (2 * Real.pi)) = 3 * t := by
    field_simp
    <;> ring
  rw [hangle]
  unfold elementaryChartLogConstant
  rw [← besselI_zero_eq_meanT_STR02901]
  ring

end DGPS.Examples.ThreeSpeciesCircle
