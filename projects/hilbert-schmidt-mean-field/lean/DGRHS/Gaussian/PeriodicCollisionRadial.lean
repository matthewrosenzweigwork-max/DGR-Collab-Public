import DGRHS.Gaussian.PeriodicGreenExponentialIntegrability

/-! Sharp radial nonintegrability, including the dimension-equal exponent.
This uses native Haar polar integration and the exact one-dimensional power
integrability criterion. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic

lemma norm_rpow_not_integrableOn_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1≤Module.finrank ℝ E) (α r : ℝ) (hα : (Module.finrank ℝ E:ℝ)≤α) (hr : 0<r) :
    ¬ IntegrableOn (fun x : E => ‖x‖^(-α)) (ball 0 r) μ := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  intro hi
  have hp := (integrableOn_fun_norm_addHaar μ (f := fun y : ℝ => y^(-α)) (r := r)).mp hi
  have he : IntegrableOn (fun y : ℝ => y^((Module.finrank ℝ E:ℝ)-1-α)) (Ioo 0 r) := by
    apply hp.congr_fun _ measurableSet_Ioo
    intro y hy
    simp only [smul_eq_mul]
    rw [← Real.rpow_natCast y (Module.finrank ℝ E-1),← Real.rpow_add hy.1]
    congr 1
    rw [Nat.cast_sub hd,Nat.cast_one]
    ring
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mp he
  linarith

lemma lintegral_norm_rpow_ball_eq_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1≤Module.finrank ℝ E) (α r : ℝ) (hα : (Module.finrank ℝ E:ℝ)≤α) (hr : 0<r) :
    (∫⁻ x : E in ball 0 r,ENNReal.ofReal (‖x‖^(-α)) ∂μ)=∞ := by
  by_contra hn
  have hi : IntegrableOn (fun x : E => ‖x‖^(-α)) (ball 0 r) μ := by
    refine ⟨(measurable_norm.pow_const _).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (fun x => Real.rpow_nonneg (norm_nonneg x) _))).mpr (lt_top_iff_ne_top.mpr hn)
  exact norm_rpow_not_integrableOn_ball μ hd α r hα hr hi

end DGRHS.Periodic
#print axioms DGRHS.Periodic.norm_rpow_not_integrableOn_ball
#print axioms DGRHS.Periodic.lintegral_norm_rpow_ball_eq_top
#check @DGRHS.Periodic.lintegral_norm_rpow_ball_eq_top
