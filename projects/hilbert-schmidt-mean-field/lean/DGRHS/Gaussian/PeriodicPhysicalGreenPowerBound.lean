import DGRHS.Gaussian.PeriodicPhysicalGreenIdentification

/-! Actual global lower and singular exponential upper bounds on a fundamental
cube. The comparison radius may be smaller than the Euclidean radius, enabling
the native finite-dimensional integrability theorem in the product chart. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLocalLogCore_antitone (r s : ℝ) (hr : 0<r) (hrs : r≤s) :
    periodicLocalLogCore s≤periodicLocalLogCore r := by
  have hs : 0<s := hr.trans_le hrs
  apply integral_mono_ae (periodicLocalLogCore_integrable s hs) (periodicLocalLogCore_integrable r hr)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0<t := ht.1
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

def periodicPhysicalGreenUpperConstant (ι : Type u) [Fintype ι] : ℝ :=
  DGRHS.Gaussian.gaussianLogCounterterm 1+periodicImageRemainderBound ι-
    periodicShortHeatMean ι+periodicLongGreenBound ι

lemma periodicPhysicalGreen_lower (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    -periodicShortHeatMean ι-periodicLongGreenBound ι≤
      periodicPhysicalGreen (fun i => (x i:UnitAddCircle)) := by
  have hs := periodicShortGreen_physical x hx hx0
  have hc := periodicLocalLogCore_nonneg ‖x‖
  have hr := (periodicNonzeroImageRemainder_bounds x hx).1
  have hl := (abs_le.mp (periodicPhysicalGreen_short_difference_bound (fun i => (x i:UnitAddCircle)))).1
  linarith

lemma periodicPhysicalGreen_upper_radius (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (r : ℝ) (hr : 0<r) (hrx : r≤‖x‖) (hr1 : r≤1) :
    periodicPhysicalGreen (fun i => (x i:UnitAddCircle)) ≤
      -Real.log r+periodicPhysicalGreenUpperConstant ι := by
  have hx0 : x≠0 := norm_pos_iff.mp (hr.trans_le hrx)
  have hs := periodicShortGreen_physical x hx hx0
  have hc := periodicLocalLogCore_antitone r ‖x‖ hr hrx
  have hrb := (periodicLocalLogCore_log_bounds r hr hr1).2
  have him := (periodicNonzeroImageRemainder_bounds x hx).2
  have hl := (abs_le.mp (periodicPhysicalGreen_short_difference_bound (fun i => (x i:UnitAddCircle)))).2
  unfold periodicPhysicalGreenUpperConstant
  linarith

lemma periodicPhysicalGreen_exp_power_bound (γ : ℝ) (hγ : 0≤γ)
    (x : EuclideanSpace ℝ ι) (hx : ∀ i,|x i|≤1/2)
    (r : ℝ) (hr : 0<r) (hrx : r≤‖x‖) (hr1 : r≤1) :
    Real.exp (γ*periodicPhysicalGreen (fun i => (x i:UnitAddCircle))) ≤
      Real.exp (γ*periodicPhysicalGreenUpperConstant ι)*r^(-γ) := by
  calc
    _ ≤ Real.exp (γ*(-Real.log r+periodicPhysicalGreenUpperConstant ι)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (periodicPhysicalGreen_upper_radius x hx r hr hrx hr1) hγ)
    _ = _ := by
      rw [Real.rpow_def_of_pos hr,← Real.exp_add]
      congr 1
      ring

lemma periodicPhysicalGreen_exp_cube_bound (γ : ℝ) (hγ : 0≤γ)
    (x : ι → ℝ) (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    Real.exp (γ*periodicPhysicalGreen (fun i => (x i:UnitAddCircle))) ≤
      Real.exp (γ*periodicPhysicalGreenUpperConstant ι)*‖x‖^(-γ) := by
  have hsup : ‖x‖≤1/2 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
    (fun i => by simpa only [Real.norm_eq_abs] using hx i)
  have hlp : ‖x‖≤‖WithLp.toLp 2 x‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun i => PiLp.norm_apply_le (WithLp.toLp 2 x) i)
  exact periodicPhysicalGreen_exp_power_bound γ hγ (WithLp.toLp 2 x) hx ‖x‖
    (norm_pos_iff.mpr hx0) hlp (by linarith)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicPhysicalGreen_lower
#print axioms DGRHS.Periodic.periodicPhysicalGreen_exp_power_bound
#print axioms DGRHS.Periodic.periodicPhysicalGreen_exp_cube_bound
#check @DGRHS.Periodic.periodicPhysicalGreen_exp_cube_bound
