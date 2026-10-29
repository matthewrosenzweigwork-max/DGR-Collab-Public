import DGRHS.Gaussian.PeriodicShortHeatLatticeSum

/-! Actual proper short-scale heat Green integral and its physical local
logarithmic decomposition. Equality to the final original Fourier Green
representative is established separately after the full scale integration. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodic_short_lattice_integrable (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    IntegrableOn (fun t : ℝ => t⁻¹*∑' k : PeriodicFrequency ι,
      Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2))) (Ioc 0 1) := by
  let C := ∑' k : PeriodicFrequency ι,Real.exp (-‖periodicFrequencyVector k‖^2/16)
  have hb := (periodicLocalLogCore_integrable ‖x‖ (norm_pos_iff.mpr hx0)).add
    ((periodicLocalLogCore_integrable (Real.sqrt (1/8)) (by positivity)).mul_const C)
  apply hb.mono'
  · apply Measurable.aestronglyMeasurable
    exact measurable_inv.mul (Measurable.tsum (fun k => by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hpos : 0≤t⁻¹*∑' k : PeriodicFrequency ι,Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2)) :=
      mul_nonneg (inv_nonneg.mpr ht.1.le) (tsum_nonneg (fun k => (Real.exp_pos _).le))
    rw [Real.norm_eq_abs,abs_of_nonneg hpos]
    have h := mul_le_mul_of_nonneg_left (periodic_short_gaussian_spatial_bound x hx t ht.1 ht.2).2
      (inv_nonneg.mpr ht.1.le)
    have he : -(Real.sqrt (1/8))^2/(2*t^2)= -(1:ℝ)/(16*t^2) := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤1/8)]
      ring
    simpa only [Pi.add_apply,he,mul_add,mul_assoc,C] using h

lemma periodicShortHeatMean_integrable :
    IntegrableOn (fun t : ℝ => periodicHeatScaleFactor ι*t^(Fintype.card ι-1)) (Ioc 0 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
  exact (show Continuous (fun t : ℝ => periodicHeatScaleFactor ι*t^(Fintype.card ι-1)) by fun_prop).intervalIntegrable 0 1

def periodicShortHeatMean (ι : Type u) [Fintype ι] : ℝ :=
  ∫ t : ℝ in Ioc 0 1,periodicHeatScaleFactor ι*t^(Fintype.card ι-1)

def periodicShortGreen (x : PeriodicTorus ι) : ℝ :=
  ∫ t : ℝ in Ioc 0 1,periodicHeatScaleFactor ι*t^(Fintype.card ι-1)*
    ((periodicGaussianHeat (2*Real.pi^2*t^2) x).re-1)

lemma periodic_short_heat_integrable (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    IntegrableOn (fun t : ℝ => periodicHeatScaleFactor ι*t^(Fintype.card ι-1)*
      (periodicGaussianHeat (2*Real.pi^2*t^2) (fun i => (x i : UnitAddCircle))).re) (Ioc 0 1) := by
  apply (periodic_short_lattice_integrable x hx hx0).congr_fun _ measurableSet_Ioc
  intro t ht
  exact (periodicHeat_physical_scale_identity t ht.1 x).symm

lemma periodicShortGreen_integrable_at (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    IntegrableOn (fun t : ℝ => periodicHeatScaleFactor ι*t^(Fintype.card ι-1)*
      ((periodicGaussianHeat (2*Real.pi^2*t^2) (fun i => (x i : UnitAddCircle))).re-1)) (Ioc 0 1) := by
  simpa only [Pi.sub_def,mul_sub,mul_one] using
    (periodic_short_heat_integrable x hx hx0).sub (periodicShortHeatMean_integrable (ι := ι))

lemma periodicShortGreen_measurable : Measurable (periodicShortGreen (ι := ι)) := by
  have hm : Measurable (fun p : PeriodicTorus ι × ℝ =>
      periodicHeatScaleFactor ι*p.2^(Fintype.card ι-1)*
        ((periodicGaussianHeat (2*Real.pi^2*p.2^2) p.1).re-1)) := by
    exact (show Measurable (fun p : PeriodicTorus ι × ℝ =>
      periodicHeatScaleFactor ι*p.2^(Fintype.card ι-1)) by fun_prop).mul ((Complex.continuous_re.measurable.comp
      (periodicGaussianHeat_joint_measurable.comp
        (show Measurable (fun p : PeriodicTorus ι × ℝ => (2*Real.pi^2*p.2^2,p.1)) by fun_prop))).sub measurable_const)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Actual proper short-scale heat Green function on a centered chart. -/
theorem periodicShortGreen_physical (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    periodicShortGreen (fun i => (x i : UnitAddCircle)) =
      periodicLocalLogCore ‖x‖+periodicNonzeroImageRemainder x-periodicShortHeatMean ι := by
  unfold periodicShortGreen
  simp only [mul_sub,mul_one]
  rw [integral_sub (periodic_short_heat_integrable x hx hx0) (periodicShortHeatMean_integrable (ι := ι))]
  congr 1
  calc
    _ = ∫ t : ℝ in Ioc 0 1,t⁻¹*∑' k : PeriodicFrequency ι,
        Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact periodicHeat_physical_scale_identity t ht.1 x
    _ = _ := periodic_short_lattice_integral x hx hx0

theorem periodicShortGreen_log_bounds (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) (hx1 : ‖x‖≤1) :
    -Real.log ‖x‖+DGRHS.Gaussian.gaussianLogCounterterm 1-1/4-periodicShortHeatMean ι ≤
      periodicShortGreen (fun i => (x i : UnitAddCircle)) ∧
    periodicShortGreen (fun i => (x i : UnitAddCircle)) ≤
      -Real.log ‖x‖+DGRHS.Gaussian.gaussianLogCounterterm 1+
        periodicImageRemainderBound ι-periodicShortHeatMean ι := by
  rw [periodicShortGreen_physical x hx hx0]
  have hc := periodicLocalLogCore_log_bounds ‖x‖ (norm_pos_iff.mpr hx0) hx1
  have hr := periodicNonzeroImageRemainder_bounds x hx
  constructor <;> linarith [hc.1,hc.2,hr.1,hr.2]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_short_lattice_integrable
#print axioms DGRHS.Periodic.periodicShortGreen_integrable_at
#print axioms DGRHS.Periodic.periodicShortGreen_measurable
#print axioms DGRHS.Periodic.periodicShortGreen_physical
#print axioms DGRHS.Periodic.periodicShortGreen_log_bounds
#check @DGRHS.Periodic.periodicShortGreen_log_bounds
