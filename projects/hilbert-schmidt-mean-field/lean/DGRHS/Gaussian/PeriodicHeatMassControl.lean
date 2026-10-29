import DGRHS.Gaussian.PeriodicHeatPhysicalIdentity

/-! Genuine probability-kernel mass and uniform L1 control for the actual
Gaussian torus heat series. This justifies the small-scale product-integral
bounds used in the physical Green construction. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicGaussianHeat_integrable (a : ℝ) (ha : 0<a) :
    Integrable (periodicGaussianHeat (ι := ι) a) (periodicHaar ι) :=
  (periodicGaussianHeat_continuous a ha).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma periodicGaussianHeat_eq_re (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    periodicGaussianHeat a x = ((periodicGaussianHeat a x).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (periodicGaussianHeat_real_nonneg a ha x).2

lemma periodicGaussianHeat_norm_eq_re (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat a x‖ = (periodicGaussianHeat a x).re := by
  conv_lhs => rw [periodicGaussianHeat_eq_re a ha x]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (periodicGaussianHeat_real_nonneg a ha x).1]

lemma periodicGaussianHeat_real_integral (a : ℝ) (ha : 0<a) :
    (∫ x,(periodicGaussianHeat (ι := ι) a x).re ∂periodicHaar ι) = 1 := by
  calc
    _ = (∫ x,periodicGaussianHeat (ι := ι) a x ∂periodicHaar ι).re :=
      integral_re (periodicGaussianHeat_integrable (ι := ι) a ha)
    _ = 1 := by rw [periodicGaussianHeat_integral a ha]; rfl

lemma periodicGaussianHeat_norm_integral (a : ℝ) (ha : 0<a) :
    (∫ x,‖periodicGaussianHeat (ι := ι) a x‖ ∂periodicHaar ι) = 1 := by
  simp only [periodicGaussianHeat_norm_eq_re a ha,periodicGaussianHeat_real_integral a ha]

lemma periodicGaussianHeat_centered_mass_bound (a : ℝ) (ha : 0<a) :
    (∫ x,‖periodicGaussianHeat (ι := ι) a x-1‖ ∂periodicHaar ι) ≤ 2 := by
  have hi := periodicGaussianHeat_integrable (ι := ι) a ha
  calc
    _ ≤ ∫ x,‖periodicGaussianHeat (ι := ι) a x‖+1 ∂periodicHaar ι :=
      integral_mono_ae (hi.sub (integrable_const _)).norm (hi.norm.add (integrable_const _))
        (Eventually.of_forall (fun x => by simpa using norm_sub_le (periodicGaussianHeat a x) (1:ℂ)))
    _ = 2 := by rw [integral_add hi.norm (integrable_const _),periodicGaussianHeat_norm_integral a ha]; simp; norm_num

lemma periodicGaussianHeat_joint_measurable :
    Measurable (fun p : ℝ × PeriodicTorus ι => periodicGaussianHeat p.1 p.2) := by
  apply Measurable.tsum
  intro k
  exact (Complex.continuous_ofReal.measurable.comp (by fun_prop)).mul
    ((UnitAddTorus.mFourier k).continuous.measurable.comp measurable_snd)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicGaussianHeat_integrable
#print axioms DGRHS.Periodic.periodicGaussianHeat_norm_integral
#print axioms DGRHS.Periodic.periodicGaussianHeat_centered_mass_bound
#print axioms DGRHS.Periodic.periodicGaussianHeat_joint_measurable
#check @DGRHS.Periodic.periodicGaussianHeat_centered_mass_bound
