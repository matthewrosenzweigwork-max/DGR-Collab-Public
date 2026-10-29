import DGRHS.Gaussian.PeriodicTrialEntropy
import DGRHS.Gaussian.PeriodicLogKernelSections

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate Classical
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local instance periodicConvolutionCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

lemma periodic_mFourier_argument_add (k : PeriodicFrequency ι) (x y : PeriodicTorus ι) :
    UnitAddTorus.mFourier k (x+y) = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    zsmul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]
lemma periodic_mFourier_norm_apply (k : PeriodicFrequency ι) (x : PeriodicTorus ι) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,fourier_apply,norm_prod,
    Circle.norm_coe,Finset.prod_const_one]
lemma periodic_mFourier_first (i : ι) (x : PeriodicTorus ι) :
    UnitAddTorus.mFourier (periodicFirstFrequency i) x = fourier 1 (x i) :=
  UnitAddTorus.mFourier_single x i
lemma periodic_mFourier_first_re (i : ι) (x : PeriodicTorus ι) :
    (UnitAddTorus.mFourier (periodicFirstFrequency i) x).re = periodicCoordinateCos i x := by
  rw [periodic_mFourier_first]
  rfl
lemma periodic_mFourier_argument_sub (k : PeriodicFrequency ι) (x y : PeriodicTorus ι) :
    UnitAddTorus.mFourier k (x-y) = UnitAddTorus.mFourier k x * conj (UnitAddTorus.mFourier k y) := by
  rw [sub_eq_add_neg,periodic_mFourier_argument_add,periodic_mFourier_reflection,
    UnitAddTorus.mFourier_neg]

lemma periodicCoordinateCos_memLp (i : ι) : MemLp (periodicCoordinateCos i) 2 (periodicHaar ι) :=
  (memLp_const (1:ℝ)).of_le (periodicCoordinateCos_continuous i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_one] using periodicCoordinateCos_abs_le_one i x)
lemma periodicCosineTrialDensity_memLp (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    MemLp (periodicCosineTrialDensity i ε) 2 (periodicHaar ι) := by
  have hf := periodicCosineTrial_positiveBounded i ε hε
  apply (memLp_const (3/2:ℝ)).of_le hf.measurable
  filter_upwards [hf.bounds] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ periodicCosineTrialDensity i ε x),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)] using hx.2
lemma periodicLog_complex_memLp :
    MemLp (fun x : PeriodicTorus ι => (periodicLogKernel x : ℂ)) 2 (periodicHaar ι) := by
  apply periodicLogKernel_memLp.mono
    (Complex.continuous_ofReal.comp_aestronglyMeasurable periodicLogKernel_memLp.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by simp
lemma periodic_mFourier_conj_memLp (k : PeriodicFrequency ι) :
    MemLp (fun x => conj (UnitAddTorus.mFourier k x)) 2 (periodicHaar ι) := by
  apply (memLp_const (1:ℂ)).of_le
    (Complex.continuous_conj.comp (UnitAddTorus.mFourier k).continuous).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by simp [periodic_mFourier_norm_apply]

lemma periodicLog_first_coefficient_integral (i : ι) :
    (∫ z,conj (UnitAddTorus.mFourier (periodicFirstFrequency i) z)*(periodicLogKernel z : ℂ) ∂periodicHaar ι) =
      ((periodicStabilityThreshold ι)⁻¹ : ℝ) := by
  have h := periodicLogKernel_fourierCoeff (periodicFirstFrequency i)
  rw [periodic_mFourierCoeff_eq_integral,periodicLogFourierCoeff_first] at h
  have he (z : PeriodicTorus ι) : UnitAddTorus.mFourier (-periodicFirstFrequency i) z = conj (UnitAddTorus.mFourier (periodicFirstFrequency i) z) := UnitAddTorus.mFourier_neg
  simp_rw [he] at h
  exact h

lemma periodicLog_cosine_convolution_shift (i : ι) (x : PeriodicTorus ι) :
    (∫ z,periodicLogKernel z * periodicCoordinateCos i (x-z) ∂periodicHaar ι) =
      (periodicStabilityThreshold ι)⁻¹ * periodicCoordinateCos i x := by
  have hi := (periodic_mFourier_conj_memLp (periodicFirstFrequency i)).integrable_mul
    (periodicLog_complex_memLp (ι := ι))
  have hi' : Integrable (fun z => UnitAddTorus.mFourier (periodicFirstFrequency i) x *
      (conj (UnitAddTorus.mFourier (periodicFirstFrequency i) z)*(periodicLogKernel z : ℂ))) (periodicHaar ι) :=
    hi.const_mul _
  calc
    (∫ z,periodicLogKernel z * periodicCoordinateCos i (x-z) ∂periodicHaar ι) =
        ∫ z,(UnitAddTorus.mFourier (periodicFirstFrequency i) x *
          (conj (UnitAddTorus.mFourier (periodicFirstFrequency i) z)*(periodicLogKernel z : ℂ))).re ∂periodicHaar ι := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change periodicLogKernel z * periodicCoordinateCos i (x-z) =
          (UnitAddTorus.mFourier (periodicFirstFrequency i) x * (conj (UnitAddTorus.mFourier (periodicFirstFrequency i) z)*(periodicLogKernel z : ℂ))).re
        rw [← periodic_mFourier_first_re,periodic_mFourier_argument_sub]
        simp only [← mul_assoc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        ring
    _ = (∫ z,UnitAddTorus.mFourier (periodicFirstFrequency i) x *
          (conj (UnitAddTorus.mFourier (periodicFirstFrequency i) z)*(periodicLogKernel z : ℂ)) ∂periodicHaar ι).re := by
      exact integral_re hi'
    _ = (UnitAddTorus.mFourier (periodicFirstFrequency i) x *
        (((periodicStabilityThreshold ι)⁻¹ : ℝ) : ℂ)).re := by
      rw [integral_const_mul,periodicLog_first_coefficient_integral]
    _ = (periodicStabilityThreshold ι)⁻¹*periodicCoordinateCos i x := by
      rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,periodic_mFourier_first_re]
      ring
lemma periodicLog_cosine_convolution (i : ι) (x : PeriodicTorus ι) :
    (∫ y,periodicLogKernel (x-y)*periodicCoordinateCos i y ∂periodicHaar ι) =
      (periodicStabilityThreshold ι)⁻¹*periodicCoordinateCos i x := by
  have hp := periodicHaar_preserving_sub_left x
  have hs : Integrable (fun z => periodicLogKernel z*periodicCoordinateCos i (x-z)) (periodicHaar ι) := by
    simpa only [Pi.mul_def,Function.comp_def] using periodicLogKernel_memLp.integrable_mul
      ((periodicCoordinateCos_memLp i).comp_measurePreserving hp)
  have hm : AEStronglyMeasurable (fun z => periodicLogKernel z*periodicCoordinateCos i (x-z))
      (Measure.map (fun y : PeriodicTorus ι => x-y) (periodicHaar ι)) := by
    rw [hp.map_eq]
    exact hs.aestronglyMeasurable
  have ht := integral_map hp.aemeasurable hm
  rw [hp.map_eq,periodicLog_cosine_convolution_shift] at ht
  simpa only [sub_sub_cancel] using ht.symm

lemma periodicLog_trial_row (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) (x : PeriodicTorus ι) :
    (∫ y,periodicCosineTrialDensity i ε y * periodicLogKernel (x-y) ∂periodicHaar ι) =
      ε*(periodicStabilityThreshold ι)⁻¹*periodicCoordinateCos i x := by
  have hg := periodicLog_row_integrable x
  have hc : Integrable (fun y => periodicLogKernel (x-y)*periodicCoordinateCos i y) (periodicHaar ι) := by
    simpa only [Pi.mul_def,Function.comp_def] using
      (periodicLogKernel_memLp.comp_measurePreserving (periodicHaar_preserving_sub_left x)).integrable_mul
        (periodicCoordinateCos_memLp i)
  calc
    _ = ∫ y,periodicLogKernel (x-y)+ε*(periodicLogKernel (x-y)*periodicCoordinateCos i y) ∂periodicHaar ι := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by unfold periodicCosineTrialDensity; ring
    _ = ε*(periodicStabilityThreshold ι)⁻¹*periodicCoordinateCos i x := by
      rw [integral_add hg (hc.const_mul ε),integral_const_mul,periodicLog_row_mean_zero,
        periodicLog_cosine_convolution]
      ring

lemma periodicLog_trial_pair_integrable (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicCosineTrialDensity i ε p.1*periodicCosineTrialDensity i ε p.2*periodicLogKernel (p.1-p.2))
      ((periodicHaar ι).prod (periodicHaar ι)) := by
  have hm : Continuous (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicCosineTrialDensity i ε p.1*periodicCosineTrialDensity i ε p.2) := by
    unfold periodicCosineTrialDensity periodicCoordinateCos
    fun_prop
  have hw : MemLp (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicCosineTrialDensity i ε p.1*periodicCosineTrialDensity i ε p.2) 2
      ((periodicHaar ι).prod (periodicHaar ι)) := by
    apply (memLp_const ((3/2)^2:ℝ)).of_le hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      have hx := periodicCosineTrialDensity_bounds i ε hε p.1
      have hy := periodicCosineTrialDensity_bounds i ε hε p.2
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith [hx.1]) (by linarith [hy.1])),Real.norm_eq_abs,abs_of_nonneg (by norm_num)]
      nlinarith
  simpa only [Pi.mul_def,Function.comp_def] using hw.integrable_mul (periodicLogPair_memLp (ι := ι))

/-- Exact energy of the ACTUAL original-kernel cosine product trial. -/
lemma periodicLog_cosine_trial_pair_energy (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    (∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicCosineTrialDensity i ε p.1*periodicCosineTrialDensity i ε p.2*periodicLogKernel (p.1-p.2)
        ∂((periodicHaar ι).prod (periodicHaar ι))) = ε^2/(2*periodicStabilityThreshold ι) := by
  rw [integral_prod _ (periodicLog_trial_pair_integrable i ε hε)]
  simp_rw [mul_assoc,integral_const_mul,periodicLog_trial_row i ε hε]
  have hlin := periodicCoordinateCos_integrable i
  have hquad : Integrable (fun x => periodicCoordinateCos i x^2) (periodicHaar ι) := by
    simpa only [Pi.mul_def,Function.comp_def,pow_two] using (periodicCoordinateCos_memLp i).integrable_mul (periodicCoordinateCos_memLp i)
  calc
    _ = (ε*(periodicStabilityThreshold ι)⁻¹) * ∫ x,
        periodicCoordinateCos i x+ε*periodicCoordinateCos i x^2 ∂periodicHaar ι := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by unfold periodicCosineTrialDensity; ring
    _ = ε^2/(2*periodicStabilityThreshold ι) := by
      rw [integral_add hlin (hquad.const_mul ε),integral_const_mul,
        periodicCoordinateCos_mean_zero,periodicCoordinateCos_second_moment]
      ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLog_cosine_trial_pair_energy
#check @DGRHS.Periodic.periodicLog_cosine_trial_pair_energy
