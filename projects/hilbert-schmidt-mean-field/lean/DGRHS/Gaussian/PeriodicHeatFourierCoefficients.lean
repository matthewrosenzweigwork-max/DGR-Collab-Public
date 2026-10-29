import DGRHS.Gaussian.PeriodicHeatSourceLimit

/-! Actual positive trace-class Fourier coefficients of the regularized
Green kernel, including absolute summability of their square roots. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatCoefficient (τ : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  Real.exp (-τ*‖periodicFrequencyVector k‖^2)*(periodicLogFourierCoeff k).re

lemma periodicLogCoefficient_nonneg (k : PeriodicFrequency ι) : 0≤(periodicLogFourierCoeff k).re := by
  unfold periodicLogFourierCoeff
  split_ifs
  · simp
  · simp only [Complex.ofReal_re]
    have hc := periodicLogConstant_pos (ι := ι)
    positivity

lemma periodicLogCoefficient_bound (k : PeriodicFrequency ι) :
    (periodicLogFourierCoeff k).re≤(periodicStabilityThreshold ι)⁻¹ := by
  have hc := periodicStabilityThreshold_pos (ι := ι)
  by_cases hk : k=0
  · subst k
    simp only [periodicLogFourierCoeff_zero,Complex.zero_re]
    positivity
  · have hr := periodicFrequency_norm_pos hk
    have hnorm : 1≤‖periodicFrequencyVector k‖ := by
      nlinarith [periodicFrequency_norm_sq_ge_one hk]
    have hi : ‖periodicFrequencyVector k‖⁻¹≤1 := by
      have h := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hr.le)
      simpa only [mul_one,inv_mul_cancel₀ hr.ne'] using h
    have hp : ‖periodicFrequencyVector k‖⁻¹^(Fintype.card ι)≤1 := pow_le_one₀ (inv_nonneg.mpr hr.le) hi
    simp only [periodicLogFourierCoeff,if_neg hk,Complex.ofReal_re,periodicStabilityThreshold,inv_div]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
      (div_nonneg periodicLogConstant_pos.le (by positivity))

lemma periodicHeatCoefficient_nonneg (τ : ℝ) (k : PeriodicFrequency ι) :
    0≤periodicHeatCoefficient τ k :=
  mul_nonneg (Real.exp_pos _).le (periodicLogCoefficient_nonneg k)

lemma periodicHeatCoefficient_bound (τ : ℝ) (k : PeriodicFrequency ι) :
    periodicHeatCoefficient τ k≤(periodicStabilityThreshold ι)⁻¹*Real.exp (-τ*‖periodicFrequencyVector k‖^2) := by
  simpa only [periodicHeatCoefficient,mul_comm] using
    mul_le_mul_of_nonneg_left (periodicLogCoefficient_bound k) (Real.exp_pos (-τ*‖periodicFrequencyVector k‖^2)).le

lemma periodicHeatCoefficient_summable (τ : ℝ) (hτ : 0<τ) :
    Summable (periodicHeatCoefficient (ι := ι) τ) :=
  ((summable_periodicGaussian τ hτ).mul_left _).of_nonneg_of_le
    (periodicHeatCoefficient_nonneg τ) (periodicHeatCoefficient_bound τ)

lemma periodicHeatCoefficient_sqrt_bound (τ : ℝ) (k : PeriodicFrequency ι) :
    Real.sqrt (periodicHeatCoefficient τ k)≤Real.sqrt ((periodicStabilityThreshold ι)⁻¹)*
      Real.exp (-(τ/2)*‖periodicFrequencyVector k‖^2) := by
  have hlambda : 0≤(periodicStabilityThreshold ι)⁻¹ := inv_nonneg.mpr periodicStabilityThreshold_pos.le
  have he : (Real.exp (-(τ/2)*‖periodicFrequencyVector k‖^2))^2=
      Real.exp (-τ*‖periodicFrequencyVector k‖^2) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)).mp
  rw [Real.sq_sqrt (periodicHeatCoefficient_nonneg τ k),mul_pow,Real.sq_sqrt hlambda,he]
  exact periodicHeatCoefficient_bound τ k

lemma periodicHeatCoefficient_sqrt_summable (τ : ℝ) (hτ : 0<τ) :
    Summable (fun k : PeriodicFrequency ι => Real.sqrt (periodicHeatCoefficient τ k)) :=
  ((summable_periodicGaussian (τ/2) (by positivity)).mul_left _).of_nonneg_of_le
    (fun _ => Real.sqrt_nonneg _) (periodicHeatCoefficient_sqrt_bound τ)

lemma periodicHeatCoefficient_coe (τ : ℝ) (k : PeriodicFrequency ι) :
    (periodicHeatCoefficient τ k:ℂ)=
      (Real.exp (-τ*‖periodicFrequencyVector k‖^2):ℂ)*periodicLogFourierCoeff k := by
  simp only [periodicHeatCoefficient,Complex.ofReal_mul]
  congr 1
  unfold periodicLogFourierCoeff
  split_ifs <;> simp only [Complex.zero_re,Complex.ofReal_zero,Complex.ofReal_re]

lemma periodicHeatCoefficient_neg (τ : ℝ) (k : PeriodicFrequency ι) :
    periodicHeatCoefficient τ (-k)=periodicHeatCoefficient τ k := by
  simp only [periodicHeatCoefficient,periodicLogFourierCoeff_neg,periodicFrequencyVector_neg,norm_neg]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatCoefficient_summable
#print axioms DGRHS.Periodic.periodicHeatCoefficient_sqrt_summable
#print axioms DGRHS.Periodic.periodicHeatCoefficient_coe
