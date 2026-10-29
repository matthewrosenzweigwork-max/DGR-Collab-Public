import DGRHS.Gaussian.PeriodicPhysicalGreenIdentification

/-! A global lower bound for the actual source Green kernel. The short heat
integral is handled separately when it is improper; its representative there
is irrelevant after the proved almost-everywhere physical identification. -/
noncomputable section
open MeasureTheory Set Filter
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicShortHeatMean_nonneg : 0 ≤ periodicShortHeatMean ι := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg periodicHeatScaleFactor_pos.le (pow_nonneg ht.1.le _)

lemma periodicShortGreen_global_lower (x : PeriodicTorus ι) :
    -periodicShortHeatMean ι ≤ periodicShortGreen x := by
  let f : ℝ → ℝ := fun t => periodicHeatScaleFactor ι*t^(Fintype.card ι-1)*
    ((periodicGaussianHeat (2*Real.pi^2*t^2) x).re-1)
  change -periodicShortHeatMean ι ≤ ∫ t in Ioc 0 1,f t
  by_cases hf : IntegrableOn f (Ioc 0 1)
  · have h := integral_mono_ae (periodicShortHeatMean_integrable (ι := ι)).neg hf ?_
    · simpa only [Pi.neg_apply,integral_neg,periodicShortHeatMean] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hw : 0 ≤ periodicHeatScaleFactor ι*t^(Fintype.card ι-1) := by
        exact mul_nonneg periodicHeatScaleFactor_pos.le (pow_nonneg ht.1.le _)
      have ht0 := ht.1
      have hg := (periodicGaussianHeat_real_nonneg (2*Real.pi^2*t^2) (by positivity) x).1
      dsimp only [f,Pi.neg_apply]
      nlinarith [mul_nonneg hw hg]
  · rw [integral_undef hf]
    exact neg_nonpos.mpr periodicShortHeatMean_nonneg

def periodicGreenLowerConstant (ι : Type u) [Fintype ι] : ℝ :=
  |periodicShortHeatMean ι|+|periodicLongGreenBound ι|

lemma periodicGreenLowerConstant_nonneg : 0 ≤ periodicGreenLowerConstant ι := by
  unfold periodicGreenLowerConstant
  positivity

lemma periodicPhysicalGreen_global_lower (x : PeriodicTorus ι) :
    -periodicGreenLowerConstant ι ≤ periodicPhysicalGreen x := by
  have hs := periodicShortGreen_global_lower x
  have hl := (abs_le.mp (periodicPhysicalGreen_short_difference_bound x)).1
  unfold periodicGreenLowerConstant
  linarith [le_abs_self (periodicShortHeatMean ι),le_abs_self (periodicLongGreenBound ι)]

theorem periodicLogKernel_lower_ae :
    ∀ᵐ x ∂periodicHaar ι,-periodicGreenLowerConstant ι ≤ periodicLogKernel x := by
  filter_upwards [periodicPhysicalGreen_eq_kernel_ae (ι := ι)] with x hx
  rw [←hx]
  exact periodicPhysicalGreen_global_lower x

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogKernel_lower_ae
#check @DGRHS.Periodic.periodicLogKernel_lower_ae
