import DGRHS.Gaussian.PeriodicLogReality
import Mathlib.MeasureTheory.Group.Prod

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local instance periodicSectionsCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

instance periodicHaar_isAddHaarMeasure : Measure.IsAddHaarMeasure (periodicHaar ι) := by
  unfold periodicHaar
  infer_instance

lemma periodicLogFourierCoeff_eq_source (k : PeriodicFrequency ι) (hk : k ≠ 0) :
    periodicLogFourierCoeff k =
      ((periodicLogConstant ι / (2*Real.pi*‖periodicFrequencyVector k‖)^(Fintype.card ι) : ℝ) : ℂ) := by
  simp only [periodicLogFourierCoeff,ite_eq_right hk]
  congr 1
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

def periodicFirstFrequency (i : ι) : PeriodicFrequency ι := Pi.single i 1
lemma periodicFirstFrequency_ne_zero (i : ι) : periodicFirstFrequency i ≠ 0 := by
  intro h
  have h' := congrFun h i
  simpa [periodicFirstFrequency] using h'
lemma norm_periodicFirstFrequency (i : ι) : ‖periodicFrequencyVector (periodicFirstFrequency i)‖ = 1 := by
  have hsq : ‖periodicFrequencyVector (periodicFirstFrequency i)‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [periodicFirstFrequency,Pi.single_apply,periodicFrequencyVector]
  have hnonneg := norm_nonneg (periodicFrequencyVector (periodicFirstFrequency i))
  nlinarith
lemma periodicLogFourierCoeff_first (i : ι) :
    periodicLogFourierCoeff (periodicFirstFrequency i) = ((periodicStabilityThreshold ι)⁻¹ : ℝ) := by
  simp [periodicLogFourierCoeff,periodicFirstFrequency_ne_zero,norm_periodicFirstFrequency,
    periodicStabilityThreshold,inv_div]

lemma periodicHaar_preserving_difference :
    MeasurePreserving (fun p : PeriodicTorus ι × PeriodicTorus ι => p.1-p.2)
      ((periodicHaar ι).prod (periodicHaar ι)) (periodicHaar ι) :=
  (measurePreserving_fst (μ := periodicHaar ι) (ν := periodicHaar ι)).comp
    (measurePreserving_sub_prod (periodicHaar ι) (periodicHaar ι))
lemma periodicLogPair_memLp :
    MemLp (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2)) 2
      ((periodicHaar ι).prod (periodicHaar ι)) :=
  periodicLogKernel_memLp.comp_measurePreserving periodicHaar_preserving_difference
lemma periodicLogPair_integrable :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2))
      ((periodicHaar ι).prod (periodicHaar ι)) := periodicLogPair_memLp.integrable (by norm_num)

lemma periodicHaar_preserving_sub_left (x : PeriodicTorus ι) :
    MeasurePreserving (fun y : PeriodicTorus ι => x-y) (periodicHaar ι) (periodicHaar ι) :=
  (periodicHaar ι).measurePreserving_sub_left x
lemma periodicLog_row_integrable (x : PeriodicTorus ι) :
    Integrable (fun y => periodicLogKernel (x-y)) (periodicHaar ι) :=
  (periodicHaar_preserving_sub_left x).integrable_comp_of_integrable periodicLogKernel_integrable
lemma periodicLog_row_mean_zero (x : PeriodicTorus ι) :
    (∫ y,periodicLogKernel (x-y) ∂periodicHaar ι) = 0 := by
  have hp := periodicHaar_preserving_sub_left x
  have hm : AEStronglyMeasurable (periodicLogKernel (ι := ι))
      (Measure.map (fun y : PeriodicTorus ι => x-y) (periodicHaar ι)) := by
    rw [hp.map_eq]
    exact periodicLogKernel_integrable.aestronglyMeasurable
  rw [← integral_map hp.aemeasurable hm,hp.map_eq,periodicLogKernel_integral_zero]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogFourierCoeff_first
#print axioms DGRHS.Periodic.periodicLogPair_memLp
#print axioms DGRHS.Periodic.periodicLog_row_mean_zero
#check @DGRHS.Periodic.periodicLog_row_mean_zero
