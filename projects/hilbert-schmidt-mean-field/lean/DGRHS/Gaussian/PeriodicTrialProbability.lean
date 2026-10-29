import DGRHS.Gaussian.PeriodicCosineConvolution
import Mathlib.MeasureTheory.Measure.WithDensityFinite

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicCosineTrialMeasure (i : ι) (ε : ℝ) : Measure (PeriodicTorus ι) :=
  (periodicHaar ι).withDensity (fun x => ENNReal.ofReal (periodicCosineTrialDensity i ε x))
lemma periodicCosineTrialDensity_measurable (i : ι) (ε : ℝ) :
    Measurable (periodicCosineTrialDensity i ε) := by
  have h : Continuous (periodicCosineTrialDensity i ε) :=
    continuous_const.add (continuous_const.mul (periodicCoordinateCos_continuous i))
  exact h.measurable
lemma periodicCosineTrialMeasure_probability (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    IsProbabilityMeasure (periodicCosineTrialMeasure i ε) := by
  constructor
  unfold periodicCosineTrialMeasure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hf := periodicCosineTrial_positiveBounded i ε hε
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrable
    (hf.bounds.mono fun x hx => by change 0 ≤ periodicCosineTrialDensity i ε x; linarith [hx.1]),periodicCosineTrialDensity_integral]
  norm_num
lemma periodicCosineTrialMeasure_integral (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2)
    (f : PeriodicTorus ι → ℝ) :
    (∫ x,f x ∂periodicCosineTrialMeasure i ε) =
      ∫ x,periodicCosineTrialDensity i ε x*f x ∂periodicHaar ι := by
  unfold periodicCosineTrialMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (periodicCosineTrialDensity_measurable i ε).ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have h := periodicCosineTrialDensity_bounds i ε hε x
    change (ENNReal.ofReal (periodicCosineTrialDensity i ε x)).toReal * f x = _
    rw [ENNReal.toReal_ofReal (by linarith [h.1])]

lemma periodicCosineTrialMeasure_pair_integrable (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2))
      ((periodicCosineTrialMeasure i ε).prod (periodicCosineTrialMeasure i ε)) := by
  rw [periodicCosineTrialMeasure,prod_withDensity
    (periodicCosineTrialDensity_measurable i ε).ennreal_ofReal
    (periodicCosineTrialDensity_measurable i ε).ennreal_ofReal]
  apply (integrable_withDensity_iff_integrable_smul'
    (((periodicCosineTrialDensity_measurable i ε).ennreal_ofReal.comp measurable_fst).mul
      ((periodicCosineTrialDensity_measurable i ε).ennreal_ofReal.comp measurable_snd))
    (Filter.Eventually.of_forall fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).mpr
  convert periodicLog_trial_pair_integrable i ε hε using 1
  ext p
  have hx := periodicCosineTrialDensity_bounds i ε hε p.1
  have hy := periodicCosineTrialDensity_bounds i ε hε p.2
  change (ENNReal.ofReal (periodicCosineTrialDensity i ε p.1) *
    ENNReal.ofReal (periodicCosineTrialDensity i ε p.2)).toReal * periodicLogKernel (p.1-p.2) = _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by linarith [hx.1]),
    ENNReal.toReal_ofReal (by linarith [hy.1])]

lemma periodicCosineTrialMeasure_pair_integral (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    (∫ p : PeriodicTorus ι × PeriodicTorus ι,periodicLogKernel (p.1-p.2)
      ∂((periodicCosineTrialMeasure i ε).prod (periodicCosineTrialMeasure i ε))) =
      ε^2/(2*periodicStabilityThreshold ι) := by
  rw [periodicCosineTrialMeasure,prod_withDensity
    (periodicCosineTrialDensity_measurable i ε).ennreal_ofReal
    (periodicCosineTrialDensity_measurable i ε).ennreal_ofReal]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      ENNReal.ofReal (periodicCosineTrialDensity i ε p.1) *
      ENNReal.ofReal (periodicCosineTrialDensity i ε p.2)) from
      ((periodicCosineTrialDensity_measurable i ε).ennreal_ofReal.comp measurable_fst).mul
      ((periodicCosineTrialDensity_measurable i ε).ennreal_ofReal.comp measurable_snd))
    (Filter.Eventually.of_forall fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicCosineTrialDensity i ε p.1*periodicCosineTrialDensity i ε p.2*periodicLogKernel (p.1-p.2)
      ∂((periodicHaar ι).prod (periodicHaar ι)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        have hx := periodicCosineTrialDensity_bounds i ε hε p.1
        have hy := periodicCosineTrialDensity_bounds i ε hε p.2
        change (ENNReal.ofReal (periodicCosineTrialDensity i ε p.1) *
          ENNReal.ofReal (periodicCosineTrialDensity i ε p.2)).toReal * periodicLogKernel (p.1-p.2) = _
        rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by linarith [hx.1]),
          ENNReal.toReal_ofReal (by linarith [hy.1])]
    _ = _ := periodicLog_cosine_trial_pair_energy i ε hε

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCosineTrialMeasure_probability
#print axioms DGRHS.Periodic.periodicCosineTrialMeasure_pair_integral
#check @DGRHS.Periodic.periodicCosineTrialMeasure_probability

#print axioms DGRHS.Periodic.periodicCosineTrialMeasure_pair_integrable
