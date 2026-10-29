import DGRHS.Gaussian.PeriodicD11Centered
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Native extended relative entropy of the literal wrapped-Cauchy law.
Properness is proved for this competitor; none is imposed on other laws. -/
noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian.D11Imported.HighDim
open DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma periodicD11Measure_absolutelyContinuous : periodicD11Measure ≪ periodicHaar (Fin 11) :=
  withDensity_absolutelyContinuous _ _

lemma periodicD11Measure_llr_ae :
    llr periodicD11Measure (periodicHaar (Fin 11)) =ᵐ[periodicD11Measure]
      (fun x => Real.log (periodizedProfile x)) := by
  have hRN := Measure.rnDeriv_withDensity (periodicHaar (Fin 11))
    periodizedProfile_measurable.ennreal_ofReal
  filter_upwards [periodicD11Measure_absolutelyContinuous.ae_le hRN] with x hx
  change Real.log (periodicD11Measure.rnDeriv (periodicHaar (Fin 11)) x).toReal=_
  unfold periodicD11Measure
  rw [hx,ENNReal.toReal_ofReal (periodizedProfile_pos x).le]

lemma periodicD11Measure_log_integrable :
    Integrable (fun x => Real.log (periodizedProfile x)) periodicD11Measure := by
  unfold periodicD11Measure
  apply (integrable_withDensity_iff_integrable_smul'
    periodizedProfile_measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  have he : (fun x => (ENNReal.ofReal (periodizedProfile x)).toReal • Real.log (periodizedProfile x))=
      (fun x => periodizedProfile x*Real.log (periodizedProfile x)) := by
    funext x
    rw [ENNReal.toReal_ofReal (periodizedProfile_pos x).le,smul_eq_mul]
  rw [he]
  exact competitorDensity_finiteEntropy

lemma periodicD11Measure_llr_integrable :
    Integrable (llr periodicD11Measure (periodicHaar (Fin 11))) periodicD11Measure :=
  periodicD11Measure_log_integrable.congr periodicD11Measure_llr_ae.symm

lemma periodicD11_entropy_nonneg : 0≤entropy competitorDensity := by
  obtain ⟨C,hC⟩ := periodizedProfile_positiveBounded
  have h := DGRHS.Concentration.entropy_nonneg hC
  simpa only [entropy,competitorDensity,DGRHS.Concentration.functionalEntropy,periodizedProfile_integral,
    Real.log_one,mul_zero,sub_zero] using h

theorem periodicD11Measure_klDiv :
    klDiv periodicD11Measure (periodicHaar (Fin 11))=ENNReal.ofReal (entropy competitorDensity) := by
  rw [klDiv_of_ac_of_integrable periodicD11Measure_absolutelyContinuous
    periodicD11Measure_llr_integrable,integral_congr_ae periodicD11Measure_llr_ae,
    periodicD11Measure_integral]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,add_sub_cancel_right]
  rfl

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicD11Measure_klDiv
#check @DGRHS.Periodic.periodicD11Measure_klDiv
