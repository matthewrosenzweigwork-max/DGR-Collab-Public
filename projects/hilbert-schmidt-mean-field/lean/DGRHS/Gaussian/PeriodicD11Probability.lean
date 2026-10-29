import DGRHS.Gaussian.PeriodicD11GreenEnergy
import DGRHS.Gaussian.PeriodicTrialProductLaw

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian.D11Imported.HighDim
open DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma periodicD11_pair_integrable :
    Integrable (fun p : Torus 11 × Torus 11 =>
      periodizedProfile p.1*periodizedProfile p.2*periodicLogKernel (p.1-p.2))
      ((periodicHaar (Fin 11)).prod (periodicHaar (Fin 11))) := by
  obtain ⟨B,hB⟩ := periodizedProfile_bounded
  have hm : Measurable (fun p : Torus 11 × Torus 11 => periodizedProfile p.1*periodizedProfile p.2) :=
    (periodizedProfile_measurable.comp measurable_fst).mul (periodizedProfile_measurable.comp measurable_snd)
  have hw : MemLp (fun p : Torus 11 × Torus 11 => periodizedProfile p.1*periodizedProfile p.2) 2
      ((periodicHaar (Fin 11)).prod (periodicHaar (Fin 11))) := by
    apply (memLp_const (B^2:ℝ)).of_le hm.aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [norm_mul,show ‖B^2‖=B*B by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg B),pow_two]]
      exact mul_le_mul (hB p.1) (hB p.2) (norm_nonneg _) ((norm_nonneg _).trans (hB p.1))
  exact hw.integrable_mul periodicLogPair_memLp

lemma periodicD11_pair_integral :
    (∫ p : Torus 11 × Torus 11,periodizedProfile p.1*periodizedProfile p.2*periodicLogKernel (p.1-p.2)
      ∂((periodicHaar (Fin 11)).prod (periodicHaar (Fin 11))))=periodicD11GreenEnergy := by
  rw [integral_prod _ periodicD11_pair_integrable]
  simp_rw [mul_assoc,integral_const_mul]
  rfl

def periodicD11Measure : Measure (Torus 11) :=
  (periodicHaar (Fin 11)).withDensity (fun x => ENNReal.ofReal (periodizedProfile x))

instance periodicD11Measure_probability : IsProbabilityMeasure periodicD11Measure := by
  constructor
  unfold periodicD11Measure
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact periodizedProfile_lintegral

lemma periodicD11Measure_integral (f : Torus 11 → ℝ) :
    (∫ x,f x ∂periodicD11Measure)=∫ x,periodizedProfile x*f x ∂periodicHaar (Fin 11) := by
  unfold periodicD11Measure
  rw [integral_withDensity_eq_integral_toReal_smul periodizedProfile_measurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (ENNReal.ofReal (periodizedProfile x)).toReal*f x=_
    rw [ENNReal.toReal_ofReal (periodizedProfile_pos x).le]

lemma periodicD11Measure_pair_integrable :
    Integrable (fun p : Torus 11 × Torus 11 => periodicLogKernel (p.1-p.2))
      (periodicD11Measure.prod periodicD11Measure) := by
  rw [periodicD11Measure,prod_withDensity periodizedProfile_measurable.ennreal_ofReal
    periodizedProfile_measurable.ennreal_ofReal]
  apply (integrable_withDensity_iff_integrable_smul'
    ((periodizedProfile_measurable.ennreal_ofReal.comp measurable_fst).mul
      (periodizedProfile_measurable.ennreal_ofReal.comp measurable_snd))
    (Eventually.of_forall fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).mpr
  convert periodicD11_pair_integrable using 1
  ext p
  change (ENNReal.ofReal (periodizedProfile p.1)*ENNReal.ofReal (periodizedProfile p.2)).toReal*
    periodicLogKernel (p.1-p.2)=_
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (periodizedProfile_pos p.1).le,
    ENNReal.toReal_ofReal (periodizedProfile_pos p.2).le]

lemma periodicD11Measure_pair_integral :
    (∫ p : Torus 11 × Torus 11,periodicLogKernel (p.1-p.2)
      ∂periodicD11Measure.prod periodicD11Measure)=periodicD11GreenEnergy := by
  rw [periodicD11Measure,prod_withDensity periodizedProfile_measurable.ennreal_ofReal
    periodizedProfile_measurable.ennreal_ofReal]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun p : Torus 11 × Torus 11 =>
      ENNReal.ofReal (periodizedProfile p.1)*ENNReal.ofReal (periodizedProfile p.2)) from
      (periodizedProfile_measurable.ennreal_ofReal.comp measurable_fst).mul
        (periodizedProfile_measurable.ennreal_ofReal.comp measurable_snd))
    (Eventually.of_forall fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  convert periodicD11_pair_integral using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    change (ENNReal.ofReal (periodizedProfile p.1)*ENNReal.ofReal (periodizedProfile p.2)).toReal*
      periodicLogKernel (p.1-p.2)=_
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (periodizedProfile_pos p.1).le,
      ENNReal.toReal_ofReal (periodizedProfile_pos p.2).le]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicD11Measure_pair_integral
#print axioms DGRHS.Periodic.periodicD11Measure_pair_integrable
