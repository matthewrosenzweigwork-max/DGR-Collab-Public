import DGRHS.Gaussian.D11Imported.ElevenCompetitorEnergy
import DGRHS.Gaussian.D11Imported.ElevenConditionalEntropy
import DGRHS.Gaussian.PeriodicBoundedFourierForm
import DGRHS.Gaussian.PeriodicDimensionThreshold

/-! Exact normalization of the actual bounded dimension-eleven competitor's
spectral energy and the original periodic Green quadratic form. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian.D11Imported.HighDim
open DGRHS.Gaussian.D11Imported.HighDim.Eleven
local instance d11CircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

lemma d11_frequencyLength_eq (k : Frequency 11) :
    frequencyLength k=‖periodicFrequencyVector k‖ := by
  unfold frequencyLength
  have h := EuclideanSpace.real_norm_sq_eq (periodicFrequencyVector k)
  simp only [periodicFrequencyVector_apply] at h
  rw [←h,Real.sqrt_sq (norm_nonneg _)]

lemma d11_fourierCoeff_eq (f : Torus 11 → ℝ) (k : Frequency 11) :
    fourierCoeff f k=UnitAddTorus.mFourierCoeff (fun x => (f x:ℂ)) k := by
  rw [periodic_mFourierCoeff_eq_integral]
  rfl

def periodicD11GreenEnergy : ℝ :=
  ∫ x,periodizedProfile x*(∫ y,periodizedProfile y*periodicLogKernel (x-y)
    ∂periodicHaar (Fin 11)) ∂periodicHaar (Fin 11)

lemma periodicD11GreenEnergy_nonneg : 0≤periodicD11GreenEnergy := by
  obtain ⟨B,hB⟩ := periodizedProfile_bounded
  exact periodicLog_bounded_form_nonneg periodizedProfile
    periodizedProfile_measurable.aestronglyMeasurable B hB

lemma periodicD11_spectral_hasSum :
    HasSum (spectralTerm competitorDensity)
      (periodicStabilityThreshold (Fin 11)*periodicD11GreenEnergy) := by
  let a : Frequency 11 → ℝ := fun k => if k=0 then 0 else
    periodicLogConstant (Fin 11)/(2*Real.pi)^11*‖periodicFrequencyVector k‖⁻¹^11
  obtain ⟨B,hB⟩ := periodizedProfile_bounded
  have hcoeff (k : Frequency 11) :
      UnitAddTorus.mFourierCoeff (fun x => (periodicLogKernel x:ℂ)) k=(a k:ℂ) := by
    rw [periodicLogKernel_fourierCoeff]
    simp only [periodicLogFourierCoeff,a,Fintype.card_fin]
    split_ifs <;> simp
  have hs := (periodic_bounded_fourier_form_hasSum periodicLogKernel periodizedProfile
    periodicLogKernel_integrable periodizedProfile_measurable.aestronglyMeasurable B hB a hcoeff).mul_left
      (periodicStabilityThreshold (Fin 11))
  have hsupport : Function.support (fun k : Frequency 11 => periodicStabilityThreshold (Fin 11)*
      (a k*((UnitAddTorus.mFourierCoeff (fun x => (periodizedProfile x:ℂ)) k).re^2+
        (UnitAddTorus.mFourierCoeff (fun x => (periodizedProfile x:ℂ)) k).im^2)))⊆{k | k≠0} := by
    intro k hk
    by_contra h
    have hk0 : k=0 := by simpa using h
    subst k
    simpa [a,Function.mem_support] using hk
  have hsub := (hasSum_subtype_iff_of_support_subset hsupport).mpr hs
  apply hsub.congr_fun
  intro k
  simp only [Function.comp_apply]
  change spectralTerm competitorDensity k = _
  rw [spectralTerm,d11_frequencyLength_eq,d11_fourierCoeff_eq]
  simp only [competitorDensity,a,if_neg k.property,Complex.sq_norm,Complex.normSq_apply]
  have hC := periodicLogConstant_pos (ι := Fin 11)
  simp only [periodicStabilityThreshold,Fintype.card_fin,inv_pow]
  field_simp [hC.ne',Real.pi_pos.ne']
  <;> ring

lemma periodicD11_spectralEnergy_eq : spectralEnergy competitorDensity=
    ENNReal.ofReal (periodicStabilityThreshold (Fin 11)*periodicD11GreenEnergy) := by
  unfold spectralEnergy
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun k => by
    unfold spectralTerm frequencyLength
    positivity) periodicD11_spectral_hasSum.summable,periodicD11_spectral_hasSum.tsum_eq]

lemma periodicD11_energy_lower : (2*(14475384292906/10^12):ℝ)<
    periodicStabilityThreshold (Fin 11)*periodicD11GreenEnergy := by
  have h := competitor_energy competitorDensity rfl
  rw [periodicD11_spectralEnergy_eq] at h
  by_contra hle
  exact (not_le_of_gt h) (ENNReal.ofReal_le_ofReal (le_of_not_gt hle))

lemma periodicD11_negative_free_energy :
    entropy competitorDensity-
      ((8653/8673:ℝ)*periodicStabilityThreshold (Fin 11))/2*periodicD11GreenEnergy<0 := by
  have h := periodicD11_energy_lower
  have he := competitor_entropy_bound
  have hm := mul_lt_mul_of_pos_left h (by norm_num : (0:ℝ)<(8653/8673)/2)
  nlinarith

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicD11_negative_free_energy
#check @DGRHS.Periodic.periodicD11_negative_free_energy
