import DGRHS.Gaussian.D11Imported.ElevenCoordinateLaw
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The one-coordinate polynomial tail bound used in the lattice-label moment. -/
noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma coordinateProfile_even (t : ℝ) : coordinateProfile (-t) = coordinateProfile t := by
  simp [coordinateProfile]

lemma coordinateProfile_le_power {t : ℝ} (ht : 0 < t) :
    coordinateProfile t ≤ (1280/(63*Real.pi*25^6)) * t^(-(12:ℝ)) := by
  have h0 : 0 < 25*t^2 := by positivity
  have hi : ((1+25*t^2)^6)⁻¹ ≤ ((25*t^2)^6)⁻¹ := by
    apply inv_anti₀ (pow_pos h0 6)
    exact pow_le_pow_left₀ h0.le (by linarith) 6
  have hc : 0 ≤ 1280/(63*Real.pi) := by positivity
  have h := mul_le_mul_of_nonneg_left hi hc
  unfold coordinateProfile
  rw [show -(12:ℝ) = ((-12:ℤ):ℝ) by norm_num, Real.rpow_intCast]
  simp only [zpow_neg, zpow_ofNat]
  convert h using 1 <;> first | rfl | (field_simp <;> ring)

lemma coordinateProfile_tail {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi a, coordinateProfile t) ≤
      (1280/(693*Real.pi*25^6)) * a^(-11:ℤ) := by
  have hm : IntegrableOn (fun t : ℝ => (1280/(63*Real.pi*25^6)) * t^(-(12:ℝ))) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(12:ℝ)< -1) ha).const_mul _
  have hb := integral_mono_ae coordinateProfile_integrable.integrableOn hm
    (show ∀ᵐ t ∂volume.restrict (Ioi a), coordinateProfile t ≤
        (1280/(63*Real.pi*25^6)) * t^(-(12:ℝ)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact coordinateProfile_le_power (ha.trans ht))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(12:ℝ)< -1) ha] at hb
  have he : -(a^(-(12:ℝ)+1))/(-(12:ℝ)+1) = a^(-11:ℤ)/11 := by
    rw [show -(12:ℝ)+1 = ((-11:ℤ):ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [he] at hb
  convert hb using 1 <;> first | rfl | ring

lemma coordinateLabelProbability_even (n : ℤ) :
    coordinateLabelProbability (-n) = coordinateLabelProbability n := by
  rw [coordinateLabelProbability_interval, coordinateLabelProbability_interval]
  have h := intervalIntegral.integral_comp_neg (f := coordinateProfile)
    (a := (n:ℝ)-1/2) (b := (n:ℝ)+1/2)
  simp only [coordinateProfile_even] at h
  rw [h]
  congr 1 <;> push_cast <;> ring

#print axioms coordinateProfile_tail
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
