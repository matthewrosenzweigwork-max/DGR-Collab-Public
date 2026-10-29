import DGRHS.Gaussian.D11Imported.ElevenCoordinateDefinitions
import DGRHS.Gaussian.D11Imported.ElevenMarginal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The true marginal and its half-open-cell probabilities, with mass obtained
from the eleven-dimensional density by Fubini. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma coordinateProfile_pos (t : ℝ) : 0 < coordinateProfile t := by
  unfold coordinateProfile
  positivity

lemma coordinateProfile_continuous : Continuous coordinateProfile := by
  unfold coordinateProfile
  fun_prop (disch := intro x; left; positivity)

lemma euclideanProfile_cons_integrable :
    Integrable (fun z : ℝ × (Fin 10 → ℝ) => euclideanProfile (Fin.cons z.1 z.2)) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin 11 => ℝ) 0).symm.integrable_comp_of_integrable
    euclideanProfile_integrable
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq, Function.comp_def] at h
  convert h using 1 <;> rfl

lemma coordinateProfile_integrable : Integrable coordinateProfile := by
  change Integrable (fun t : ℝ => 1280/(63*Real.pi) * (1+25*t^2)^(-6:ℤ))
  have h := euclideanProfile_cons_integrable.integral_prod_left
  simpa only [euclideanProfile_marginal, coordinateProfile] using h

lemma coordinateProfile_integral : (∫ t : ℝ, coordinateProfile t) = 1 := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin 11 => ℝ) 0).symm.integral_comp'
    euclideanProfile
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] at h
  change (∫ z : ℝ × (Fin 10 → ℝ), euclideanProfile (Fin.cons z.1 z.2) ∂(volume.prod volume)) =
    (∫ y : Fin 11 → ℝ, euclideanProfile y) at h
  rw [integral_prod _ euclideanProfile_cons_integrable, euclideanProfile_integral] at h
  simpa only [euclideanProfile_marginal, coordinateProfile] using h

lemma coordinateLabelProbability_nonneg (n : ℤ) : 0 ≤ coordinateLabelProbability n :=
  integral_nonneg (fun _ => (coordinateProfile_pos _).le)

lemma coordinateLabelProbability_interval (n : ℤ) :
    coordinateLabelProbability n = ∫ t in ((n:ℝ)-1/2)..((n:ℝ)+1/2), coordinateProfile t := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact integral_Ico_eq_integral_Ioc

lemma coordinateLabelProbability_hasSum : HasSum coordinateLabelProbability 1 := by
  have h := coordinateProfile_integrable.hasSum_intervalIntegral (-(1/2:ℝ))
  rw [coordinateProfile_integral] at h
  apply h.congr_fun
  intro n
  rw [coordinateLabelProbability_interval]
  congr 1 <;> ring

#print axioms coordinateLabelProbability_hasSum
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
