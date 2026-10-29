/- Actual normalized exponential density on a probability space.
Its probability mass and integral formula are proved from proper integrability. -/
import DGRHS.CLT.ExponentialMomentTransfer
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S]

def exponentialTiltMeasure (μ : Measure S) (Y : S → ℝ) : Measure S :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp (Y x)/(∫ z, Real.exp (Y z) ∂μ)))

lemma exponentialTiltMeasure_probability {μ : Measure S} [IsProbabilityMeasure μ]
    (Y : S → ℝ) (hi : Integrable (fun x => Real.exp (Y x)) μ) :
    IsProbabilityMeasure (exponentialTiltMeasure μ Y) := by
  have hz : 0 < ∫ z, Real.exp (Y z) ∂μ := integral_exp_pos hi
  refine ⟨?_⟩
  unfold exponentialTiltMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (ae_of_all _ fun x => div_nonneg (Real.exp_pos _).le hz.le), integral_div]
  simp [hz.ne']

lemma integral_exponentialTiltMeasure {μ : Measure S} [IsProbabilityMeasure μ]
    (Y : S → ℝ) (hY : AEMeasurable Y μ)
    (hi : Integrable (fun x => Real.exp (Y x)) μ) (F : S → ℝ) :
    (∫ x, F x ∂exponentialTiltMeasure μ Y) =
      (∫ x, F x*Real.exp (Y x) ∂μ)/(∫ z, Real.exp (Y z) ∂μ) := by
  have hz : 0 < ∫ z, Real.exp (Y z) ∂μ := integral_exp_pos hi
  have hd : AEMeasurable (fun x => ENNReal.ofReal
      (Real.exp (Y x)/(∫ z, Real.exp (Y z) ∂μ))) μ := by
    fun_prop
  unfold exponentialTiltMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have he : (fun x => (ENNReal.ofReal
      (Real.exp (Y x)/(∫ z, Real.exp (Y z) ∂μ))).toReal • F x) =
      fun x => (F x*Real.exp (Y x))/(∫ z, Real.exp (Y z) ∂μ) := by
    funext x
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hz.le), smul_eq_mul]
    ring
  rw [he, integral_div]

end DGRHS.CLT
#print axioms DGRHS.CLT.exponentialTiltMeasure_probability
#print axioms DGRHS.CLT.integral_exponentialTiltMeasure
#check @DGRHS.CLT.exponentialTiltMeasure_probability
#check @DGRHS.CLT.integral_exponentialTiltMeasure
