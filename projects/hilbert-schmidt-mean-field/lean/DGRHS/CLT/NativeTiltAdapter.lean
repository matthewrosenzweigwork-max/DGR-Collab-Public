/- Bind the checked normalized density to pinned Mathlib's native tilted measure.
Native proper-integrability/integral formulas are reused downstream. -/
import DGRHS.CLT.ExponentialTiltMeasure
import Mathlib.MeasureTheory.Measure.Tilted
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S]

lemma exponentialTiltMeasure_eq_native (μ : Measure S) (Y : S → ℝ) :
    exponentialTiltMeasure μ Y = μ.tilted Y := rfl

lemma integrable_exponentialTiltMeasure_iff {μ : Measure S} {Y : S → ℝ}
    (hi : Integrable (fun x => Real.exp (Y x)) μ) (F : S → ℝ) :
    Integrable F (exponentialTiltMeasure μ Y) ↔
      Integrable (fun x => Real.exp (Y x)*F x) μ := by
  rw [exponentialTiltMeasure_eq_native]
  simpa only [smul_eq_mul] using integrable_tilted_iff hi F

lemma integral_exp_exponentialTiltMeasure (μ : Measure S) (Y F : S → ℝ) :
    (∫ x, Real.exp (F x) ∂exponentialTiltMeasure μ Y) =
      (∫ x, Real.exp (Y x+F x) ∂μ)/(∫ x, Real.exp (Y x) ∂μ) := by
  rw [exponentialTiltMeasure_eq_native]
  simpa only [Pi.add_apply] using integral_exp_tilted Y F

end DGRHS.CLT
#print axioms DGRHS.CLT.exponentialTiltMeasure_eq_native
#print axioms DGRHS.CLT.integrable_exponentialTiltMeasure_iff
#print axioms DGRHS.CLT.integral_exp_exponentialTiltMeasure
#check @DGRHS.CLT.integrable_exponentialTiltMeasure_iff
