/- Constants cancel from the actual normalized Esscher transform.
Pinned native tilted_tilted and actual probability normalization are reused. -/
import DGRHS.CLT.NativeTiltAdapter
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

lemma integrable_exp_add_const (Y : S → ℝ)
    (hi : Integrable (fun x => Real.exp (Y x)) μ) (c : ℝ) :
    Integrable (fun x => Real.exp (Y x+c)) μ := by
  simpa only [Real.exp_add] using hi.mul_const (Real.exp c)

lemma integral_exp_add_const (Y : S → ℝ) (c : ℝ) :
    (∫ x, Real.exp (Y x+c) ∂μ) = Real.exp c * (∫ x, Real.exp (Y x) ∂μ) := by
  simp_rw [Real.exp_add]
  rw [integral_mul_const,mul_comm]

lemma exponentialTiltMeasure_add_const [IsProbabilityMeasure μ]
    (Y : S → ℝ) (hi : Integrable (fun x => Real.exp (Y x)) μ) (c : ℝ) :
    exponentialTiltMeasure μ (fun x => Y x+c) = exponentialTiltMeasure μ Y := by
  simp only [exponentialTiltMeasure_eq_native]
  letI := isProbabilityMeasure_tilted hi
  calc
    _ = (μ.tilted Y).tilted (fun _ => c) := by
      exact (tilted_tilted hi (fun _ => c)).symm
    _ = μ.tilted Y := tilted_const _ c
end DGRHS.CLT
#print axioms DGRHS.CLT.integrable_exp_add_const
#print axioms DGRHS.CLT.integral_exp_add_const
#print axioms DGRHS.CLT.exponentialTiltMeasure_add_const
#check @DGRHS.CLT.exponentialTiltMeasure_add_const
