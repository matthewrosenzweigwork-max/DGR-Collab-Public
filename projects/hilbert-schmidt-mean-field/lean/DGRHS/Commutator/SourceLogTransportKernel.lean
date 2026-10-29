import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-
Original source eq:Andef / eq:knetadef, logarithmic interaction -log(norm z).
Kernel derivative only: the velocity difference is a frozen contraction vector.
Native primary provenance: pinned Mathlib InnerProductSpace.Calculus and Log.Deriv,
Apache2.0; exact native snapshots/search receipts preserved in records/log-transport.
-/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace NNReal
namespace DGRHS.Commutator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceLogPotential (z : E) : ℝ := -Real.log ‖z‖

/-- Actual nth spatial Fréchet derivative contraction, with the excluded diagonal set to zero. -/
def sourceLogTransportKernel (n : ℕ) (v : E → E) (p : E × E) : ℝ := by
  classical
  exact if p.1 = p.2 then 0 else
    iteratedFDeriv ℝ n sourceLogPotential (p.1 - p.2) (fun _ => v p.1 - v p.2)

omit [InnerProductSpace ℝ E] in
theorem sourceLogPotential_eq_half_log_sq (z : E) :
    sourceLogPotential z = -(1 / 2 : ℝ) * Real.log (‖z‖ ^ 2) := by
  rw [Real.log_pow]
  unfold sourceLogPotential
  push_cast
  ring

theorem sourceLogPotential_fderiv_apply {z : E} (hz : z ≠ 0) (w : E) :
    fderiv ℝ sourceLogPotential z w = -⟪z, w⟫ / ‖z‖ ^ 2 := by
  have hsq : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hd := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.log hsq).const_mul (-(1 / 2 : ℝ))
  have heq : sourceLogPotential (E := E) =
      (fun t => -(1 / 2 : ℝ) * Real.log (‖t‖ ^ 2)) :=
    funext sourceLogPotential_eq_half_log_sq
  rw [heq, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

theorem sourceLogTransportKernel_one (v : E → E) (p : E × E) :
    sourceLogTransportKernel 1 v p = -⟪p.1 - p.2, v p.1 - v p.2⟫ / ‖p.1 - p.2‖ ^ 2 := by
  by_cases hp : p.1 = p.2
  · simp [sourceLogTransportKernel, hp]
  · rw [sourceLogTransportKernel, ite_eq_right hp, iteratedFDeriv_one_apply]
    exact sourceLogPotential_fderiv_apply (sub_ne_zero.mpr hp) _

theorem abs_sourceLogTransportKernel_one_le {v : E → E} {K : ℝ≥0}
    (hv : LipschitzWith K v) (p : E × E) :
    |sourceLogTransportKernel 1 v p| ≤ K := by
  rw [sourceLogTransportKernel_one]
  by_cases hp : p.1 = p.2
  · simp [hp]
  have hz : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  have hw : ‖v p.1 - v p.2‖ ≤ K * ‖p.1 - p.2‖ := by
    simpa only [dist_eq_norm] using hv.dist_le_mul p.1 p.2
  rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg ‖p.1 - p.2‖)]
  apply (div_le_iff₀ (sq_pos_of_pos hz)).mpr
  have hc := abs_real_inner_le_norm (p.1 - p.2) (v p.1 - v p.2)
  nlinarith [mul_le_mul_of_nonneg_left hw hz.le]

section Measurable
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_sourceLogTransportKernel_one {v : E → E} {K : ℝ≥0}
    (hv : LipschitzWith K v) : Measurable (sourceLogTransportKernel 1 v) := by
  have hz : Continuous (fun p : E × E => p.1 - p.2) := continuous_fst.sub continuous_snd
  have hw : Continuous (fun p : E × E => v p.1 - v p.2) :=
    (hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)
  have hm := (hz.inner hw).measurable.neg.div (hz.norm.measurable.pow_const 2)
  have heq : sourceLogTransportKernel 1 v =
      (fun p => -⟪p.1 - p.2, v p.1 - v p.2⟫ / ‖p.1 - p.2‖ ^ 2) :=
    funext (sourceLogTransportKernel_one v)
  rw [heq]
  exact hm
end Measurable

#print axioms sourceLogPotential_fderiv_apply
#print axioms sourceLogTransportKernel_one
#print axioms abs_sourceLogTransportKernel_one_le
#print axioms measurable_sourceLogTransportKernel_one
end DGRHS.Commutator
