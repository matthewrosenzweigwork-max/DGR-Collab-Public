/- Source uniform rows imply a bound for the actual integral operator.
Reuses the licensed, checked operator and actual native proper Fubini;
no eigenbasis, operator bound or spectral conclusion is a premise. -/
import DGRHS.Attractive.RowMoments
import DGRHS.Attractive.CanonicalFactorialMoment
import DGRHS.Kernel.Operator
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma rowMoment_joint_second_bound (h : S × S → ℝ) (hh : Measurable h)
    (C : ℝ) (hrow : RowFactorialMoments μ h C) :
    (∫ p,h p^2 ∂μ.prod μ) ≤ 2*C^2 := by
  have hi := joint_abs_power_integrable μ h hh C hrow 2 (by omega)
  calc
    _ = ∫ p,|h p|^2 ∂μ.prod μ := by simp only [sq_abs]
    _ = ∫ y,∫ x,|h (x,y)|^2 ∂μ ∂μ := integral_prod_symm _ hi
    _ ≤ ∫ y,(2*C^2:ℝ) ∂μ := integral_mono_ae hi.integral_prod_right
      (integrable_const _) (Filter.Eventually.of_forall fun y => by
        have hb := hrow.bound 2 (by omega) y
        norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,
          Nat.cast_one,mul_one] at hb
        simpa only [mul_comm] using hb)
    _ = 2*C^2 := by simp

lemma rowMoment_actual_operator_norm_le (h : S × S → ℝ) (hh : Measurable h)
    (C : ℝ) (hrow : RowFactorialMoments μ h C) :
    ‖DGRHS.Kernel.integralOperator h (joint_memLp μ h hh C hrow 2 (by omega))‖ ≤ 2*C := by
  let hk : MemLp h 2 (μ.prod μ) := joint_memLp μ h hh C hrow 2 (by omega)
  have hs : ‖hk.toLp h‖^2 ≤ 2*C^2 := by
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact rowMoment_joint_second_bound h hh C hrow
  have hn : ‖hk.toLp h‖ ≤ 2*C := by
    nlinarith [norm_nonneg (hk.toLp h),hrow.nonneg,sq_nonneg C]
  exact (DGRHS.Kernel.norm_integralOperator_le h hk).trans hn

lemma attractiveMomentConstant_two_le : (2:ℝ) ≤ attractiveMomentConstant := by
  have he : (1:ℝ) ≤ Real.exp 2 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0:ℝ)≤2 by norm_num)
  unfold attractiveMomentConstant
  linarith

lemma attractiveMomentConstant_four_le : (4:ℝ) ≤ attractiveMomentConstant := by
  have he : (1:ℝ) ≤ Real.exp 2 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0:ℝ)≤2 by norm_num)
  unfold attractiveMomentConstant
  linarith

lemma rowMoment_actual_operator_weak_margin (h : S × S → ℝ) (hh : Measurable h)
    (C β : ℝ) (hrow : RowFactorialMoments μ h C)
    (hβ : 0≤β) (hsmall : β*(attractiveMomentConstant*C)<1) :
    β*‖DGRHS.Kernel.integralOperator h
      (joint_memLp μ h hh C hrow 2 (by omega))‖ < 1 := by
  have hop := rowMoment_actual_operator_norm_le h hh C hrow
  have hC : 2*C≤attractiveMomentConstant*C :=
    mul_le_mul_of_nonneg_right attractiveMomentConstant_two_le hrow.nonneg
  exact (mul_le_mul_of_nonneg_left (hop.trans hC) hβ).trans_lt hsmall

lemma rowMoment_actual_operator_doubled_margin (h : S × S → ℝ) (hh : Measurable h)
    (C β : ℝ) (hrow : RowFactorialMoments μ h C)
    (hβ : 0≤β) (hsmall : β*(attractiveMomentConstant*C)<1) :
    2*β*‖DGRHS.Kernel.integralOperator h
      (joint_memLp μ h hh C hrow 2 (by omega))‖ < 1 := by
  have hop := rowMoment_actual_operator_norm_le h hh C hrow
  have hC : 4*C≤attractiveMomentConstant*C :=
    mul_le_mul_of_nonneg_right attractiveMomentConstant_four_le hrow.nonneg
  have he : 2*β*‖DGRHS.Kernel.integralOperator h
      (joint_memLp μ h hh C hrow 2 (by omega))‖ ≤ β*(4*C) := by
    nlinarith [mul_le_mul_of_nonneg_left hop (show 0≤2*β by positivity)]
  exact he.trans_lt ((mul_le_mul_of_nonneg_left hC hβ).trans_lt hsmall)

end DGRHS.Attractive
#check @DGRHS.Attractive.rowMoment_actual_operator_norm_le
#print axioms DGRHS.Attractive.rowMoment_joint_second_bound
#print axioms DGRHS.Attractive.rowMoment_actual_operator_norm_le
#print axioms DGRHS.Attractive.rowMoment_actual_operator_weak_margin
#print axioms DGRHS.Attractive.rowMoment_actual_operator_doubled_margin
