import DGRHS.Gaussian.PeriodicL1FourierUniqueness
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-! Draft domination for the actual circle logarithm along Abel radii. The
bound is proved from the unit-circle norm identity, not a Fourier assumption.
The endpoint z=1 is excluded explicitly for the later Haar-AE argument. -/
noncomputable section
open MeasureTheory
namespace DGRHS.Periodic

lemma periodicD1_abel_norm_sq (r : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    ‖(1:ℂ)-(r:ℂ)*z‖^2=(1-r)^2+r*‖(1:ℂ)-z‖^2 := by
  have hs := Complex.sq_norm z
  rw [hz,Complex.normSq_apply] at hs
  rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,zero_add,sub_zero]
  linear_combination (r-r^2)*hs

lemma periodicD1_abel_norm_bounds (r : ℝ) (hr : (1:ℝ)/2≤r) (hr1 : r≤1)
    (z : ℂ) (hz : ‖z‖=1) :
    ‖(1:ℂ)-z‖/2≤‖(1:ℂ)-(r:ℂ)*z‖ ∧ ‖(1:ℂ)-(r:ℂ)*z‖≤2 := by
  have hr0 : 0≤r := by linarith
  constructor
  · have hs := periodicD1_abel_norm_sq r z hz
    have hn := norm_nonneg ((1:ℂ)-(r:ℂ)*z)
    have hn' := norm_nonneg ((1:ℂ)-z)
    have hb := mul_nonneg (by linarith : 0≤r-(1:ℝ)/4) (sq_nonneg ‖(1:ℂ)-z‖)
    nlinarith [sq_nonneg (1-r)]
  · calc
      _ ≤ ‖(1:ℂ)‖+‖(r:ℂ)*z‖ := norm_sub_le _ _
      _ = 1+r := by rw [norm_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0,hz,mul_one]
      _ ≤ 2 := by linarith

lemma periodicD1_abel_log_domination (r : ℝ) (hr : (1:ℝ)/2≤r) (hr1 : r≤1)
    (z : ℂ) (hz : ‖z‖=1) (hne : z≠1) :
    |Real.log ‖(1:ℂ)-(r:ℂ)*z‖|≤Real.log 2+|Real.log ‖(1:ℂ)-z‖| := by
  have hn : 0<‖(1:ℂ)-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨hlo,hhi⟩ := periodicD1_abel_norm_bounds r hr hr1 z hz
  have hp : 0<‖(1:ℂ)-(r:ℂ)*z‖ := (half_pos hn).trans_le hlo
  have hloglo := Real.log_le_log (half_pos hn) hlo
  rw [Real.log_div hn.ne' (by norm_num : (2:ℝ)≠0)] at hloglo
  have hloghi := Real.log_le_log hp hhi
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log ‖(1:ℂ)-z‖)]
  · linarith [abs_nonneg (Real.log ‖(1:ℂ)-z‖)]

end DGRHS.Periodic
