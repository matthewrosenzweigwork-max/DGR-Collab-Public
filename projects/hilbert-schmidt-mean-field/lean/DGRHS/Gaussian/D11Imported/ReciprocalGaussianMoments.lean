/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ReciprocalGaussianDerivative
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! Polynomial moments of the reciprocal Gaussian. Integration by parts
gives the half-integer Bessel recurrence with all boundary terms justified. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DGRHS.Gaussian.D11Imported.ReciprocalGaussian

def moment (n : ℕ) (a : ℝ) : ℝ := ∫ x in Ioi (0:ℝ), x^(2*n)*kernel a x

lemma pow_kernel_integrable (n : ℕ) (a : ℝ) :
    IntegrableOn (fun x : ℝ => x^n*kernel a x) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => x^n*Real.exp (-x^2)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0:ℝ)<1) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n) : (-1:ℝ)<(n:ℝ))
  apply hg.mono' (by unfold kernel; exact Measurable.aestronglyMeasurable (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.le n) (kernel_pos a x).le)]
  exact mul_le_mul_of_nonneg_left (kernel_le_gaussian a x) (pow_nonneg hx.le n)

lemma pow_kernel_tendsto_zero (n : ℕ) (hn : 0 < n) (a : ℝ) :
    Tendsto (fun x : ℝ => x^n*kernel a x) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x^n) (𝓝[>] 0) (𝓝 0) := by
    simpa [zero_pow (by omega : n ≠ 0)] using
      ((continuous_pow n).continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ => x^n) (𝓝[>] 0) (𝓝 (0^n)))
  apply squeeze_zero' _ _ hp
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (pow_nonneg hx.le n) (kernel_pos a x).le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hk : kernel a x ≤ 1 := (kernel_le_gaussian a x).trans (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))
    exact mul_le_of_le_one_right (pow_nonneg hx.le n) hk

lemma pow_kernel_tendsto_atTop (n : ℕ) (a : ℝ) :
    Tendsto (fun x : ℝ => x^n*kernel a x) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => |x|^n*Real.exp (-x^2)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (by norm_num : (0:ℝ)<1) (n:ℝ)).mono_left (show atTop ≤ cocompact ℝ from atTop_le_cocompact)
  apply squeeze_zero' _ _ hg
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact mul_nonneg (pow_nonneg hx.le n) (kernel_pos a x).le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [abs_of_pos hx]
    exact mul_le_mul_of_nonneg_left (kernel_le_gaussian a x) (pow_nonneg hx.le n)

lemma kernel_spatial_hasDerivAt (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (kernel a) ((-2*x+2*a^2/x^3)*kernel a x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.sub
    (((hasDerivAt_const x a).div (hasDerivAt_id x) (ne_of_gt hx)).pow 2)).exp
  convert h using 1
  · rfl
  · dsimp [kernel]
    conv_rhs => rw [mul_comm]
    congr 1
    field_simp
    ring

lemma moment_zero (a : ℝ) : moment 0 a = mass a := by simp [moment, mass]

end DGRHS.Gaussian.D11Imported.ReciprocalGaussian
