import LeanResearch.PeriodicAttractiveLogGas.LogHessian

/-! Quantitative operator-norm bounds for the actual logarithmic derivatives. -/

noncomputable section
open scoped RealInnerProductSpace

namespace PeriodicAttractiveLogGas

theorem norm_hessian_planarLogKernel_le {x : PlanarSpace} (hx : x ≠ 0) :
    ‖fderiv ℝ (fderiv ℝ planarLogKernel) x‖ ≤ 3 * (‖x‖ ^ 2)⁻¹ := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hi : 0 ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_fderiv_planarLogKernel_apply hx]
  have hiu : |inner ℝ x u| ≤ ‖x‖ * ‖u‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x u
  have hiv : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x v
  have huv : |inner ℝ u v| ≤ ‖u‖ * ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) u v
  calc
    ‖2 * (‖x‖ ^ 2)⁻¹ ^ 2 * inner ℝ x u * inner ℝ x v -
        (‖x‖ ^ 2)⁻¹ * inner ℝ u v‖ ≤
        ‖2 * (‖x‖ ^ 2)⁻¹ ^ 2 * inner ℝ x u * inner ℝ x v‖ +
        ‖(‖x‖ ^ 2)⁻¹ * inner ℝ u v‖ := norm_sub_le _ _
    _ = 2 * (‖x‖ ^ 2)⁻¹ ^ 2 * |inner ℝ x u| * |inner ℝ x v| +
        (‖x‖ ^ 2)⁻¹ * |inner ℝ u v| := by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hi, abs_pow]
      norm_num
    _ ≤ 2 * (‖x‖ ^ 2)⁻¹ ^ 2 * (‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) +
        (‖x‖ ^ 2)⁻¹ * (‖u‖ * ‖v‖) := by gcongr
    _ = (3 * (‖x‖ ^ 2)⁻¹ * ‖u‖) * ‖v‖ := by field_simp; ring

end PeriodicAttractiveLogGas
