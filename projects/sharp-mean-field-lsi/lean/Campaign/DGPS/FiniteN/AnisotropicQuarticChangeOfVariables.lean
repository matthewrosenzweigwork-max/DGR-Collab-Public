import DGPS.FiniteN.AnisotropicQuarticChart
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Actual integration through the quartic chart

This adapts the existing FIN059 change-of-variables argument to an open two-dimensional
chart. It proves integrability of the Jacobian-weighted pullback and the genuine integral
identity from the chart geometry. Identification of the triangular determinant with the
retained FIN068 inverse derivative and metric-restored FIN069 coercivity remain separate.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace DGPS.FiniteN

/-- Two-dimensional change of variables for the FIN068 chart, including actual integrability
of the Jacobian-weighted pullback. Both inverse identities and source/image membership are
geometric inputs, and no integral equality or estimate is assumed. -/
theorem quartic_chart_change_of_variables (U Q : Set (ℝ × ℝ)) (hQo : IsOpen Q)
    (T R : ℝ × ℝ → ℝ × ℝ) (hR : ContDiffOn ℝ ∞ R Q)
    (hTU : ∀ x ∈ U, T x ∈ Q) (hRQ : ∀ q ∈ Q, R q ∈ U)
    (hTR : ∀ q ∈ Q, T (R q) = q) (hRT : ∀ x ∈ U, R (T x) = x)
    (g : ℝ × ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) :
    IntegrableOn (fun q => |(fderiv ℝ R q).det| * g (R q)) Q ∧
      (∫ x, g x) = ∫ q in Q, |(fderiv ℝ R q).det| * g (R q) := by
  have himg : R '' Q = U := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hRQ q hq
    · intro hx
      exact ⟨T x, hTU x hx, hRT x hx⟩
  have hinj : Set.InjOn R Q := by
    intro q₁ hq₁ q₂ hq₂ heq
    calc q₁ = T (R q₁) := (hTR q₁ hq₁).symm
      _ = T (R q₂) := congrArg T heq
      _ = q₂ := hTR q₂ hq₂
  have hder : ∀ q ∈ Q, HasFDerivWithinAt R (fderiv ℝ R q) Q q := by
    intro q hq
    exact ((hR.contDiffAt (hQo.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  constructor
  · have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume) hQo.measurableSet hder hinj g).1 (by rw [himg]; exact hgi.integrableOn)
    simpa only [smul_eq_mul] using h
  · have hzero : ∀ x, x ∉ U → g x = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (fun h => hx (hgU h))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) hzero, ← himg]
    simpa only [smul_eq_mul] using integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) hQo.measurableSet hder hinj g

end DGPS.FiniteN
