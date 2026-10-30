import DGPS.FiniteN.AnisotropicQuarticScale
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A fixed smooth extension of the reduced quartic potential

The selected FIN068 reduced potential is only smooth on a fixed interval. Multiplication
by a fixed bump extends it smoothly to the line while preserving its germ on the whole
smaller interval. Neither the cutoff nor its agreement window depends on particle number.
-/

open Filter Topology Set Metric
open scoped ContDiff

namespace DGPS.FiniteN

/-- Extend a locally smooth reduced potential without changing it near any point of the
fixed half-width interval. -/
theorem quartic_reduced_extension (δ : ℝ) (hδ : 0 < δ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ ∞ φ (Ioo (-δ) δ)) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧
      ∀ y : ℝ, |y| < δ / 2 → Φ =ᶠ[nhds y] φ := by
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := δ / 2
      rOut := 3 * δ / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let Φ : ℝ → ℝ := fun y => χ y * φ y
  have hsupp : tsupport χ ⊆ Ioo (-δ) δ := by
    rw [χ.tsupport_eq]
    intro y hy
    have hy' : |y| ≤ 3 * δ / 4 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, χ] using hy
    exact abs_lt.mp (lt_of_le_of_lt hy' (by linarith))
  refine ⟨Φ, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Ioo (-δ) δ
    · exact χ.contDiffAt.mul (hφ.contDiffAt (isOpen_Ioo.mem_nhds hy))
    · have hyχ : y ∉ tsupport χ := fun h => hy (hsupp h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hyχ] with z hz
      change χ z * φ z = 0
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  · intro y hy
    have hyb : y ∈ ball (0 : ℝ) χ.rIn := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, χ] using hy
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hyb] with z hz
    change χ z * φ z = φ z
    rw [hz]
    simp

/-- The extension preserves the first two ordinary derivatives throughout its agreement
window, so the actual FIN068 reduced curvature bound transfers there. -/
theorem quartic_reduced_extension_derivatives (δ : ℝ) (hδ : 0 < δ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ ∞ φ (Ioo (-δ) δ)) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ ∀ y : ℝ, |y| < δ / 2 →
      Φ y = φ y ∧ deriv Φ y = deriv φ y ∧ deriv (deriv Φ) y = deriv (deriv φ) y := by
  obtain ⟨Φ, hΦ, heq⟩ := quartic_reduced_extension δ hδ φ hφ
  refine ⟨Φ, hΦ, fun y hy => ?_⟩
  have h := heq y hy
  exact ⟨h.eq_of_nhds, h.deriv_eq, h.deriv.deriv_eq⟩

end DGPS.FiniteN
