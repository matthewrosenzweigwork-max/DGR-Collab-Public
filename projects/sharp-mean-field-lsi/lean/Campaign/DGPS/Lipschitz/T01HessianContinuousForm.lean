import DGPS.Lipschitz.T01HessianCoercivity
import SharpSymmetricLSI.Paper.Coercivity2

/-!
# The continuous quadratic-form consequence of the actual density Hessian

This is the exact form input used by the small-entropy estimate. The coercivity constant
may be decreased to at most one; the mean-zero continuous test is otherwise unrestricted.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Canonical coercivity implies the continuous centered-kernel form bound, with a positive
constant at most one. This changes neither the reference measure nor the interaction kernel. -/
theorem t01_continuous_hessian_form (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (hH : IsCoerciveDensityHessian A μ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ w : C(Torus d, ℝ),
      (∫ x, w x ∂(μ : Measure (Torus d))) = 0 →
        σ * (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) ≤
          (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) +
            SharpLSI.quadF (centeredKernel A (μ : Measure (Torus d)))
              (μ : Measure (Torus d)) w := by
  obtain ⟨c, hc, hbound⟩ := hH
  refine ⟨min c 1, lt_min hc zero_lt_one, min_le_right _ _, fun w hw => ?_⟩
  let v : Lp ℝ 2 (μ : Measure (Torus d)) :=
    ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ w
  have hrep : v =ᵐ[(μ : Measure (Torus d))] w :=
    ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) w
  have hvmean : v ∈ centeredL2 μ := by
    rw [mem_centeredL2, integral_toLp_eq]
    exact hw
  let f : centeredL2 μ := ⟨v, hvmean⟩
  have hn : ‖v‖ ^ 2 = ∫ x, w x ^ 2 ∂(μ : Measure (Torus d)) := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
    exact integral_congr_ae (hrep.mono fun x hx => by
      change v x * v x = w x ^ 2
      rw [hx, pow_two])
  have hOp : centeredOperator A (μ : Measure (Torus d)) v =ᵐ[(μ : Measure (Torus d))]
      fun x => ∫ y, centeredKernel A (μ : Measure (Torus d)) x y * w y
        ∂(μ : Measure (Torus d)) := by
    filter_upwards [centeredOperator_apply_ae A (μ : Measure (Torus d)) v] with x hx
    exact hx.trans (integral_congr_ae (hrep.mono fun y hy => by
      change centeredKernel A (μ : Measure (Torus d)) x y * v y =
        centeredKernel A (μ : Measure (Torus d)) x y * w y
      rw [hy]))
  have hq : inner ℝ v (DGPS.kernelOp A μ v) =
      SharpLSI.quadF (centeredKernel A (μ : Measure (Torus d)))
        (μ : Measure (Torus d)) w := by
    rw [← centeredOperator_eq_kernelOp A μ, inner_eq_integral]
    unfold SharpLSI.quadF
    exact integral_congr_ae ((hrep.and hOp).mono fun x hx => by
      change v x * (centeredOperator A (μ : Measure (Torus d)) v) x =
        w x * ∫ y, centeredKernel A (μ : Measure (Torus d)) x y * w y
          ∂(μ : Measure (Torus d))
      rw [hx.1, hx.2])
  have hform : inner ℝ f (densityHessian A μ f) =
      (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) +
        SharpLSI.quadF (centeredKernel A (μ : Measure (Torus d)))
          (μ : Measure (Torus d)) w := by
    change inner ℝ v (v + DGPS.kernelOp A μ v) = _
    rw [inner_add_right, real_inner_self_eq_norm_sq, hn, hq]
  calc min c 1 * (∫ x, w x ^ 2 ∂(μ : Measure (Torus d)))
      ≤ c * (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (integral_nonneg fun x => sq_nonneg _)
    _ = c * ‖f‖ ^ 2 := by rw [← hn]; rfl
    _ ≤ inner ℝ f (densityHessian A μ f) := hbound f
    _ = _ := hform

end DGPS.Lipschitz
