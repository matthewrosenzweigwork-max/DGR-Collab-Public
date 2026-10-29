import DGPS.FiniteN.Tools.GroundState

open MeasureTheory Real
open scoped ContDiff

/-!
# FIN022: negative direction local Dirichlet rate

Module `DGPS.FiniteN.Tools.NegativeDirection` (placed in a new file instead of
`DGPS/FiniteN/Tools.lean` to avoid file contention; R5 note).

On `ℝ^k = EuclideanSpace ℝ (Fin k)`, let `ψ` be smooth, `v` a fixed Euclidean unit vector, and
`U` a set (the neighborhood) on which the second directional derivative
`∂_v² ψ = fderiv (fun y => fderiv ψ y v) x v` is `≤ -c` for some `c > 0`. Then every smooth `F`
with compact support contained in `U`, and every `N ≥ 0`, satisfies
`∫ ‖∇F‖² e^{-Nψ} ≥ (c N / 2) ∫ F² e^{-Nψ}`. No assumption is made on the other Hessian directions.
-/

namespace DGPS.FiniteN

/-- FIN022 (`DGPS.FiniteN.negative_direction_local_dirichlet_rate`). -/
theorem negative_direction_local_dirichlet_rate {k : ℕ} (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (v : EuclideanSpace ℝ (Fin k)) (hv : ‖v‖ = 1)
    (U : Set (EuclideanSpace ℝ (Fin k))) (c : ℝ) (_hc : 0 < c)
    (hneg : ∀ x ∈ U, fderiv ℝ (fun y => fderiv ℝ ψ y v) x v ≤ -c)
    (N : ℝ) (hN : 0 ≤ N)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFU : tsupport F ⊆ U) :
    c * N / 2 * ∫ x, (F x) ^ 2 * exp (-(N * ψ x)) ≤
      ∫ x, ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x)) := by
  obtain ⟨hI1, hI2, hEq⟩ := groundState_direction_aux
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin k)))) N ψ F hψ hF hFc v
  have hEc : Continuous (fun y => exp (-(N * ψ y))) :=
    (contDiff_exp.comp (contDiff_const.mul hψ).neg).continuous
  have hFcont : Continuous F := hF.continuous
  have hdF : Continuous (fun x => fderiv ℝ F x) := hF.continuous_fderiv (by simp)
  have hGint : Integrable (fun x => (F x) ^ 2 * exp (-(N * ψ x))) volume := by
    refine Continuous.integrable_of_hasCompactSupport ((hFcont.pow 2).mul hEc) ?_
    have : (fun x => (F x) ^ 2 * exp (-(N * ψ x))) =
        (F * F) * (fun y => exp (-(N * ψ y))) := by funext x; simp [sq]
    rw [this]
    exact (hFc.mul_right).mul_right
  have hLint : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x))) volume := by
    refine Continuous.integrable_of_hasCompactSupport ((hdF.norm.pow 2).mul hEc) ?_
    have h0 : HasCompactSupport (fun x => ‖fderiv ℝ F x‖) := (hFc.fderiv ℝ).norm
    have : (fun x => ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x))) =
        ((fun x => ‖fderiv ℝ F x‖) * (fun x => ‖fderiv ℝ F x‖)) *
          (fun y => exp (-(N * ψ y))) := by funext x; simp [sq]
    rw [this]
    exact (h0.mul_right).mul_right
  -- the directional energy is dominated by the full energy
  have hdir : ∫ x, (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x)) ≤
      ∫ x, ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x)) := by
    refine integral_mono hI1 hLint fun x => ?_
    have h1 : |fderiv ℝ F x v| ≤ ‖fderiv ℝ F x‖ := by
      have := (fderiv ℝ F x).le_opNorm v
      rw [hv, mul_one] at this
      simpa [Real.norm_eq_abs] using this
    have h2 : (fderiv ℝ F x v) ^ 2 ≤ ‖fderiv ℝ F x‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_right h2 (exp_pos _).le
  -- the ground-state side is at least the potential term
  have hwt : ∀ x, (F x * exp (-(N * ψ x) / 2)) ^ 2 = (F x) ^ 2 * exp (-(N * ψ x)) := by
    intro x
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hlow : c * N / 2 * ∫ x, (F x) ^ 2 * exp (-(N * ψ x)) ≤
      ∫ x, ((fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4
          - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) := by
    rw [← integral_const_mul]
    refine integral_mono (hGint.const_mul _) hI2 fun x => ?_
    show c * N / 2 * ((F x) ^ 2 * exp (-(N * ψ x))) ≤ _
    rw [← hwt x]
    by_cases hx : F x = 0
    · simp only [hx, zero_mul, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero]
      positivity
    · have hxU : x ∈ U := hFU (subset_tsupport F hx)
      have h3 := hneg x hxU
      have hsq : 0 ≤ (F x * exp (-(N * ψ x) / 2)) ^ 2 := sq_nonneg _
      have h4 : c * N / 2 ≤ N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4
          - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2 := by
        have : 0 ≤ N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h3 hN]
      have h5 := mul_le_mul_of_nonneg_right h4 hsq
      have h6 : 0 ≤ (fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2 := sq_nonneg _
      linarith
  rw [← hEq] at hlow
  exact hlow.trans hdir

end DGPS.FiniteN
