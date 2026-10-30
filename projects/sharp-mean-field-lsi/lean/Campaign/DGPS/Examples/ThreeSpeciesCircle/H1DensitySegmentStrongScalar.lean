import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv

/-! Elementary quantitative Jensen from honest scalar derivative witnesses.
Actual density-path Hessian lower bounds are supplied by a separate module. -/

noncomputable section
open Set

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A true lower bound on the second derivative gives the quadratic Jensen
gain, including both closed-segment endpoints. No sign of A is required. -/
theorem h1DensitySegment_scalar_strongJensen (F F1 F2 : ℝ → ℝ) (A : ℝ)
    (h1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F1 t) t)
    (h2 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F1 (F2 t) t)
    (hlow : ∀ t ∈ Ioo (0 : ℝ) 1, 2 * A ≤ F2 t) :
    ∀ θ ∈ Icc (0 : ℝ) 1,
      F θ ≤ (1 - θ) * F 0 + θ * F 1 - A * θ * (1 - θ) := by
  let G := fun t : ℝ => F t - A * t ^ 2
  let G1 := fun t : ℝ => F1 t - 2 * A * t
  let G2 := fun t : ℝ => F2 t - 2 * A
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt G (G1 t) t := by
    have hq : HasDerivAt (fun s : ℝ => A * s ^ 2) (2 * A * t) t := by
      convert ((hasDerivAt_id t).pow 2).const_mul A using 1 <;> simp [Pi.pow_apply] <;> ring
    exact (h1 t ht).sub hq
  have hG1 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt G1 (G2 t) t := by
    have hl : HasDerivAt (fun s : ℝ => 2 * A * s) (2 * A) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * A)
    exact (h2 t ht).sub hl
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) G := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f := G) (f' := G1) (f'' := G2)
      (convex_Icc (0 : ℝ) 1) ?_ ?_ ?_ ?_
    · intro t ht
      exact (hG t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hG t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hG1 t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact sub_nonneg.mpr (hlow t ht)
  intro θ hθ
  have hj := hconv.2 (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
    (sub_nonneg.mpr hθ.2) hθ.1 (by ring : (1 - θ) + θ = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hj
  dsimp only [G] at hj
  norm_num only [zero_pow, mul_zero, sub_zero, one_pow, mul_one] at hj
  nlinarith only [hj]

end DGPS.Examples.ThreeSpeciesCircle
