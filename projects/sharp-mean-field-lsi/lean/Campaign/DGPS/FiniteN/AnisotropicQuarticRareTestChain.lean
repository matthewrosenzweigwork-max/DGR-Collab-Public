import DGPS.FiniteN.AnisotropicQuarticRareTestDerivatives

/-! Exact cutoff chain rule and the inner derivative support. -/

open DGPS.Models DGPS.FiniteN.ScalarFoldFIN064
open scoped ContDiff

namespace DGPS.FiniteN

/-- The bump derivative vanishes on the closed inner interval, including its
boundary, because these points are genuine global maxima of the smooth bump. -/
theorem quartic_cutoff_derivative_inner_zero (u : ℝ) (hu : |u| ≤ 1) :
    deriv chiFIN064 u = 0 := by
  have hm : IsLocalMax chiFIN064 u := Filter.Eventually.of_forall fun v => by
    rw [chi_one_FIN064 hu]
    exact chi_le_one_FIN064 v
  exact hm.deriv_eq_zero

/-- The actual two-coordinate rare test has the physical derivatives displayed
here, with the longitudinal and transverse cutoff contributions separated. -/
theorem quarticRareTest_partial (δ : ℝ) (N : ℕ+) (i : Fin N) (x : ParticleSpace 1 N) :
    particlePartial i 0 (quarticRareTest δ N) x =
      (chiFIN064 ((N : ℝ) ^ (1 / 4 : ℝ) * quarticEmpiricalSin N x) *
        deriv chiFIN064 ((2 / δ) * (quarticEmpiricalCos N x + 4)) * (2 / δ)) *
          (-(2 * Real.pi * quarticKappa / (N : ℝ)) * scalarSin (x i)) +
      (chiFIN064 ((2 / δ) * (quarticEmpiricalCos N x + 4)) *
        deriv chiFIN064 ((N : ℝ) ^ (1 / 4 : ℝ) * quarticEmpiricalSin N x) *
          (N : ℝ) ^ (1 / 4 : ℝ)) *
            ((2 * Real.pi * (quarticKappa * quarticEta) / (N : ℝ)) * scalarCos (x i)) := by
  let a := 2 / δ
  let b := 8 / δ
  let q := (N : ℝ) ^ (1 / 4 : ℝ)
  have harg : ∀ t : ℝ, a * t + b = (2 / δ) * (t + 4) := by
    intro t
    dsimp only [a, b]
    ring
  have he : quarticRareTest δ N = fun y =>
      gFIN064 a b (quarticEmpiricalCos N y) * gFIN064 q 0 (quarticEmpiricalSin N y) := by
    funext y
    simp only [quarticRareTest, gFIN064, harg, add_zero, q]
  rw [he, PositiveRate.particlePartial_mul
    (isSmooth_comp_FIN064 (quartic_empirical_cos_smooth N) (gFIN064_contDiff a b))
    (isSmooth_comp_FIN064 (quartic_empirical_sin_smooth N) (gFIN064_contDiff q 0)),
    particlePartial_comp_FIN064 (quartic_empirical_cos_smooth N) (gFIN064_contDiff a b),
    particlePartial_comp_FIN064 (quartic_empirical_sin_smooth N) (gFIN064_contDiff q 0),
    deriv_gFIN064, deriv_gFIN064, quartic_empirical_cos_partial, quartic_empirical_sin_partial]
  simp only [gFIN064, harg, add_zero, a, q]
  ring

end DGPS.FiniteN
