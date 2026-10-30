import DGPS.Examples.PolynomialLogDerivativeBounds
import DGPS.Examples.PolynomialFeatureDerivativeBounds

/-! Actual uniform physical generator derivative bounds for the polynomial
feature. The product rule is applied to the actual generator, preserving the
moving-reference logarithmic drift. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.PositiveRankOne

namespace DGPS.Examples.PolynomialSpecies

/-- The true generator derivative includes both changing log-score terms. -/
theorem polynomial_generator_derivative (h : ℝ) (x : Torus 1) :
    coordPartial 0 (polynomialRankOne h).Aq x =
      -coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x -
        coordPartial 0 (polynomialRankOne h).dlogq x * (polynomialRankOne h).dφ x -
          (polynomialRankOne h).dlogq x * coordPartial 0 (polynomialRankOne h).dφ x := by
  let M := polynomialRankOne h
  have hs : IsSmoothPeriodic M.dlogq := M.log_smooth.isSmoothPeriodic_coordPartial 0
  have hdd := M.dφ_smooth.isSmoothPeriodic_coordPartial 0
  have he : M.Aq = fun y => (-1 : ℝ) * coordPartial 0 M.dφ y +
      (-1 : ℝ) * (M.dlogq y * M.dφ y) + 0 := by
    funext y
    change -coordPartial 0 M.dφ y - M.dlogq y * M.dφ y = _
    ring
  rw [he, RankOneModel.coordPartial_lin hdd (hs.mul M.dφ_smooth),
    coordPartial_mul hs M.dφ_smooth]
  ring

/-- A common genuine field interval and constant bound the actual physical
spatial derivative of the generator feature before every point. -/
theorem polynomial_uniform_generator_derivative_bound :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ h : ℝ, |h| ≤ δ → ∀ x : Torus 1,
      |coordPartial 0 (polynomialRankOne h).Aq x| ≤ K := by
  obtain ⟨ε, hε, hlog⟩ := polynomial_log_score_second_derivatives_at_origin
  obtain ⟨K, hK, hfeature⟩ := polynomial_uniform_feature_derivative_bound
  have he : ∀ᶠ h : ℝ in 𝓝 0, ε h ≤ 1 := hε.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨a, ha, hab⟩ := Metric.eventually_nhds_iff.1 he
  let δ := min 1 (a / 2)
  refine ⟨3 * K, δ, by positivity, lt_min one_pos (half_pos ha), min_le_left _ _, fun h hh x => ?_⟩
  have hεh : ε h ≤ 1 := hab (by
    rw [Real.dist_eq, sub_zero]
    exact hh.trans_lt ((min_le_right _ _).trans_lt (by linarith)))
  have hσ := hlog h x
  have h0 : |(polynomialRankOne h).dlogq x| ≤ 1 := by
    nlinarith [abs_nonneg (coordPartial 0 (polynomialRankOne h).dlogq x),
      abs_nonneg (coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dlogq y) x)]
  have h1 : |coordPartial 0 (polynomialRankOne h).dlogq x| ≤ 1 := by
    nlinarith [abs_nonneg ((polynomialRankOne h).dlogq x),
      abs_nonneg (coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dlogq y) x)]
  have hf := hfeature h (hh.trans (min_le_left _ _)) x
  have hf0 : |(polynomialRankOne h).dφ x| ≤ K := by
    nlinarith [abs_nonneg (coordPartial 0 (polynomialRankOne h).dφ x),
      abs_nonneg (coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x)]
  have hf1 : |coordPartial 0 (polynomialRankOne h).dφ x| ≤ K := by
    nlinarith [abs_nonneg ((polynomialRankOne h).dφ x),
      abs_nonneg (coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x)]
  have hf2 : |coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x| ≤ K := by
    nlinarith [abs_nonneg ((polynomialRankOne h).dφ x), abs_nonneg (coordPartial 0 (polynomialRankOne h).dφ x)]
  rw [polynomial_generator_derivative]
  calc
    _ ≤ |coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x| +
        |coordPartial 0 (polynomialRankOne h).dlogq x * (polynomialRankOne h).dφ x| +
        |(polynomialRankOne h).dlogq x * coordPartial 0 (polynomialRankOne h).dφ x| := by
      have hi := norm_sub_le
        (-coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x -
          coordPartial 0 (polynomialRankOne h).dlogq x * (polynomialRankOne h).dφ x)
        ((polynomialRankOne h).dlogq x * coordPartial 0 (polynomialRankOne h).dφ x)
      have hj := norm_sub_le
        (-coordPartial 0 (fun y => coordPartial 0 (polynomialRankOne h).dφ y) x)
        (coordPartial 0 (polynomialRankOne h).dlogq x * (polynomialRankOne h).dφ x)
      simp only [Real.norm_eq_abs] at hi hj
      rw [abs_neg] at hj
      linarith
    _ ≤ K + 1 * K + 1 * K := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add hf2 (mul_le_mul h1 hf0 (abs_nonneg _) zero_le_one))
        (mul_le_mul h0 hf1 (abs_nonneg _) zero_le_one)
    _ = 3 * K := by ring

end DGPS.Examples.PolynomialSpecies
