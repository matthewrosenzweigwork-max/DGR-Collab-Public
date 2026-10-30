import DGPS.Examples.PolynomialSpeciesRadialBootstrap
import DGPS.Examples.PolynomialSpeciesAbsoluteProfileJet

/-! Actual every-minimizer parameter normalization on ONE retained graph.
The radial producers give amplitude/rate scales; the selected-root bound gives
an independent fixed tilt box. The resulting absolute-logarithm jet retains
the original density. No optimizer classification is assumed. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

/-- Every original scalar minimizer has a bounded scaled-parameter description
and the genuine SAME-graph absolute-profile jet. Constants precede the field,
drift and every original H1 minimizer. Box entry and scales are proved by their
actual producers; neither is a hypothesis. -/
theorem polynomial_scalarMinimizer_absolute_profile_jet
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (henv : ∀ a b h γ : ℝ,
      ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h (a0 * (1 + τ))
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
        (-2 * a0 * polynomialChartGap h
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ) :
    ∃ δ M K : ℝ, 0 < δ ∧ 1 ≤ M ∧ 0 < K ∧
      ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∃ A B σ α : ℝ, |A| ≤ M ∧ |B| ≤ M ∧ |σ| ≤ M ∧ |α| ≤ M ∧
        h ^ 4 * σ = root_EX054 h ∧
        h ^ 2 * α = (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1 ∧
        ((h * A, h * B, (h, h ^ 4 * σ), h ^ 2 * α) : PolynomialRangeParameters) ∈ U ∧
        ρ.density =ᵐ[haar 1]
          (polynomialChartAbsolute h
            (polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * A, h * B))).density ∧
        ‖polynomialRangeLogWeight (h, h ^ 4 * σ) +
            polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * A, h * B) -
          polynomialMixedAbsoluteProfile A B h‖ ≤ K * h ^ 3 := by
  obtain ⟨δS, M0, hδS, hM0, hscale⟩ := polynomial_scalarMinimizer_same_graph_scale
    hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  obtain ⟨Cs, δs, hCs, hδs, hroot⟩ := abs_root_le_sixth_EX054
  let M := M0 + Cs + 1
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hM0M : M0 ≤ M := by dsimp only [M]; linarith
  have hCsM : Cs ≤ M := by dsimp only [M]; linarith
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := hzero 0 0 0 h0U
  have hgraph0 : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0 :=
    fun p hp => (hgraph p hp (ψ p) (hψN p hp)).2 rfl
  obtain ⟨δJ, K, hδJ, hK, hjet⟩ := polynomial_range_graph_absolute_profile_remainder
    hU h0U hψ hψ0 hgraph0 hzero hamp M hM
  let δ := min δS (min δs (min δJ 1))
  have hδ : 0 < δ := lt_min hδS (lt_min hδs (lt_min hδJ zero_lt_one))
  refine ⟨δ, M, K, hδ, hM, hK, fun h hh hsmall b ρ hG hmin => ?_⟩
  have hhS : h < δS := hsmall.trans_le (min_le_left _ _)
  have hhs : h ≤ δs := hsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhJ : h ≤ δJ := hsmall.le.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hh1 : h ≤ 1 := hsmall.le.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨x, hp, hρ, hR, hγ⟩ := hscale h hh hhS b ρ hG hmin
  let γ := (scalarRate (canonical_elementary_polynomial_model h) b).toReal / a0 - 1
  change |γ| ≤ M0 * h ^ 2 at hγ
  let A := x.1 / h
  let B := x.2 / h
  let σ := root_EX054 h / h ^ 4
  let α := γ / h ^ 2
  have hR2 : (Real.sqrt (x.1 ^ 2 + x.2 ^ 2)) ^ 2 = x.1 ^ 2 + x.2 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hx1 : |x.1| ≤ Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, hR2]
    nlinarith only [sq_nonneg x.2]
  have hx2 : |x.2| ≤ Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, hR2]
    nlinarith only [sq_nonneg x.1]
  have hA : |A| ≤ M := by
    dsimp only [A]
    rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).2
    exact (hx1.trans hR).trans (mul_le_mul_of_nonneg_right hM0M hh.le)
  have hB : |B| ≤ M := by
    dsimp only [B]
    rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).2
    exact (hx2.trans hR).trans (mul_le_mul_of_nonneg_right hM0M hh.le)
  have hα : |α| ≤ M := by
    dsimp only [α]
    rw [abs_div, abs_of_pos (pow_pos hh 2)]
    exact (div_le_iff₀ (pow_pos hh 2)).2
      (hγ.trans (mul_le_mul_of_nonneg_right hM0M (sq_nonneg h)))
  have hs := hroot h (by rw [abs_of_pos hh]; exact hhs)
  have h2 : h ^ 2 ≤ 1 := by
    nlinarith only [hh1, mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have h64 : h ^ 6 ≤ h ^ 4 := by
    have he := mul_le_mul_of_nonneg_right h2 (pow_nonneg hh.le 4)
    nlinarith only [he]
  have hσ : |σ| ≤ M := by
    dsimp only [σ]
    rw [abs_div, abs_of_pos (pow_pos hh 4)]
    apply (div_le_iff₀ (pow_pos hh 4)).2
    exact (hs.trans (mul_le_mul_of_nonneg_left h64 hCs.le)).trans
      (mul_le_mul_of_nonneg_right hCsM (pow_nonneg hh.le 4))
  have hAeq : h * A = x.1 := by dsimp only [A]; field_simp [hh.ne']
  have hBeq : h * B = x.2 := by dsimp only [B]; field_simp [hh.ne']
  have hσeq : h ^ 4 * σ = root_EX054 h := by dsimp only [σ]; field_simp [hh.ne']
  have hαeq : h ^ 2 * α = γ := by dsimp only [α]; field_simp [hh.ne']
  obtain ⟨hpJ, herr⟩ := hjet A B σ α h hA hB hσ hα hh.le hhJ
  refine ⟨A, B, σ, α, hA, hB, hσ, hα, hσeq, hαeq, hpJ, ?_, herr⟩
  rw [hAeq, hBeq, hσeq, hαeq]
  exact hρ

end DGPS.Examples.PolynomialSpecies
