import DGPS.Examples.PolynomialSpeciesMixedFiniteProfile

/-! The true UNNORMALIZED absolute log-profile on the same graph. Reference
tilt is retained in the error, rather than discarded as a density constant. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

def polynomialMixedAbsoluteProfile (a b h : ℝ) : PeriodicC2_STR02969 :=
  h • cosC2_STR02915 + polynomialMixedFiniteProfile a b h

theorem polynomialMixedAbsoluteProfile_val (a b h t : ℝ) :
    (polynomialMixedAbsoluteProfile a b h).val t =
      h * ((1 + a) * Real.cos t + b * Real.sin t) +
        h ^ 2 * (-(a + a ^ 2 - b ^ 2) / 6 * Real.cos (2 * t) -
          b * (1 + a) / 6 * Real.sin (2 * t)) := by
  simp only [polynomialMixedAbsoluteProfile, PeriodicC2_STR02969.val_add,
    PeriodicC2_STR02969.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cosC2_val_STR02915, polynomialMixedFiniteProfile_val]
  unfold uFun_STR02945 pFun_STR02945 qFun_STR02945
  ring

private theorem baseFeature_eq (h : ℝ) :
    polynomialRangeBaseFeature h = polynomialRangeBaseFeature 0 - (h / 3) • cosC2_STR02915 := by
  apply Subtype.ext
  funext t
  change (polynomialRangeBaseFeature h).val t = (polynomialRangeBaseFeature 0 - (h / 3) • cosC2_STR02915).val t
  simp only [polynomialRangeBaseFeature_val_explicit, PeriodicC2_STR02969.val_sub,
    PeriodicC2_STR02969.val_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    cosC2_val_STR02915, zero_div, zero_mul, sub_zero]

private theorem logWeight_eq (h s : ℝ) :
    polynomialRangeLogWeight (h, s) = h • cosC2_STR02915 - s • polynomialRangeBaseFeature h := by
  apply Subtype.ext
  funext t
  change (polynomialRangeLogWeight (h, s)).val t = (h • cosC2_STR02915 - s • polynomialRangeBaseFeature h).val t
  simp only [polynomialRangeLogWeight_val_explicit, polynomialRangeBaseFeature_val_explicit,
    PeriodicC2_STR02969.val_sub, PeriodicC2_STR02969.val_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, cosC2_val_STR02915]

/-- A genuine full C2 Holder jet of the unnormalized absolute logarithm.
The rate/tilt coordinates remain independent. This is factual graph data for
the profile Poincare bound, not a Poincare or optimizer conclusion. -/
theorem polynomial_range_graph_absolute_profile_remainder
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ a b σ α h : ℝ, |a| ≤ M → |b| ≤ M → |σ| ≤ M → |α| ≤ M →
        0 ≤ h → h ≤ δ →
        ((h * a, h * b, (h, h ^ 4 * σ), h ^ 2 * α) : PolynomialRangeParameters) ∈ U ∧
        ‖polynomialRangeLogWeight (h, h ^ 4 * σ) +
            polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b) -
          polynomialMixedAbsoluteProfile a b h‖ ≤ K * h ^ 3 := by
  obtain ⟨δ, K, hδ, hK, hbound⟩ := polynomial_range_graph_scaled_profile_remainder
    hU h0U hψ hψ0 hgraph hzero hfirst M hM
  let C := ‖polynomialRangeBaseFeature 0‖ + ‖cosC2_STR02915‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨min δ 1, K + M * C, lt_min hδ zero_lt_one, add_pos hK (mul_pos hMp hC), ?_⟩
  intro a b σ α h ha hb hσ hα hh hhδ
  have hh1 : h ≤ 1 := hhδ.trans (min_le_right _ _)
  obtain ⟨hp, he⟩ := hbound a b σ α h ha hb hσ hα hh (hhδ.trans (min_le_left _ _))
  have hbnd : ‖polynomialRangeBaseFeature h‖ ≤ C := by
    rw [baseFeature_eq]
    calc
      _ ≤ ‖polynomialRangeBaseFeature 0‖ + ‖(h / 3) • cosC2_STR02915‖ := norm_sub_le _ _
      _ ≤ ‖polynomialRangeBaseFeature 0‖ + ‖cosC2_STR02915‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hh]
        have hd : h / |(3 : ℝ)| ≤ 1 := by norm_num; linarith
        exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) hd)
      _ ≤ C := by dsimp [C]; linarith
  have h4 : h ^ 4 ≤ h ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hh 3) (sub_nonneg.mpr hh1)]
  have hlog : ‖polynomialRangeLogWeight (h, h ^ 4 * σ) - h • cosC2_STR02915‖ ≤
      M * C * h ^ 3 := by
    rw [logWeight_eq]
    have heq : h • cosC2_STR02915 - (h ^ 4 * σ) • polynomialRangeBaseFeature h -
        h • cosC2_STR02915 = -((h ^ 4 * σ) • polynomialRangeBaseFeature h) := by abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hh]
    calc
      _ ≤ (h ^ 4 * M) * C := mul_le_mul (mul_le_mul_of_nonneg_left hσ (pow_nonneg hh 4))
        hbnd (norm_nonneg _) (by positivity)
      _ ≤ (h ^ 3 * M) * C := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h4 hMp.le) hC.le
      _ = _ := by ring
  refine ⟨hp, ?_⟩
  have heq : polynomialRangeLogWeight (h, h ^ 4 * σ) +
        polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b) -
        polynomialMixedAbsoluteProfile a b h =
      (polynomialRangeLogWeight (h, h ^ 4 * σ) - h • cosC2_STR02915) +
        (polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b) -
          polynomialMixedFiniteProfile a b h) := by
    unfold polynomialMixedAbsoluteProfile
    abel
  rw [heq]
  calc
    _ ≤ ‖polynomialRangeLogWeight (h, h ^ 4 * σ) - h • cosC2_STR02915‖ +
        ‖polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b) -
          polynomialMixedFiniteProfile a b h‖ := norm_add_le _ _
    _ ≤ M * C * h ^ 3 + K * h ^ 3 := add_le_add hlog he
    _ = _ := by ring

end DGPS.Examples.PolynomialSpecies
