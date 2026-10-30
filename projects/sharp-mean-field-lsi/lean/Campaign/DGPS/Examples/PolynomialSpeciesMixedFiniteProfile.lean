import DGPS.Examples.PolynomialSpeciesReducedGap
import DGPS.Examples.PolynomialSpeciesRangeGraphScaledTaylor
import DGPS.Examples.PolynomialSpeciesFiniteProfileCanonical

/-! Concrete finite Fourier profile from the actual mixed graph second jet,
and its quantitative relation to the SAME graph's original C2 chart. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Relative finite profile; the second-derivative correction has factor one
half. The absolute unnormalized profile additionally contains the reference. -/
def polynomialMixedFiniteProfile (a b h : ℝ) : PeriodicC2_STR02969 :=
  (h * a) • cosC2_STR02915 + (h * b) • sinC2_STR02915 +
    (h ^ 2 / 2) • (polynomialOriginMixedSecondCorrection a b : PeriodicC2_STR02969)

theorem polynomialMixedFiniteProfile_val (a b h t : ℝ) :
    (polynomialMixedFiniteProfile a b h).val t =
      uFun_STR02945 a b (-(a + a ^ 2 - b ^ 2) / 6) (-(b * (1 + a)) / 6) 0 0 h t := by
  simp only [polynomialMixedFiniteProfile, PeriodicC2_STR02969.val_add,
    PeriodicC2_STR02969.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cosC2_val_STR02915, sinC2_val_STR02915, polynomialOriginMixedSecondCorrection_val]
  unfold uFun_STR02945 pFun_STR02945 qFun_STR02945
  ring

/-- Exact actual finite-profile information with the genuine physical Fisher
normalization. This does not replace the nonlocal part by an eigenformula. -/
theorem polynomialMixedFiniteProfile_information (a b h : ℝ) :
    eulerFisher (e0_STR02955 (polynomialRangeLogWeight (h, 0)))
        (polynomialMixedFiniteProfile a b h) =
      DGPS.Circle.AngularNormalization.a0 * polynomialFiniteProfileFisher a b
        (-(a + a ^ 2 - b ^ 2) / 6) (-(b * (1 + a)) / 6) h ∧
    eulerEntropy (e0_STR02955 (polynomialRangeLogWeight (h, 0)))
        (polynomialMixedFiniteProfile a b h) =
      polynomialFiniteProfileEntropy a b (-(a + a ^ 2 - b ^ 2) / 6)
        (-(b * (1 + a)) / 6) h :=
  polynomialFiniteProfile_core_information _ _ _ _ _ _ (polynomialMixedFiniteProfile_val a b h)

/-- The original same-graph C2 chart is uniformly approximated by this
concrete finite profile, including bounded independent tilt and rate scales. -/
theorem polynomial_range_graph_scaled_profile_remainder
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
        ‖polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b) -
          polynomialMixedFiniteProfile a b h‖ ≤ K * h ^ 3 := by
  obtain ⟨δ, K, hδ, hK, hbound⟩ := polynomial_range_graph_scaled_mixed_remainder
    hU h0U hψ hψ0 hgraph hzero hfirst M hM
  refine ⟨δ, K, hδ, hK, fun a b σ α h ha hb hσ hα hh hhδ => ?_⟩
  obtain ⟨hp, he⟩ := hbound a b σ α h ha hb hσ hα hh hhδ
  refine ⟨hp, ?_⟩
  have hd : polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * a, h * b) -
      polynomialMixedFiniteProfile a b h =
      (ψ (h * a, h * b, (h, h ^ 4 * σ), h ^ 2 * α) : PeriodicC2_STR02969) -
        (h ^ 2 / 2) • (polynomialOriginMixedSecondCorrection a b : PeriodicC2_STR02969) := by
    unfold polynomialGapLift polynomialGapSlice polynomialMixedFiniteProfile
    abel
  rw [hd]
  exact he

end DGPS.Examples.PolynomialSpecies
