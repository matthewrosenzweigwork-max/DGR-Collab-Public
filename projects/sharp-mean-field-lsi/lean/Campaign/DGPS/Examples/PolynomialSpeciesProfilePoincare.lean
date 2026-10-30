import DGPS.Examples.PolynomialSpeciesAbsoluteProfileJet
import DGPS.Examples.PolynomialProfilePoincareUpper

/-! The actual same-graph scaled absolute profile supplies the C2 jet for the
one-sided native Poincare bound. The unnormalized logarithm and its genuine
normalized probability are retained; no optimizer classification is assumed. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Analysis.PeriodicHolder
open DGPS.Circle.AngularNormalization DGPS.Circle.FirstClusterPerturbation

namespace DGPS.Examples.PolynomialSpecies

private theorem norm_error_gives_angular_jet (F : PeriodicC2_STR02969)
    (ell : AngCircle → ℝ) (h A B K : ℝ) (hh : 0 ≤ h)
    (hlift : ∀ t : ℝ, ell (t : AngCircle) = F.val t)
    (herr : ‖F - polynomialMixedAbsoluteProfile A B h‖ ≤ K * h ^ 3) :
    c2JetError_EX009 ell h (1 + A) B (-(A + A ^ 2 - B ^ 2) / 6) (-B * (1 + A) / 6) K := by
  let Q := polynomialMixedAbsoluteProfile A B h
  let T := F - Q
  have hb0 (t : ℝ) : |T.val t| ≤ ‖T‖ :=
    ((bdd_parts_STR02969 T.isC2).1.abs_le_supNorm t).trans (le_c2Norm_STR02969 T.val).1
  have hb1 (t : ℝ) : |deriv T.val t| ≤ ‖T‖ :=
    ((bdd_parts_STR02969 T.isC2).2.1.abs_le_supNorm t).trans (le_c2Norm_STR02969 T.val).2.1
  have hs2 : supNorm (deriv (deriv T.val)) ≤ ‖T‖ :=
    (le_add_of_nonneg_right (circHolder_nonneg_STR02953 (1 / 2) (deriv (deriv T.val)))).trans
      (le_c2Norm_STR02969 T.val).2.2
  have hb2 (t : ℝ) : |deriv (deriv T.val) t| ≤ ‖T‖ :=
    ((bdd_parts_STR02969 T.isC2).2.2.abs_le_supNorm t).trans hs2
  have hval : T.val = F.val - Q.val := PeriodicC2_STR02969.val_sub F Q
  have hder : deriv T.val = deriv F.val - deriv Q.val := by
    rw [hval]
    exact deriv_sub_fun_STR02969 F.isC2.2.1 Q.isC2.2.1
  have hder2 : deriv (deriv T.val) = deriv (deriv F.val) - deriv (deriv Q.val) := by
    rw [hder]
    exact deriv_sub_fun_STR02969 F.isC2.2.2.1 Q.isC2.2.2.1
  have he : (fun t : ℝ => ell (t : AngCircle)) = F.val := funext hlift
  have hQ : Q.val = harmonicLog_EX009 h (1 + A) B
      (-(A + A ^ 2 - B ^ 2) / 6) (-B * (1 + A) / 6) := by
    funext t
    change (polynomialMixedAbsoluteProfile A B h).val t = _
    rw [polynomialMixedAbsoluteProfile_val]
    unfold harmonicLog_EX009
    ring
  intro t
  rw [he, ← hQ, abs_of_nonneg hh]
  have h0 := (hb0 t).trans herr
  have h1 := (hb1 t).trans herr
  have h2 := (hb2 t).trans herr
  rw [hval] at h0
  rw [hder] at h1
  rw [hder2] at h2
  rw [hlift t]
  exact ⟨h0, h1, h2⟩

/-- The factual SAME-graph C2 jet gives an actual native full-weak-H1 Poincare
upper bound, uniformly on bounded scaled boxes. Smoothness of the supplied
angular profile and its exact normalized probability are factual inputs;
the original-domain minimizer regularity producer supplies them at optimizers.
No Poincare, rate, minimizer, parity or coefficient-classification premise occurs. -/
theorem polynomial_same_graph_profile_poincare_upper
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ A B σ α h : ℝ,
      |A| ≤ M → |B| ≤ M → |σ| ≤ M → |α| ≤ M → 0 ≤ h → h ≤ δ →
      ∀ (P : BoundedPositiveReference 1) (ell : AngCircle → ℝ), IsSmoothAngular ell →
      (∀ t : ℝ, ell (t : AngCircle) =
        (polynomialRangeLogWeight (h, h ^ 4 * σ) +
          polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * A, h * B)).val t) →
      P.density = angularGibbs_EX009 ell →
      poincareRate ⟨P.measure, P.isProbabilityMeasure⟩ ≤
        ENNReal.ofReal (a0 * (1 + h ^ 2 * ((1 + 3 * A + 2 * A ^ 2) / 6)) + a0 * C * h ^ 3) := by
  obtain ⟨δJ, K, hδJ, hK, hJet⟩ := polynomial_range_graph_absolute_profile_remainder
    hU h0U hψ hψ0 hgraph hzero hfirst M hM
  let coeff : (ℝ × ℝ) → Fin 4 → ℝ := fun p =>
    ![1 + p.1, p.2, -(p.1 + p.1 ^ 2 - p.2 ^ 2) / 6, -p.2 * (1 + p.1) / 6]
  let S : Set (Fin 4 → ℝ) := coeff '' (Set.Icc (-M) M ×ˢ Set.Icc (-M) M)
  have hc : Continuous coeff := by unfold coeff; fun_prop
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image hc
  obtain ⟨L, hL, hBox⟩ := compact_coefficient_box_EX009 S hS
  obtain ⟨δP, C, hδP, hC, hPC⟩ := polynomial_profile_poincare_upper hL hK.le
  refine ⟨min δJ δP, C, lt_min hδJ hδP, hC, fun A B σ α h hA hB hσ hα hh hsmall P ell hell hlift hP => ?_⟩
  obtain ⟨_hp, herr⟩ := hJet A B σ α h hA hB hσ hα hh (hsmall.trans (min_le_left _ _))
  have hcoeff : coeff (A, B) ∈ S :=
    ⟨(A, B), ⟨abs_le.mp hA, abs_le.mp hB⟩, rfl⟩
  have hj := norm_error_gives_angular_jet
    (polynomialRangeLogWeight (h, h ^ 4 * σ) +
      polynomialGapLift ψ ((h, h ^ 4 * σ), h ^ 2 * α) (h * A, h * B)) ell h A B K hh hlift herr
  have hspec := hPC (coeff (A, B)) P ell h (hBox _ hcoeff) hell hP
    (by rw [abs_of_nonneg hh]; exact hsmall.trans (min_le_right _ _)) hj
  have he : ((coeff (A, B)) 0 ^ 2 + (coeff (A, B)) 1 ^ 2) / 6 - (coeff (A, B)) 2 =
      (1 + 3 * A + 2 * A ^ 2) / 6 := by
    change ((1 + A) ^ 2 + B ^ 2) / 6 - (-(A + A ^ 2 - B ^ 2) / 6) = _
    ring
  rw [he, abs_of_nonneg hh] at hspec
  exact hspec

end DGPS.Examples.PolynomialSpecies
