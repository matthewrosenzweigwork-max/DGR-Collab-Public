import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Analysis.WeightedRateComparison
import DGPS.Circle.VonMisesSpectrum

/-! A one-sided native Poincare bound for the actual moving polynomial
reference. The full weak-H1 test domain is transported by the proved logarithmic
density comparison. The selected root is used only through its genuine O(h^6)
bound; no differentiability of that selection is required. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments
open DGPS.Circle.VonMisesParity DGPS.Examples.PolynomialEquilibrium
open DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private theorem reference_density (h : ℝ) (x : Torus 1) :
    (polynomialRankOne h).ref.density x = density_EX054 h (root_EX054 h) (angEquiv x) := by
  have hw (y : Torus 1) : Real.exp (-polyPot_EX055 h (root_EX054 h) y) =
      weight_EX054 h (root_EX054 h) (angEquiv y) := by
    simp only [polyPot_EX055, weight_EX054, feature_model_EX054,
      DGPS.Circle.VonMisesSmallField.ex010_angCos, cosT, ThreeSpeciesCircle.cosHarm]
    congr 1
    ring
  have hZ : ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h (root_EX054 h)) =
      partition_EX054 h (root_EX054 h) := by
    unfold ThreeSpeciesCircle.gibbsZ partition_EX054
    simp_rw [hw]
    exact integral_comp_angEquiv _
  change Real.exp (-polyPot_EX055 h (root_EX054 h) x) /
    ThreeSpeciesCircle.gibbsZ (polyPot_EX055 h (root_EX054 h)) = _
  rw [hw, hZ]
  rfl

/-- The actual normalized reference differs from von Mises by logarithmic
oscillation O(h^6), and the native rates compare on their full original domains. -/
theorem polynomial_reference_poincare_comparison :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      ENNReal.ofReal (Real.exp (-C * h ^ 6)) *
          poincareRate ⟨(vmRef h).measure, (vmRef h).isProbabilityMeasure⟩ ≤
        poincareRate ⟨(polynomialRankOne h).ref.measure,
          (polynomialRankOne h).ref.isProbabilityMeasure⟩ := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := logRatio_fixed_Ck_EX054 0
  refine ⟨2 * C, δ, by positivity, hδ, fun h hh => ?_⟩
  have hlog (θ : AngCircle) : |logRatio_EX054 h (root_EX054 h) θ| ≤ C * h ^ 6 := by
    induction θ using Real.Angle.induction_on with
    | _ t =>
      have ht := hb h hh 0 le_rfl t
      simp only [iteratedDeriv_zero] at ht
      convert ht using 1 <;> rfl
  have hosc : ∀ᵐ x ∂haar 1, ∀ᵐ y ∂haar 1,
      Real.log ((polynomialRankOne h).ref.density x / (vmRef h).density x) -
        Real.log ((polynomialRankOne h).ref.density y / (vmRef h).density y) ≤
          2 * C * h ^ 6 := by
    apply Eventually.of_forall
    intro x
    apply Eventually.of_forall
    intro y
    simp only [reference_density, vmRef, vmWeight]
    change logRatio_EX054 h (root_EX054 h) (angEquiv x) -
      logRatio_EX054 h (root_EX054 h) (angEquiv y) ≤ 2 * C * h ^ 6
    have hx := (abs_le.mp (hlog (angEquiv x))).2
    have hy := (abs_le.mp (hlog (angEquiv y))).1
    linarith
  have hc := (DGPS.Examples.ordinary_lsi_bounded_density_comparison
    (vmRef h) (polynomialRankOne h).ref (2 * C * h ^ 6) hosc).2.1.1
  simpa only [neg_mul] using hc

private theorem elementary_lower {t c w : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hct : c * t ≤ 1 / 96)
    (hwt : w * t ^ 2 ≤ 1 / 96) :
    1 + t / 8 ≤ Real.exp (-w * t ^ 3) * (1 + t / 6 - c * t ^ 2) := by
  have he := Real.add_one_le_exp (-w * t ^ 3)
  have hct2 : c * t ^ 2 ≤ t / 96 := by nlinarith [mul_le_mul_of_nonneg_right hct ht]
  have hwt3 : w * t ^ 3 ≤ t / 96 := by nlinarith [mul_le_mul_of_nonneg_right hwt ht]
  have hL : 0 ≤ 1 + t / 6 - c * t ^ 2 := by linarith
  have hLu : 1 + t / 6 - c * t ^ 2 ≤ 7 / 6 := by nlinarith [mul_nonneg hc (sq_nonneg t)]
  calc
    _ ≤ (1 + t / 6 - c * t ^ 2) - (7 / 6) * (w * t ^ 3) := by linarith
    _ ≤ (1 - w * t ^ 3) * (1 + t / 6 - c * t ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hLu (show 0 ≤ w * t ^ 3 by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : 1 - w * t ^ 3 ≤ Real.exp (-w * t ^ 3)) hL

/-- A strict quadratic subrate of the actual reference Poincare rate. The
constant field threshold precedes every signed field. This is a one-sided bound,
not an optimizer Poincare expansion. -/
theorem polynomial_reference_poincare_quadratic_lower :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 / 8)) ≤
        poincareRate ⟨(polynomialRankOne h).ref.measure,
          (polynomialRankOne h).ref.isProbabilityMeasure⟩ := by
  obtain ⟨W, δw, hW, hδw, hcomp⟩ := polynomial_reference_poincare_comparison
  obtain ⟨C, δc, hC, hδc, hspec⟩ := DGPS.Examples.even_small_field_poincare_expansion
  have he : ∀ᶠ h : ℝ in 𝓝 0,
      h ^ 2 ≤ 1 ∧ C * h ^ 2 ≤ 1 / 96 ∧ W * h ^ 4 ≤ 1 / 96 := by
    have h1 : Tendsto (fun h : ℝ => h ^ 2) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun h : ℝ => h ^ 2) := continuous_id.pow 2
      simpa using hc.tendsto (0 : ℝ)
    have h2 : Tendsto (fun h : ℝ => C * h ^ 2) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun h : ℝ => C * h ^ 2) := continuous_const.mul (continuous_id.pow 2)
      simpa using hc.tendsto (0 : ℝ)
    have h3 : Tendsto (fun h : ℝ => W * h ^ 4) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun h : ℝ => W * h ^ 4) := continuous_const.mul (continuous_id.pow 4)
      simpa using hc.tendsto (0 : ℝ)
    filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 96)),
      h3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 96))] with h h1 h2 h3
    exact ⟨h1.le, h2.le, h3.le⟩
  obtain ⟨d, hd, hdb⟩ := Metric.eventually_nhds_iff.1 he
  refine ⟨min δw (min (δc / 2) (d / 2)), lt_min hδw (lt_min (by positivity) (by positivity)), ?_⟩
  intro h hh
  have hhw : |h| ≤ δw := hh.trans (min_le_left _ _)
  have hhc : |h| < δc := lt_of_le_of_lt (hh.trans ((min_le_right _ _).trans (min_le_left _ _))) (by linarith)
  have hhd : dist h 0 < d := by
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt (hh.trans ((min_le_right _ _).trans (min_le_right _ _))) (by linarith)
  obtain ⟨ht, hct, hwt⟩ := hdb hhd
  obtain ⟨lam, hlam, _, _, heq, herr⟩ := hspec h hhc
  have hl : DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 / 6 - C * h ^ 4) ≤ lam := by
    have hl := (abs_le.mp herr).1
    nlinarith
  have he4 : (h ^ 2) ^ 2 = h ^ 4 := by ring
  have he6 : (h ^ 2) ^ 3 = h ^ 6 := by ring
  have hwt' : W * (h ^ 2) ^ 2 ≤ 1 / 96 := by rw [he4]; exact hwt
  have hs := elementary_lower (sq_nonneg h) ht hC.le hW.le hct hwt'
  rw [he4, he6] at hs
  have hreal : DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 / 8) ≤ Real.exp (-W * h ^ 6) * lam := by
    have hs' : DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 / 8) ≤
        Real.exp (-W * h ^ 6) * (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 / 6 - C * h ^ 4)) := by
      convert mul_le_mul_of_nonneg_left hs DGPS.Circle.AngularNormalization.a0_pos.le using 1 <;> ring
    exact hs'.trans (mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le)
  have hc := hcomp h hhw
  rw [heq, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hc
  exact (ENNReal.ofReal_le_ofReal hreal).trans hc

end DGPS.Examples.PolynomialSpecies
