import DGPS.Examples.ThreeSpeciesCircle.GaussianStrictLiftAlgebra
import DGPS.Examples.ThreeSpeciesCircle.GaussianNativeCovariance
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferencePoincareGap

/-! Actual fixed-field strict Gaussian lifting on the entire original native
weak form domain. All covariance coefficients and defect estimates are
discharged from the canonical model; no spectral comparison premise is added. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem reference_rate_pos {h : ℝ} (hh : 0 < h) (hhsmall : |h| ≤ 1 / 1000) :
    0 < poincareRate (refProb hh) := by
  have hs : h ^ 2 < 1 := by
    have ht := (sq_le_sq₀ (abs_nonneg h) (by norm_num : (0 : ℝ) ≤ 1 / 1000)).2 hhsmall
    rw [sq_abs] at ht
    nlinarith only [ht]
  have hl := threefold_reference_poincare_lower h hhsmall
  change ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 * (1 - h ^ 2)) ≤
    poincareRate (refProb hh) at hl
  have hconst : 0 < DGPS.Circle.AngularNormalization.a0 := by
    unfold DGPS.Circle.AngularNormalization.a0
    positivity
  exact (ENNReal.ofReal_pos.2 (mul_pos hconst (sub_pos.2 hs))).trans_le hl

/-- For each actual positive small field, one coupling interval is chosen
before all original native weak tests and before the coercivity proof. -/
theorem elementaryModel_gaussianRate_gt_referencePoincare {h : ℝ} (hh : 0 < h)
    (hhsmall : |h| ≤ 1 / 1000) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh),
        poincareRate (refProb hh) < gaussianRate (modelData h ε) (refProb hh) hH := by
  let μ := refProb hh
  have hPtop := threefold_reference_poincare_ne_top hh
  let P := (poincareRate μ).toReal
  have hP : 0 < P := ENNReal.toReal_pos (reference_rate_pos hh hhsmall).ne' hPtop
  let b := ∫ x, featureB h x ^ 2 ∂(μ : Measure (Torus 1))
  have hb : 0 ≤ b := integral_nonneg fun _ => sq_nonneg _
  let ε0 := min (epsMax h) (a0 / (4 * P * kBeta * (b + 1)))
  have hε0 : 0 < ε0 := lt_min (epsMax_pos h) (by have := kBeta_pos; have := a0_pos; positivity)
  refine ⟨ε0, hε0, min_le_left _ _, ?_⟩
  intro ε hε hε0' hH
  have hεmax : ε < epsMax h := hε0'.trans_le (min_le_left _ _)
  have hsmall : ε * (4 * P * kBeta * (b + 1)) < a0 :=
    (lt_div_iff₀ (by have := kBeta_pos; positivity : 0 < 4 * P * kBeta * (b + 1))).1
      (hε0'.trans_le (min_le_right _ _))
  let A := ε * kAlpha / (1 + ε * kAlpha * (1 / (2 * h ^ 2)))
  let B := ε * kBeta / (1 - ε * kBeta * b)
  have hA : 0 < A := by dsimp [A]; have := kAlpha_pos; positivity
  have hnormB : ‖gaussianReferenceFeature hh 2‖ ^ 2 = b := by
    change ‖lpOf μ (featVec h 2) (continuous_featVec h 2)‖ ^ 2 =
      ∫ x, featVec h 2 x ^ 2 ∂(μ : Measure (Torus 1))
    rw [Structural.norm_sq_eq_integral_sq μ]
    apply integral_congr_ae
    filter_upwards [lpOf_ae μ (featVec h 2) (continuous_featVec h 2)] with x hx
    exact congrArg (fun z : ℝ => z ^ 2) hx
  have hden : (1 / 2 : ℝ) ≤ 1 - ε * kBeta * b := by
    have ht := elementaryModel_feature_denominator_lower hh hε hεmax 2
    rw [hnormB] at ht
    convert ht using 1 <;> simp only [Matrix.cons_val, Matrix.cons_val_zero] <;> ring
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hε.le kBeta_pos.le) (by linarith only [hden])
  have hBupper : B ≤ 2 * ε * kBeta := by
    apply (div_le_iff₀ (by linarith only [hden] : 0 < 1 - ε * kBeta * b)).2
    have hcoef : 0 ≤ 2 * ε * kBeta :=
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε.le) kBeta_pos.le
    have ht := mul_le_mul_of_nonneg_left hden hcoef
    nlinarith only [ht]
  have hpenalty : P * B * b / a0 ≤ 1 / 2 := by
    calc
      _ ≤ P * (2 * ε * kBeta) * b / a0 := by
        apply div_le_div_of_nonneg_right _ a0_pos.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBupper hP.le) hb
      _ ≤ _ := by
        apply (div_le_iff₀ a0_pos).2
        have hpos : 0 ≤ ε * P * kBeta :=
          mul_nonneg (mul_nonneg hε.le hP.le) kBeta_pos.le
        nlinarith only [hsmall, hpos]
  let k := min (a0 / 4) (P * A / (6 * h ^ 2))
  have hk : 0 < k := lt_min (by have := a0_pos; positivity) (by positivity)
  have hRate : ENNReal.ofReal (P + k / 2) ≤ gaussianRate (modelData h ε) μ hH := by
    apply (le_gaussianRate_iff_forall _ _ _ _).2
    intro f hf
    let L := gaussianReferenceMass hh f
    let E := gaussianReferenceRealEnergy hh f
    let X := (∫ x, featureC h x * f.fn x ∂(μ : Measure (Torus 1))) ^ 2 +
      (∫ x, featureS h x * f.fn x ∂(μ : Measure (Torus 1))) ^ 2
    let Z := (∫ x, featureB h x * f.fn x ∂(μ : Measure (Torus 1))) ^ 2
    let d := E - P * L
    let D := gaussianDenominator (modelData h ε) μ hH f hf.1
    have hL : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
    have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have hd : 0 ≤ d := by
      have ht := gaussianReference_poincare_real hh f
      unfold weightedVariance at ht
      rw [hf.1] at ht
      simp only [sub_zero] at ht
      change P * L ≤ E at ht
      exact sub_nonneg.2 ht
    have hmass := gaussianReference_mass_defect_first_moments hh hhsmall f hf.1
    have hthird := gaussianReference_third_moment_defect hh hhsmall f hf.1
    have hD := elementaryModel_native_covariance_formula hh hε hεmax hH f hf.1
    have hnorm : ‖f.toCentered μ hf.1‖ ^ 2 = L := by
      change ‖f.isWeak.memLp.toLp f.fn‖ ^ 2 = _
      rw [Structural.norm_sq_eq_integral_sq μ]
      apply integral_congr_ae
      filter_upwards [f.isWeak.memLp.coeFn_toLp] with x hx
      rw [hx]
    have hDupper : D ≤ 2 * L := by
      have ht := elementaryModel_covariance_form_le_two hh hε hεmax hH (f.toCentered μ hf.1)
      rw [hnorm] at ht
      exact ht
    have hgain := (gaussian_strict_lift_absorption a0 P h A B b L X Z d D
      a0_pos hP hh hA hB hL hX hd hmass hthird hpenalty hD hDupper).2
    change (P + k / 2) * D ≤ d + P * L at hgain
    have hreal : (P + k / 2) * D ≤ E := by dsimp only [d] at hgain; linarith only [hgain]
    rw [gaussianReference_energy_eq_ofReal]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ P + k / 2)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hstrict : poincareRate μ < ENNReal.ofReal (P + k / 2) := by
    rw [← ENNReal.ofReal_toReal hPtop]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by change P < P + k / 2; linarith only [hk])
  exact hstrict.trans_le hRate

end DGPS.Examples.ThreeSpeciesCircle
