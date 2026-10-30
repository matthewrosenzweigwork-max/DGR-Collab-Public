import DGPS.Examples.ThreeSpeciesCircle.GaussianFeatureOperator

/-! The actual inverse Hessian in the C3 feature classes. Orthogonality comes
from the proved reference symmetry, and all inverse coefficients have actual
positive denominators. The generator is not diagonalized here. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem feature_pair_integral {h : ℝ} (hh : 0 < h) (i j : Fin 3) :
    inner ℝ (gaussianReferenceFeature hh i) (gaussianReferenceFeature hh j) =
      ∫ x, featVec h i x * featVec h j x ∂(refProb hh : Measure (Torus 1)) := by
  rw [gaussianReferenceFeature_inner]
  apply integral_congr_ae
  filter_upwards [lpOf_ae (refProb hh) (featVec h j) (continuous_featVec h j)] with x hx
  rw [show ((gaussianReferenceFeature hh j : centeredL2 (refProb hh)) :
    Lp ℝ 2 (refProb hh : Measure (Torus 1))) = lpOf (refProb hh) (featVec h j) (continuous_featVec h j) from rfl,
    hx]

/-- The actual centered feature classes are pairwise orthogonal. -/
theorem gaussianReferenceFeature_orthogonal {h : ℝ} (hh : 0 < h) (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (gaussianReferenceFeature hh i) (gaussianReferenceFeature hh j) = 0 := by
  obtain ⟨_, _, hcs, hbc, hbs⟩ := elementaryReference_feature_gram hh
  rw [feature_pair_integral]
  fin_cases i
  · fin_cases j
    · exact (hij rfl).elim
    · exact hcs
    · change (∫ x, featureC h x * featureB h x ∂(refProb hh : Measure (Torus 1))) = 0
      simpa only [mul_comm] using hbc
  · fin_cases j
    · change (∫ x, featureS h x * featureC h x ∂(refProb hh : Measure (Torus 1))) = 0
      simpa only [mul_comm] using hcs
    · exact (hij rfl).elim
    · change (∫ x, featureS h x * featureB h x ∂(refProb hh : Measure (Torus 1))) = 0
      simpa only [mul_comm] using hbs
  · fin_cases j
    · exact hbc
    · exact hbs
    · exact (hij rfl).elim

/-- The Hessian has an exact action on each elementary Hilbert feature. This is
an interaction-Hessian identity, not a weighted-generator eigenfunction claim. -/
theorem elementaryModel_hessian_feature {h : ℝ} (hh : 0 < h) (ε : ℝ) (i : Fin 3) :
    densityHessian (modelData h ε) (refProb hh) (gaussianReferenceFeature hh i) =
      (1 + ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2) •
        gaussianReferenceFeature hh i := by
  rw [elementaryModel_densityHessian_features]
  have he : (∑ j : Fin 3, (ε * ![kAlpha, kAlpha, -kBeta] j *
      inner ℝ (gaussianReferenceFeature hh j) (gaussianReferenceFeature hh i)) •
      gaussianReferenceFeature hh j) =
      (ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2) •
        gaussianReferenceFeature hh i := by
    rw [Finset.sum_eq_single i]
    · rw [real_inner_self_eq_norm_sq]
    · intro j hj hji
      rw [gaussianReferenceFeature_orthogonal hh j i hji, mul_zero, zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [he]
  conv_lhs => lhs; rw [← one_smul ℝ (gaussianReferenceFeature hh i)]
  rw [← add_smul]

/-- Every inverse feature denominator is genuinely at least one half in the
actual admissible coupling range, including a possible zero feature class. -/
theorem elementaryModel_feature_denominator_lower {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (i : Fin 3) :
    (1 / 2 : ℝ) ≤ 1 + ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2 := by
  by_cases hi : gaussianReferenceFeature hh i = 0
  · norm_num [hi]
  · have hn : 0 < ‖gaussianReferenceFeature hh i‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 hi) 2
    have hl := hessian_half hh hε hεmax (gaussianReferenceFeature hh i)
    rw [elementaryModel_hessian_feature,
      real_inner_smul_right (F := centeredL2 (refProb hh)), real_inner_self_eq_norm_sq] at hl
    nlinarith only [hl, hn]

/-- The actual inverse covariance acts on the same reference feature classes. -/
theorem elementaryModel_covariance_feature {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh)) (i : Fin 3) :
    densityCovariance (modelData h ε) (refProb hh) hH (gaussianReferenceFeature hh i) =
      (1 + ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2)⁻¹ •
        gaussianReferenceFeature hh i := by
  let rateDen := 1 + ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2
  have hden0 : rateDen ≠ 0 := by
    have hl : (1 / 2 : ℝ) ≤ rateDen := elementaryModel_feature_denominator_lower hh hε hεmax i
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hl).ne'
  have hHinv : densityHessian (modelData h ε) (refProb hh)
      (rateDen⁻¹ • gaussianReferenceFeature hh i) = gaussianReferenceFeature hh i := by
    rw [map_smul, elementaryModel_hessian_feature, smul_smul]
    change (rateDen⁻¹ * rateDen) • gaussianReferenceFeature hh i = _
    rw [inv_mul_cancel₀ hden0, one_smul]
  calc
    _ = densityCovariance (modelData h ε) (refProb hh) hH
        (densityHessian (modelData h ε) (refProb hh) (rateDen⁻¹ • gaussianReferenceFeature hh i)) :=
      congrArg (densityCovariance (modelData h ε) (refProb hh) hH) hHinv.symm
    _ = _ := densityCovariance_densityHessian _ _ hH _

/-- Exact signed finite-rank correction to the actual inverse covariance form.
The positive C/S and negative B contributions remain separate from the generator. -/
theorem elementaryModel_covariance_feature_formula {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh))
    (f : centeredL2 (refProb hh)) :
    inner ℝ f (densityCovariance (modelData h ε) (refProb hh) hH f) = ‖f‖ ^ 2 -
      ∑ i : Fin 3, (ε * ![kAlpha, kAlpha, -kBeta] i /
        (1 + ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2)) *
          (inner ℝ (gaussianReferenceFeature hh i) f) ^ 2 := by
  let C := densityCovariance (modelData h ε) (refProb hh) hH
  have hcoord (i : Fin 3) : inner ℝ (gaussianReferenceFeature hh i) (C f) =
      (1 + ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2)⁻¹ *
        inner ℝ (gaussianReferenceFeature hh i) f := by
    rw [← densityCovariance_symmetric, elementaryModel_covariance_feature hh hε hεmax hH i,
      real_inner_smul_left (F := centeredL2 (refProb hh))]
  have he := elementaryModel_densityHessian_features hh ε (C f)
  rw [show densityHessian (modelData h ε) (refProb hh) (C f) = f from
    densityHessian_densityCovariance _ _ hH f] at he
  have hi := congrArg (fun z : centeredL2 (refProb hh) => inner ℝ f z) he
  simp only [inner_add_right, inner_sum,
    real_inner_smul_right (F := centeredL2 (refProb hh)), real_inner_self_eq_norm_sq] at hi
  have hsum : (∑ i : Fin 3, (ε * ![kAlpha, kAlpha, -kBeta] i *
      inner ℝ (gaussianReferenceFeature hh i) (C f)) * inner ℝ f (gaussianReferenceFeature hh i)) =
      ∑ i : Fin 3, (ε * ![kAlpha, kAlpha, -kBeta] i /
        (1 + ε * ![kAlpha, kAlpha, -kBeta] i * ‖gaussianReferenceFeature hh i‖ ^ 2)) *
          (inner ℝ (gaussianReferenceFeature hh i) f) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord, real_inner_comm f (gaussianReferenceFeature hh i), div_eq_mul_inv]
    ring
  rw [hsum] at hi
  linarith only [hi]

end DGPS.Examples.ThreeSpeciesCircle
