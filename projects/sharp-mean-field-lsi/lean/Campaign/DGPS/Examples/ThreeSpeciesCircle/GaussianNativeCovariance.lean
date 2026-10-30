import DGPS.Examples.ThreeSpeciesCircle.GaussianFeatureCovariance
import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceDefect

/-! The actual signed inverse-Hessian denominator on every original centered
native weak test. Interaction-feature coordinates are kept separate from the
reference generator. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Exact original native denominator, with positive C/S and negative B
interaction-Hessian coefficients. No form-domain restriction is introduced. -/
theorem elementaryModel_native_covariance_formula {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh))
    (f : WeakH1Test (refProb hh))
    (hf : (∫ x, f.fn x ∂(refProb hh : Measure (Torus 1))) = 0) :
    gaussianDenominator (modelData h ε) (refProb hh) hH f hf =
      gaussianReferenceMass hh f -
        (ε * kAlpha / (1 + ε * kAlpha * (1 / (2 * h ^ 2)))) *
          ((∫ x, featureC h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2 +
            (∫ x, featureS h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2) +
        (ε * kBeta / (1 - ε * kBeta * ∫ x, featureB h x ^ 2 ∂(refProb hh : Measure (Torus 1)))) *
          (∫ x, featureB h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2 := by
  let μ := refProb hh
  let F := f.toCentered μ hf
  have hcoord (i : Fin 3) : inner ℝ (gaussianReferenceFeature hh i) F =
      ∫ x, featVec h i x * f.fn x ∂(μ : Measure (Torus 1)) := by
    rw [gaussianReferenceFeature_inner]
    apply integral_congr_ae
    filter_upwards [f.isWeak.memLp.coeFn_toLp] with x hx
    change featVec h i x * (f.isWeak.memLp.toLp f.fn) x = _
    rw [hx]
  have hnorm : ‖F‖ ^ 2 = gaussianReferenceMass hh f := by
    change ‖f.isWeak.memLp.toLp f.fn‖ ^ 2 = _
    rw [Structural.norm_sq_eq_integral_sq μ]
    apply integral_congr_ae
    filter_upwards [f.isWeak.memLp.coeFn_toLp] with x hx
    rw [hx]
  have henorm (i : Fin 3) : ‖gaussianReferenceFeature hh i‖ ^ 2 =
      ∫ x, featVec h i x ^ 2 ∂(μ : Measure (Torus 1)) := by
    change ‖lpOf μ (featVec h i) (continuous_featVec h i)‖ ^ 2 = _
    rw [Structural.norm_sq_eq_integral_sq μ]
    apply integral_congr_ae
    filter_upwards [lpOf_ae μ (featVec h i) (continuous_featVec h i)] with x hx
    rw [hx]
  have he := elementaryModel_covariance_feature_formula hh hε hεmax hH F
  rw [hnorm, Fin.sum_univ_three, hcoord 0, hcoord 1, hcoord 2,
    henorm 0, henorm 1, henorm 2] at he
  obtain ⟨hc, hs, _, _, _⟩ := elementaryReference_feature_gram hh
  simp only [featVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at he
  rw [hc, hs] at he
  change gaussianDenominator (modelData h ε) μ hH f hf = _ at he
  rw [he]
  ring

end DGPS.Examples.ThreeSpeciesCircle
