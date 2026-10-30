import DGPS.Examples.ThreeSpeciesCircle.InteractingGapVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorCentering

/-! The actual first variation of the signed interaction-generator correction.
Both feature moments and generator-feature moments vary with the density. No
eigenfeature or kernel/generator commutation identity is used. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual normalized path has exactly the original observable moments at
zero, including when the stored nonnegative root is irregular on null sets. -/
theorem absoluteRootVariation_moment_zero (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    (g : Torus 1 → ℝ) :
    (∫ x, g x ∂(densityMeasure (absoluteRootVariation ρ hφ 0) : Measure (Torus 1))) =
      ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) := by
  have hn0 : 0 < ∫ x, (ρ.sqrt x + (0 : ℝ) * φ x) ^ 2 ∂haar 1 := by
    simpa only [zero_mul, add_zero, ρ.mass_one] using (one_pos : (0 : ℝ) < 1)
  rw [absoluteRootVariation_moment ρ hφ 0 hn0 g]
  rw [Structural.budget_integral_densityMeasure]
  simp only [zero_mul, add_zero, ρ.mass_one, div_one, AbsoluteDensity.density]

/-- Genuine full-H1 differentiation of the actual signed correction `C(h,a)`.
The physical generator images retain their extra harmonics and are not replaced
by scalar eigenvalues. The changing-force feedback is part of the derivative. -/
theorem absoluteRootVariation_elementaryC_hasDerivAt (h a : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt (fun t : ℝ => elementaryC h a (absoluteRootVariation ρ hφ t))
      (2 * kAlpha *
        (absoluteRootMomentDerivative ρ φ (featureC h) *
            (∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure ρ : Measure (Torus 1))) +
          momC h (densityMeasure ρ) *
            absoluteRootMomentDerivative ρ φ (elementaryFeatureGenerator h (featureC h)) +
          (absoluteRootMomentDerivative ρ φ (featureS h) *
            (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure ρ : Measure (Torus 1))) +
          momS h (densityMeasure ρ) *
            absoluteRootMomentDerivative ρ φ (elementaryFeatureGenerator h (featureS h)))) -
        2 * kBeta *
          (absoluteRootMomentDerivative ρ φ (featureB h) *
            (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure ρ : Measure (Torus 1))) +
          momB h (densityMeasure ρ) *
            absoluteRootMomentDerivative ρ φ (elementaryFeatureGenerator h (featureB h))) -
        a * (2 * kAlpha *
          (momC h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureC h) +
            momS h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureS h)) -
          2 * kBeta * momB h (densityMeasure ρ) *
            absoluteRootMomentDerivative ρ φ (featureB h))) 0 := by
  have hd (g : Torus 1 → ℝ) (hg : Continuous g) :
      HasDerivAt
        (fun t : ℝ => ∫ x, g x ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)))
        (absoluteRootMomentDerivative ρ φ g) 0 :=
    absoluteRootVariation_moment_hasDerivAt ρ hφ g hg
  have hC := hd (featureC h) (isSmooth_featureC h).continuous_torus
  have hS := hd (featureS h) (isSmooth_featureS h).continuous_torus
  have hB := hd (featureB h) (isSmooth_featureB h).continuous_torus
  have hAC := hd (elementaryFeatureGenerator h (featureC h))
    (continuous_elementaryFeatureGenerator h (featureC h) (smooth_featureC h))
  have hAS := hd (elementaryFeatureGenerator h (featureS h))
    (continuous_elementaryFeatureGenerator h (featureS h) (smooth_featureS h))
  have hAB := hd (elementaryFeatureGenerator h (featureB h))
    (continuous_elementaryFeatureGenerator h (featureB h) (smooth_featureB h))
  have hQ := absoluteRootVariation_elementaryQ_hasDerivAt h ρ hφ
  have hpoly := ((((hC.mul hAC).add (hS.mul hAS)).const_mul (2 * kAlpha)).sub
    ((hB.mul hAB).const_mul (2 * kBeta))).sub (hQ.const_mul a)
  convert hpoly using 1
  · funext t
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    rw [elementaryC_moments, elementaryQ_moments]
    simp only [momC, momS, momB] <;> ring
  · simp only [momC, momS, momB]
    simp_rw [absoluteRootVariation_moment_zero]

end DGPS.Examples.ThreeSpeciesCircle
