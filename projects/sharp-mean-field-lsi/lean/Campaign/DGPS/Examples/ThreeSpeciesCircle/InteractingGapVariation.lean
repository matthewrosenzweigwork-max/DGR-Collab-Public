import DGPS.Examples.ThreeSpeciesCircle.InteractingEntropyVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingDeficitExpansion
import DGPS.Variational.SpeciesInclusion

/-! Actual first variations of the finite-rank interaction and scalar gap on
the original absolute H1 carrier. The normalized observable derivative includes
the changing-law covariance term; the force moments are not frozen. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual observable derivative along a normalized square-root variation. -/
def absoluteRootMomentDerivative (ρ : AbsoluteDensity 1) (φ g : Torus 1 → ℝ) : ℝ :=
  2 * (∫ x, ρ.sqrt x * φ x * g x ∂haar 1) -
    (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) *
      ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1))

/-- The actual interaction quadratic form has the genuine finite-three-moment
derivative on every original H1 direction, including roots with zeros. -/
theorem absoluteRootVariation_elementaryQ_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt
      (fun t : ℝ => elementaryQ h (densityMeasure (absoluteRootVariation ρ hφ t)))
      (2 * kAlpha *
          (momC h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureC h) +
            momS h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureS h)) -
        2 * kBeta * momB h (densityMeasure ρ) *
          absoluteRootMomentDerivative ρ φ (featureB h)) 0 := by
  have hC := absoluteRootVariation_moment_hasDerivAt ρ hφ (featureC h)
    (isSmooth_featureC h).continuous_torus
  have hS := absoluteRootVariation_moment_hasDerivAt ρ hφ (featureS h)
    (isSmooth_featureS h).continuous_torus
  have hB := absoluteRootVariation_moment_hasDerivAt ρ hφ (featureB h)
    (isSmooth_featureB h).continuous_torus
  change HasDerivAt (fun t => momC h (densityMeasure (absoluteRootVariation ρ hφ t)))
    (absoluteRootMomentDerivative ρ φ (featureC h)) 0 at hC
  change HasDerivAt (fun t => momS h (densityMeasure (absoluteRootVariation ρ hφ t)))
    (absoluteRootMomentDerivative ρ φ (featureS h)) 0 at hS
  change HasDerivAt (fun t => momB h (densityMeasure (absoluteRootVariation ρ hφ t)))
    (absoluteRootMomentDerivative ρ φ (featureB h)) 0 at hB
  have hQ := (((hC.pow 2).add (hS.pow 2)).const_mul kAlpha).sub
    ((hB.pow 2).const_mul kBeta)
  have hM (g : Torus 1 → ℝ) :
      (∫ x, g x ∂(densityMeasure (absoluteRootVariation ρ hφ 0) : Measure (Torus 1))) =
        ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) := by
    have hn0 : 0 < ∫ x, (ρ.sqrt x + (0 : ℝ) * φ x) ^ 2 ∂haar 1 := by
      simpa only [zero_mul, add_zero, ρ.mass_one] using (one_pos : (0 : ℝ) < 1)
    rw [absoluteRootVariation_moment ρ hφ 0 hn0 g]
    rw [Structural.budget_integral_densityMeasure]
    simp only [zero_mul, add_zero, ρ.mass_one, div_one, AbsoluteDensity.density]
  have hC0 : momC h (densityMeasure (absoluteRootVariation ρ hφ 0)) =
      momC h (densityMeasure ρ) := hM (featureC h)
  have hS0 : momS h (densityMeasure (absoluteRootVariation ρ hφ 0)) =
      momS h (densityMeasure ρ) := hM (featureS h)
  have hB0 : momB h (densityMeasure (absoluteRootVariation ρ hφ 0)) =
      momB h (densityMeasure ρ) := hM (featureB h)
  simp_rw [elementaryQ_moments]
  convert hQ using 1
  rw [hC0, hS0, hB0]
  ring

/-- The actual scalar free-energy gap derivative includes both entropy and
changing finite-rank interaction moments. No Euler equation or smoothness of
the competitor is an input. -/
theorem absoluteRootVariation_scalarGap_hasDerivAt {h ε : ℝ} (hh : 0 < h)
    (hε : 0 < ε) (hεmax : ε < epsMax h) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ) {φ : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt
      (fun t : ℝ => (scalarGap (modelData h ε) (absoluteRootVariation ρ hφ t) : ℝ))
      ((∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) -
        2 * (∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) * ((ordinaryEntropy h ρ).toReal + 1) +
        ε / 2 * (2 * kAlpha *
          (momC h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureC h) +
            momS h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureS h)) -
          2 * kBeta * momB h (densityMeasure ρ) *
            absoluteRootMomentDerivative ρ φ (featureB h))) 0 := by
  have hH := absoluteRootVariation_entropy_hasDerivAt h ρ hpos hφ
  have hQ := absoluteRootVariation_elementaryQ_hasDerivAt h ρ hφ
  have hgap (τ : AbsoluteDensity 1) : (scalarGap (modelData h ε) τ : ℝ) =
      (ordinaryEntropy h τ).toReal + ε / 2 * elementaryQ h (densityMeasure τ) := by
    have hg := elementaryModel_speciesGap_expansion hh hε hεmax (SpeciesFamily.single τ)
    simpa only [speciesGap_single, densityMeasure_barycenter_single, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] using hg
  simp_rw [hgap]
  exact hH.add (hQ.const_mul (ε / 2))

end DGPS.Examples.ThreeSpeciesCircle
