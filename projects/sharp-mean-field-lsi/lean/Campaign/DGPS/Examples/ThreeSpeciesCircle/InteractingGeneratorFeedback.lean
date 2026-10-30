import DGPS.Examples.ThreeSpeciesCircle.InteractingMomentLinearity
import DGPS.Examples.ThreeSpeciesCircle.InteractingCorrectionVariation

/-! The actual rank-three generator feedback in the nonlinear weak Euler
equation. The generator's true extra harmonics remain present. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The genuine changing-law generator feedback, with actual generator moments. -/
def elementaryGeneratorFeedback (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ :=
  kAlpha *
    ((∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureC h x +
      (∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureS h x) -
    kBeta *
      ((∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureB h x)

theorem isSmooth_elementaryGeneratorFeedback (h : ℝ) (ρ : AbsoluteDensity 1) :
    IsSmoothPeriodic (elementaryGeneratorFeedback h ρ) := by
  unfold IsSmoothPeriodic elementaryGeneratorFeedback
  exact (contDiff_const.mul ((contDiff_const.mul (smooth_featureC h)).add
    (contDiff_const.mul (smooth_featureS h)))).sub
      (contDiff_const.mul (contDiff_const.mul (smooth_featureB h)))

private theorem moment_linear3 (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G)
    (a b c : ℝ) (f g k : Torus 1 → ℝ) (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    absoluteRootMomentDerivative ρ φ (fun x => a * f x + b * g x + c * k x) =
      a * absoluteRootMomentDerivative ρ φ f + b * absoluteRootMomentDerivative ρ φ g +
        c * absoluteRootMomentDerivative ρ φ k := by
  rw [absoluteRootMomentDerivative_add ρ hφ
    (f := fun x => a * f x + b * g x) (g := fun x => c * k x)
    ((hf.const_mul a).add (hg.const_mul b)) (hk.const_mul c),
    absoluteRootMomentDerivative_add ρ hφ
      (f := fun x => a * f x) (g := fun x => b * g x) (hf.const_mul a) (hg.const_mul b),
    absoluteRootMomentDerivative_const_mul ρ hφ hf,
    absoluteRootMomentDerivative_const_mul ρ hφ hg,
    absoluteRootMomentDerivative_const_mul ρ hφ hk]

private theorem moment_kernel (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    absoluteRootMomentDerivative ρ φ (elementaryKernelMean h (densityMeasure ρ)) =
      kAlpha * (momC h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureC h) +
        momS h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureS h)) -
      kBeta * momB h (densityMeasure ρ) * absoluteRootMomentDerivative ρ φ (featureB h) := by
  have he : elementaryKernelMean h (densityMeasure ρ) = fun x =>
      (kAlpha * momC h (densityMeasure ρ)) * featureC h x +
      (kAlpha * momS h (densityMeasure ρ)) * featureS h x +
      (-kBeta * momB h (densityMeasure ρ)) * featureB h x := by
    funext x
    unfold elementaryKernelMean
    ring
  rw [he, moment_linear3 ρ hφ _ _ _ _ _ _
    (isSmooth_featureC h).continuous_torus (isSmooth_featureS h).continuous_torus
    (isSmooth_featureB h).continuous_torus]
  ring

private theorem moment_generator (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    absoluteRootMomentDerivative ρ φ (elementaryAK h (densityMeasure ρ)) =
      kAlpha * (momC h (densityMeasure ρ) *
          absoluteRootMomentDerivative ρ φ (elementaryFeatureGenerator h (featureC h)) +
        momS h (densityMeasure ρ) *
          absoluteRootMomentDerivative ρ φ (elementaryFeatureGenerator h (featureS h))) -
      kBeta * momB h (densityMeasure ρ) *
        absoluteRootMomentDerivative ρ φ (elementaryFeatureGenerator h (featureB h)) := by
  have he : elementaryAK h (densityMeasure ρ) = fun x =>
      (kAlpha * momC h (densityMeasure ρ)) * elementaryFeatureGenerator h (featureC h) x +
      (kAlpha * momS h (densityMeasure ρ)) * elementaryFeatureGenerator h (featureS h) x +
      (-kBeta * momB h (densityMeasure ρ)) * elementaryFeatureGenerator h (featureB h) x := by
    funext x
    rw [elementaryAK_moments]
    ring
  rw [he, moment_linear3 ρ hφ _ _ _ _ _ _
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureC h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureS h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureB h))]
  ring

private theorem moment_feedback (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    absoluteRootMomentDerivative ρ φ (elementaryGeneratorFeedback h ρ) =
      kAlpha *
        ((∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure ρ : Measure (Torus 1))) *
            absoluteRootMomentDerivative ρ φ (featureC h) +
          (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure ρ : Measure (Torus 1))) *
            absoluteRootMomentDerivative ρ φ (featureS h)) -
      kBeta *
        (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure ρ : Measure (Torus 1))) *
          absoluteRootMomentDerivative ρ φ (featureB h) := by
  have he : elementaryGeneratorFeedback h ρ = fun x =>
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureC h x +
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureS h x +
      (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureB h x := by
    funext x
    unfold elementaryGeneratorFeedback
    ring
  rw [he, moment_linear3 ρ hφ _ _ _ _ _ _
    (isSmooth_featureC h).continuous_torus (isSmooth_featureS h).continuous_torus
    (isSmooth_featureB h).continuous_torus]
  ring

/-- The actual signed correction has the compact generator-feedback derivative.
It is obtained from the full changing-moment formula, not assumed as Euler data. -/
theorem absoluteRootVariation_elementaryC_feedback_hasDerivAt (h a : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt (fun t : ℝ => elementaryC h a (absoluteRootVariation ρ hφ t))
      (2 * absoluteRootMomentDerivative ρ φ (fun x =>
        elementaryAK h (densityMeasure ρ) x + elementaryGeneratorFeedback h ρ x -
          a * elementaryKernelMean h (densityMeasure ρ) x)) 0 := by
  have hA := continuous_elementaryAK h (densityMeasure ρ)
  have hL := (isSmooth_elementaryGeneratorFeedback h ρ).continuous_torus
  have hK := (isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_torus
  have hd := absoluteRootVariation_elementaryC_hasDerivAt h a ρ hφ
  convert hd using 1
  rw [absoluteRootMomentDerivative_sub ρ hφ
    (f := fun x => elementaryAK h (densityMeasure ρ) x + elementaryGeneratorFeedback h ρ x)
    (g := fun x => a * elementaryKernelMean h (densityMeasure ρ) x) (hA.add hL) (hK.const_mul a),
    absoluteRootMomentDerivative_add ρ hφ hA hL,
    absoluteRootMomentDerivative_const_mul ρ hφ hK,
    moment_generator h ρ hφ, moment_feedback h ρ hφ, moment_kernel h ρ hφ]
  ring

end DGPS.Examples.ThreeSpeciesCircle
