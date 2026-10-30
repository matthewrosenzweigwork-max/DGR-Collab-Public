import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorFeedback
import DGPS.Examples.PositiveH1.Transfer

/-! Exact means of the ACTUAL rank-three nonlinear Euler feedbacks. These
identities identify the mass-normalization term without a commutation or
eigenfeature assumption. All probability integrals involve continuous functions. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

def elementaryForceFeedback (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ :=
  kAlpha *
    ((∫ y, elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureC h) y
        ∂(densityMeasure ρ : Measure (Torus 1))) * featureC h x +
      (∫ y, elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureS h) y
        ∂(densityMeasure ρ : Measure (Torus 1))) * featureS h x) -
    kBeta *
      ((∫ y, elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureB h) y
        ∂(densityMeasure ρ : Measure (Torus 1))) * featureB h x)

theorem isSmooth_elementaryForceFeedback (h : ℝ) (ρ : AbsoluteDensity 1) :
    IsSmoothPeriodic (elementaryForceFeedback h ρ) := by
  unfold IsSmoothPeriodic elementaryForceFeedback
  exact (contDiff_const.mul ((contDiff_const.mul (smooth_featureC h)).add
    (contDiff_const.mul (smooth_featureS h)))).sub
      (contDiff_const.mul (contDiff_const.mul (smooth_featureB h)))

/-- The physical derivative of the actual kernel potential. -/
theorem elementaryKprime_three_features (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryKprime h (densityMeasure ρ) x =
      kAlpha * (momC h (densityMeasure ρ) * coordPartial 0 (featureC h) x +
        momS h (densityMeasure ρ) * coordPartial 0 (featureS h) x) -
        kBeta * momB h (densityMeasure ρ) * coordPartial 0 (featureB h) x := by
  have he : elementaryKernelMean h (densityMeasure ρ) = fun y =>
      (kAlpha * momC h (densityMeasure ρ)) * featureC h y +
      (kAlpha * momS h (densityMeasure ρ)) * featureS h y +
      (-kBeta * momB h (densityMeasure ρ)) * featureB h y := by
    funext y
    unfold elementaryKernelMean
    ring
  have hC : IsSmoothPeriodic (fun y => (kAlpha * momC h (densityMeasure ρ)) * featureC h y) :=
    contDiff_const.mul (isSmooth_featureC h)
  have hS : IsSmoothPeriodic (fun y => (kAlpha * momS h (densityMeasure ρ)) * featureS h y) :=
    contDiff_const.mul (isSmooth_featureS h)
  have hB : IsSmoothPeriodic (fun y => (-kBeta * momB h (densityMeasure ρ)) * featureB h y) :=
    contDiff_const.mul (isSmooth_featureB h)
  have hCS : IsSmoothPeriodic (fun y =>
      (kAlpha * momC h (densityMeasure ρ)) * featureC h y +
        (kAlpha * momS h (densityMeasure ρ)) * featureS h y) := hC.add hS
  unfold elementaryKprime
  rw [he, DGPS.Examples.PositiveH1.Transfer.coordPartial_add hCS hB,
    DGPS.Examples.PositiveH1.Transfer.coordPartial_add hC hS,
    DGPS.Examples.PositiveH1.Transfer.coordPartial_const_mul (isSmooth_featureC h),
    DGPS.Examples.PositiveH1.Transfer.coordPartial_const_mul (isSmooth_featureS h),
    DGPS.Examples.PositiveH1.Transfer.coordPartial_const_mul (isSmooth_featureB h)]
  ring

theorem elementaryGeneratorFeedback_mean (h : ℝ) (ρ : AbsoluteDensity 1) :
    (∫ x, elementaryGeneratorFeedback h ρ x ∂(densityMeasure ρ : Measure (Torus 1))) =
      ∫ x, elementaryAK h (densityMeasure ρ) x ∂(densityMeasure ρ : Measure (Torus 1)) := by
  have he : elementaryGeneratorFeedback h ρ = fun x =>
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureC h x +
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureS h x +
      (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureB h x + 0 := by
    funext x
    unfold elementaryGeneratorFeedback
    ring
  have hL : (∫ x, elementaryGeneratorFeedback h ρ x ∂(densityMeasure ρ : Measure (Torus 1))) =
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momC h (densityMeasure ρ) +
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momS h (densityMeasure ρ) +
      (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momB h (densityMeasure ρ) := by
    rw [he, integral_affine3]
    ring
  have hC0 : elementaryC h 0 ρ =
      2 * ∫ x, elementaryGeneratorFeedback h ρ x ∂(densityMeasure ρ : Measure (Torus 1)) := by
    rw [elementaryC_moments, hL]
    ring
  have hDef : elementaryC h 0 ρ =
      2 * ∫ x, elementaryAK h (densityMeasure ρ) x ∂(densityMeasure ρ : Measure (Torus 1)) := by
    unfold elementaryC
    rw [← Structural.budget_integral_densityMeasure]
    ring
  linarith

theorem elementaryC_feedback_mean (h a : ℝ) (ρ : AbsoluteDensity 1) :
    (∫ x, elementaryAK h (densityMeasure ρ) x + elementaryGeneratorFeedback h ρ x -
      a * elementaryKernelMean h (densityMeasure ρ) x
        ∂(densityMeasure ρ : Measure (Torus 1))) = elementaryC h a ρ := by
  have hA := (continuous_elementaryAK h (densityMeasure ρ)).integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hL := (isSmooth_elementaryGeneratorFeedback h ρ).continuous_torus.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hK := (isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_torus.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hAL : Integrable (fun x => elementaryAK h (densityMeasure ρ) x +
      elementaryGeneratorFeedback h ρ x) (densityMeasure ρ : Measure (Torus 1)) := hA.add hL
  rw [integral_sub hAL (hK.const_mul a), integral_add hA hL,
    integral_const_mul, elementaryGeneratorFeedback_mean]
  unfold elementaryC elementaryQ
  rw [← Structural.budget_integral_densityMeasure]
  ring

/-- Symmetry of the genuine force-gradient quadratic expression identifies the
feedback mean with the ACTUAL force-square moment. -/
theorem elementaryForceFeedback_mean (h : ℝ) (ρ : AbsoluteDensity 1) :
    (∫ x, elementaryForceFeedback h ρ x ∂(densityMeasure ρ : Measure (Torus 1))) =
      elementaryJ h ρ := by
  let κ := elementaryKprime h (densityMeasure ρ)
  let gC := coordPartial 0 (featureC h)
  let gS := coordPartial 0 (featureS h)
  let gB := coordPartial 0 (featureB h)
  have hκ := (isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0
  have hC := hκ.mul ((isSmooth_featureC h).continuous_coordPartial 0)
  have hS := hκ.mul ((isSmooth_featureS h).continuous_coordPartial 0)
  have hB := hκ.mul ((isSmooth_featureB h).continuous_coordPartial 0)
  have hiC : Integrable (fun x => κ x * gC x) (densityMeasure ρ : Measure (Torus 1)) :=
    hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (fun x => κ x * gS x) (densityMeasure ρ : Measure (Torus 1)) :=
    hS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiB : Integrable (fun x => κ x * gB x) (densityMeasure ρ : Measure (Torus 1)) :=
    hB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heF : elementaryForceFeedback h ρ = fun x =>
      (kAlpha * ∫ y, κ y * gC y ∂(densityMeasure ρ : Measure (Torus 1))) * featureC h x +
      (kAlpha * ∫ y, κ y * gS y ∂(densityMeasure ρ : Measure (Torus 1))) * featureS h x +
      (-kBeta * ∫ y, κ y * gB y ∂(densityMeasure ρ : Measure (Torus 1))) * featureB h x + 0 := by
    funext x
    dsimp only [elementaryForceFeedback, κ, gC, gS, gB]
    ring
  rw [heF, integral_affine3]
  have heSq : (fun x => κ x ^ 2) = fun x =>
      (kAlpha * momC h (densityMeasure ρ)) * (κ x * gC x) +
      (kAlpha * momS h (densityMeasure ρ)) * (κ x * gS x) +
      (-kBeta * momB h (densityMeasure ρ)) * (κ x * gB x) := by
    funext x
    dsimp only [κ, gC, gS, gB]
    simp_rw [elementaryKprime_three_features h ρ x]
    ring
  have hJ : elementaryJ h ρ =
      (kAlpha * momC h (densityMeasure ρ)) * (∫ x, κ x * gC x ∂(densityMeasure ρ : Measure (Torus 1))) +
      (kAlpha * momS h (densityMeasure ρ)) * (∫ x, κ x * gS x ∂(densityMeasure ρ : Measure (Torus 1))) +
      (-kBeta * momB h (densityMeasure ρ)) * (∫ x, κ x * gB x ∂(densityMeasure ρ : Measure (Torus 1))) := by
    have hiCS : Integrable (fun x =>
        (kAlpha * momC h (densityMeasure ρ)) * (κ x * gC x) +
          (kAlpha * momS h (densityMeasure ρ)) * (κ x * gS x))
        (densityMeasure ρ : Measure (Torus 1)) :=
      (hiC.const_mul _).add (hiS.const_mul _)
    unfold elementaryJ
    rw [← Structural.budget_integral_densityMeasure]
    change (∫ x, κ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) = _
    rw [heSq, integral_add hiCS (hiB.const_mul _),
      integral_add (hiC.const_mul _) (hiS.const_mul _)]
    simp only [integral_const_mul]
  rw [hJ]
  ring

theorem elementaryJ_feedback_mean (h : ℝ) (ρ : AbsoluteDensity 1) :
    (∫ x, (elementaryKprime h (densityMeasure ρ) x) ^ 2 + 2 * elementaryForceFeedback h ρ x
      ∂(densityMeasure ρ : Measure (Torus 1))) = 3 * elementaryJ h ρ := by
  have hκ : Continuous (fun x => (elementaryKprime h (densityMeasure ρ) x) ^ 2) :=
    ((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0).pow 2
  have hL := (isSmooth_elementaryForceFeedback h ρ).continuous_torus
  have hiκ := hκ.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hiL := hL.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  rw [integral_add hiκ (hiL.const_mul 2), integral_const_mul, elementaryForceFeedback_mean]
  have he : (∫ x, (elementaryKprime h (densityMeasure ρ) x) ^ 2
      ∂(densityMeasure ρ : Measure (Torus 1))) = elementaryJ h ρ := by
    unfold elementaryJ
    rw [← Structural.budget_integral_densityMeasure]
  rw [he]
  ring

end DGPS.Examples.ThreeSpeciesCircle
