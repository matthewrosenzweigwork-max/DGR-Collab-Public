import DGPS.Examples.ThreeSpeciesCircle.InteractingKernelRotation

/-! Covariance of both genuine changing-law feedbacks and the actual weak Euler
correction. Integral representations preserve the true kernel derivatives; no
commutation with a feature projection or assumed eigenrelation is used. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029 DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem integral_linear3 (ν : ProbabilityMeasure (Torus 1)) (f g k : Torus 1 → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) (a b c : ℝ) :
    (∫ x, a * f x + b * g x + c * k x ∂(ν : Measure (Torus 1))) =
      a * (∫ x, f x ∂(ν : Measure (Torus 1))) +
        b * (∫ x, g x ∂(ν : Measure (Torus 1))) + c * (∫ x, k x ∂(ν : Measure (Torus 1))) := by
  have hi (f : Torus 1 → ℝ) (hf : Continuous f) : Integrable f (ν : Measure (Torus 1)) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_add (f := fun x => a * f x + b * g x) (g := fun x => c * k x) (((hi f hf).const_mul a).add ((hi g hg).const_mul b)) ((hi k hk).const_mul c),
    integral_add (f := fun x => a * f x) (g := fun x => b * g x) ((hi f hf).const_mul a) ((hi g hg).const_mul b),
    integral_const_mul, integral_const_mul, integral_const_mul]

private theorem kernel_row (h : ℝ) (x : Torus 1) :
    (fun y => kernelK h x y) = fun y =>
      (kAlpha * featureC h x) * featureC h y + (kAlpha * featureS h x) * featureS h y +
        (-kBeta * featureB h x) * featureB h y := by
  funext y
  unfold kernelK
  ring

private theorem kernel_generator_row (h : ℝ) (x y : Torus 1) :
    elementaryFeatureGenerator h (fun z => kernelK h x z) y =
      (kAlpha * featureC h x) * elementaryFeatureGenerator h (featureC h) y +
        (kAlpha * featureS h x) * elementaryFeatureGenerator h (featureS h) y +
          (-kBeta * featureB h x) * elementaryFeatureGenerator h (featureB h) y := by
  rw [kernel_row]
  exact elementaryFeatureGenerator_linear3 h _ _ _
    (isSmooth_featureC h) (isSmooth_featureS h) (isSmooth_featureB h) _ _ _ _

private theorem kernel_derivative_row (h : ℝ) (x y : Torus 1) :
    coordPartial 0 (fun z => kernelK h x z) y =
      (kAlpha * featureC h x) * coordPartial 0 (featureC h) y +
        (kAlpha * featureS h x) * coordPartial 0 (featureS h) y +
          (-kBeta * featureB h x) * coordPartial 0 (featureB h) y := by
  rw [kernel_row]
  have hC : IsSmoothPeriodic (fun z => (kAlpha * featureC h x) * featureC h z) :=
    contDiff_const.mul (isSmooth_featureC h)
  have hS : IsSmoothPeriodic (fun z => (kAlpha * featureS h x) * featureS h z) :=
    contDiff_const.mul (isSmooth_featureS h)
  have hB : IsSmoothPeriodic (fun z => (-kBeta * featureB h x) * featureB h z) :=
    contDiff_const.mul (isSmooth_featureB h)
  have hCS : IsSmoothPeriodic (fun z => (kAlpha * featureC h x) * featureC h z + (kAlpha * featureS h x) * featureS h z) := hC.add hS
  rw [DGPS.Examples.PositiveH1.Transfer.coordPartial_add hCS hB,
    DGPS.Examples.PositiveH1.Transfer.coordPartial_add hC hS,
    DGPS.Examples.PositiveH1.Transfer.coordPartial_const_mul (isSmooth_featureC h),
    DGPS.Examples.PositiveH1.Transfer.coordPartial_const_mul (isSmooth_featureS h),
    DGPS.Examples.PositiveH1.Transfer.coordPartial_const_mul (isSmooth_featureB h)]

/-- Exact changing-law generator feedback as a genuine probability integral. -/
theorem elementaryGeneratorFeedback_kernel_integral (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryGeneratorFeedback h ρ x =
      ∫ y, elementaryFeatureGenerator h (fun z => kernelK h x z) y
        ∂(densityMeasure ρ : Measure (Torus 1)) := by
  simp_rw [kernel_generator_row]
  rw [integral_linear3 _ _ _ _
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureC h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureS h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureB h))]
  unfold elementaryGeneratorFeedback
  ring

/-- Exact changing-law force feedback, including the actual physical derivative. -/
theorem elementaryForceFeedback_kernel_integral (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryForceFeedback h ρ x =
      ∫ y, elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (fun z => kernelK h x z) y
        ∂(densityMeasure ρ : Measure (Torus 1)) := by
  have hκ : Continuous (elementaryKprime h (densityMeasure ρ)) :=
    (isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0
  have he : (fun y => elementaryKprime h (densityMeasure ρ) y *
      coordPartial 0 (fun z => kernelK h x z) y) = fun y =>
      (kAlpha * featureC h x) * (elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureC h) y) +
        (kAlpha * featureS h x) * (elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureS h) y) +
          (-kBeta * featureB h x) * (elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureB h) y) := by
    funext y
    rw [kernel_derivative_row]
    ring
  rw [he, integral_linear3 _ (fun y => elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureC h) y) (fun y => elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureS h) y) (fun y => elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (featureB h) y) (hκ.mul ((isSmooth_featureC h).continuous_coordPartial 0))
    (hκ.mul ((isSmooth_featureS h).continuous_coordPartial 0))
    (hκ.mul ((isSmooth_featureB h).continuous_coordPartial 0))]
  unfold elementaryForceFeedback
  ring

private theorem kernel_generator_cov (h : ℝ) (j : Fin 3) (x y : Torus 1) :
    elementaryFeatureGenerator h (fun z => kernelK h (x + pt ((j : ℕ) / 3)) z)
        (y + pt ((j : ℕ) / 3)) =
      elementaryFeatureGenerator h (fun z => kernelK h x z) y := by
  have he : (fun z => kernelK h (x + pt ((j : ℕ) / 3)) (z + pt ((j : ℕ) / 3))) =
      fun z => kernelK h x z := funext (kernelK_interactingThirdTurn h j x)
  have hd := congrArg (fun f : Torus 1 → ℝ => elementaryFeatureGenerator h f y) he
  rw [elementaryFeatureGenerator_interactingThirdTurn] at hd
  exact hd

private theorem kernel_derivative_cov (h : ℝ) (j : Fin 3) (x y : Torus 1) :
    coordPartial 0 (fun z => kernelK h (x + pt ((j : ℕ) / 3)) z) (y + pt ((j : ℕ) / 3)) =
      coordPartial 0 (fun z => kernelK h x z) y := by
  have he : (fun z => kernelK h (x + pt ((j : ℕ) / 3)) (z + pt ((j : ℕ) / 3))) =
      fun z => kernelK h x z := funext (kernelK_interactingThirdTurn h j x)
  have hd := congrArg (fun f : Torus 1 → ℝ => coordPartial 0 f y) he
  rw [coordPartial_translate] at hd
  exact hd

/-- Covariance of the genuine generator changing-law term, on all Abs densities. -/
theorem elementaryGeneratorFeedback_interactingThirdTurn (h : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryGeneratorFeedback h (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ)
      (x + pt ((j : ℕ) / 3)) = elementaryGeneratorFeedback h ρ x := by
  rw [elementaryGeneratorFeedback_kernel_integral, interactingDensityTranslate_integral,
    elementaryGeneratorFeedback_kernel_integral]
  exact integral_congr_ae (Eventually.of_forall (kernel_generator_cov h j x))

/-- Covariance of the genuine force changing-law term, on all Abs densities. -/
theorem elementaryForceFeedback_interactingThirdTurn (h : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryForceFeedback h (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ)
      (x + pt ((j : ℕ) / 3)) = elementaryForceFeedback h ρ x := by
  rw [elementaryForceFeedback_kernel_integral, interactingDensityTranslate_integral,
    elementaryForceFeedback_kernel_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [elementaryKprime_interactingThirdTurn, kernel_derivative_cov]

/-- Actual nonlinear weak-Euler field covariance. Both changing-law feedbacks
are retained. The rate and coupling are fixed real numbers, independent of x. -/
theorem elementaryEulerCorrection_interactingThirdTurn (h ε r : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryEulerCorrection h ε r (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ)
      (x + pt ((j : ℕ) / 3)) = elementaryEulerCorrection h ε r ρ x := by
  unfold elementaryEulerCorrection
  rw [elementaryAK_interactingThirdTurn, elementaryGeneratorFeedback_interactingThirdTurn,
    elementaryKernelMean_interactingThirdTurn, elementaryKprime_interactingThirdTurn,
    elementaryForceFeedback_interactingThirdTurn]

theorem elementaryEulerMultiplier_interactingThirdTurn (h ε r : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) :
    elementaryEulerMultiplier h ε r (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ) =
      elementaryEulerMultiplier h ε r ρ := by
  unfold elementaryEulerMultiplier
  rw [elementaryC_interactingThirdTurn, elementaryJ_interactingThirdTurn]

/-- Common native field/value transport, before any identification with family
stationarity. The external field transforms by the same physical pullback. -/
theorem externalNativeDeficit_interactingThirdTurn (h r c : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (V : Torus 1 → ℝ) :
    let a := pt ((j : ℕ) / 3)
    let τ := interactingDensityTranslate a ρ
    (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal +
        (∫ x, V (x - a) ∂(densityMeasure τ : Measure (Torus 1))) - c =
      (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
        (∫ x, V x ∂(densityMeasure ρ : Measure (Torus 1))) - c := by
  dsimp only
  rw [ordinaryFisher_interactingThirdTurn, ordinaryEntropy_interactingThirdTurn,
    interactingDensityTranslate_integral]
  simp only [add_sub_cancel_right]

end DGPS.Examples.ThreeSpeciesCircle
