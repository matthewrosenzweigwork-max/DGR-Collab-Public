import LeanResearch.PeriodicAttractiveLogGas.RectangleRotation
import LeanResearch.PeriodicAttractiveLogGas.ScaledRectangleDensity

/-! The proved density estimates after an actual coordinate isometry,
including composition with translation and positive dilation. These are
planar statements; identifying their charts with torus cells is separate. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.RectangleRotation

open DensityEntropy

/-- The horizontal hypotheses are discharged by the checked density theorem. -/
theorem vertical_density_estimates (p : PlanarSpace → ℝ)
    [IsProbabilityMeasure (horizontalLaw p)] {c q K : ℝ}
    (hc : 0 < c) (hpc : ∀ᵐ x ∂rectangleLebesgue, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) rectangleLebesgue)
    (hK : lpNorm p (ENNReal.ofReal q) rectangleLebesgue ≤ K)
    {f : PlanarSpace → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f closedVerticalRectangle) :
    MemLp (rectangleOrdinaryGradient f) 2 (verticalLaw p) ∧ MemLp f 2 (verticalLaw p) ∧
      ProbabilityTheory.variance f (verticalLaw p) ≤ poincareConstant rectangleSobolevConstant c q K *
        (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂verticalLaw p) ∧
      entropy (verticalLaw p) (fun x ↦ f x ^ 2) ≤
        ((logSobolevConstant rectangleSobolevConstant c q K *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂verticalLaw p) : ℝ) : EReal) ∧
      ∀ s : ℝ, 2 ≤ s →
        MemLp (fun x ↦ f x - ∫ y, f y ∂verticalLaw p) (ENNReal.ofReal s) (verticalLaw p) ∧
          lpNorm (fun x ↦ f x - ∫ y, f y ∂verticalLaw p) (ENNReal.ofReal s) (verticalLaw p) ≤
            momentConstant rectangleSobolevConstant c q K s *
              lpNorm (rectangleOrdinaryGradient f) 2 (verticalLaw p) := by
  let := verticalLaw_probability p
  have hac : verticalLaw p ≪ verticalLebesgue := withDensity_absolutelyContinuous _ _
  refine ⟨memLp_gradient_vertical_of_absolutelyContinuous hac hf 2,
    memLp_vertical_of_absolutelyContinuous hac hf 2, ?_, ?_, ?_⟩
  · apply transport_poincare_vertical p _ _ hf
    intro u Lu hu
    exact (rectangle_density_estimates (ν := horizontalLaw p) rfl hc hpc hq hpq hK hu).2.2.1
  · apply transport_logSobolev_vertical p _ _ hf
    intro u Lu hu
    exact (rectangle_density_estimates (ν := horizontalLaw p) rfl hc hpc hq hpq hK hu).2.2.2.1
  · intro s hs
    refine ⟨memLp_centered_vertical_of_absolutelyContinuous hac hf _, ?_⟩
    apply transport_moment_vertical p _ hs _ hf
    intro u Lu hu
    exact ((rectangle_density_estimates (ν := horizontalLaw p) rfl hc hpc hq hpq hK hu).2.2.2.2 s hs).2

theorem lipschitzOnWith_swapPullback {s : Set PlanarSpace} {f : PlanarSpace → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (coordinateSwap '' s)) :
    LipschitzOnWith L (fun Z ↦ f (coordinateSwap Z)) s := by
  simpa only [mul_one, Function.comp_def] using!
    hf.comp coordinateSwap.lipschitz.lipschitzOnWith (fun Z hZ ↦ ⟨Z, hZ, rfl⟩)

theorem differentiableAt_of_swap {f : PlanarSpace → ℝ} {Z : PlanarSpace}
    (hf : DifferentiableAt ℝ (fun W ↦ f (coordinateSwap W)) Z) :
    DifferentiableAt ℝ f (coordinateSwap Z) := by
  have hf' : DifferentiableAt ℝ (fun W ↦ f (coordinateSwap W)) (coordinateSwap (coordinateSwap Z)) := by
    simpa only [coordinateSwap_involutive] using hf
  have h := hf'.comp (coordinateSwap Z) (hasFDerivAt_coordinateSwap (coordinateSwap Z)).differentiableAt
  simpa only [Function.comp_def, coordinateSwap_involutive] using h

theorem centered_memLp_swapLaw_iff (μ : Measure PlanarSpace) (f : PlanarSpace → ℝ) (p : ℝ≥0∞) :
    MemLp (fun Z ↦ f (coordinateSwap Z) - ∫ W, f (coordinateSwap W) ∂μ) p μ ↔
      MemLp (fun x ↦ f x - ∫ y, f y ∂swapLaw μ) p (swapLaw μ) := by
  rw [integral_swapLaw μ f]
  exact memLp_swapLaw_iff μ (fun x ↦ f x - ∫ y, f y ∂swapLaw μ) p

open RectangleDilation

/-- The isometry is applied after the actual affine dilation. Both resulting
energy and moment coefficients retain their exact source powers of J. -/
theorem oriented_scaled_density_estimates (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)] {c q K : ℝ}
    (hc : 0 < c) (hpc : ∀ᵐ x ∂RectangleDilation.referenceMeasure b, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) (RectangleDilation.referenceMeasure b))
    (hK : lpNorm p (ENNReal.ofReal q) (RectangleDilation.referenceMeasure b) ≤ K)
    {f : PlanarSpace → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (coordinateSwap '' scaledClosed b a J)) :
    MemLp (rectangleOrdinaryGradient f) 2 (swapLaw (scaledLaw b a J p)) ∧
      MemLp f 2 (swapLaw (scaledLaw b a J p)) ∧
      ProbabilityTheory.variance f (swapLaw (scaledLaw b a J p)) ≤
        (poincareConstant (sobolevConstant b) c q K / J ^ 2) *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂swapLaw (scaledLaw b a J p)) ∧
      entropy (swapLaw (scaledLaw b a J p)) (fun x ↦ f x ^ 2) ≤
        (((logSobolevConstant (sobolevConstant b) c q K / J ^ 2) *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂swapLaw (scaledLaw b a J p)) : ℝ) : EReal) ∧
      ∀ s : ℝ, 2 ≤ s →
        MemLp (fun x ↦ f x - ∫ y, f y ∂swapLaw (scaledLaw b a J p)) (ENNReal.ofReal s)
          (swapLaw (scaledLaw b a J p)) ∧
          lpNorm (fun x ↦ f x - ∫ y, f y ∂swapLaw (scaledLaw b a J p)) (ENNReal.ofReal s)
            (swapLaw (scaledLaw b a J p)) ≤
            (momentConstant (sobolevConstant b) c q K s / J) *
              lpNorm (rectangleOrdinaryGradient f) 2 (swapLaw (scaledLaw b a J p)) := by
  let := scaledLaw_probability b a hJ p
  have hf' := lipschitzOnWith_swapPullback hf
  have h := scaled_density_estimates b a hJ p hc hpc hq hpq hK hf'
  have hac : scaledLaw b a J p ≪ scaledLebesgue b a J := withDensity_absolutelyContinuous _ _
  have hd : ∀ᵐ x ∂swapLaw (scaledLaw b a J p), DifferentiableAt ℝ f x := by
    rw [swapLaw, measurableEmbedding_coordinateSwap.ae_map_iff]
    filter_upwards [hac.ae_le (ae_differentiableAt_scaled hJ hf')] with Z hZ
    exact differentiableAt_of_swap hZ
  have hGc : MemLp (fun Z ↦ rectangleOrdinaryGradient f (coordinateSwap Z)) 2 (scaledLaw b a J p) := by
    apply h.1.congr_norm
      ((measurable_rectangleOrdinaryGradient f).comp coordinateSwap.continuous.measurable).aestronglyMeasurable
    filter_upwards [ae_gradient_swap_of_ae_differentiable hd] with Z hZ
    rw [hZ, norm_coordinateSwap, Function.comp_def]
  refine ⟨(memLp_swapLaw_iff _ _ _).mp hGc, (memLp_swapLaw_iff _ _ _).mp h.2.1, ?_, ?_, ?_⟩
  · have hPI := h.2.2.1
    rw [variance_swapLaw, integral_energy_swap_of_ae_differentiable hd] at hPI
    exact hPI
  · have hLSI := h.2.2.2.1
    rw [entropy_swapLaw (scaledLaw b a J p) (fun x ↦ f x ^ 2),
      integral_energy_swap_of_ae_differentiable hd] at hLSI
    exact hLSI
  · intro s hs
    have hm := h.2.2.2.2 s hs
    refine ⟨(centered_memLp_swapLaw_iff _ _ _).mp hm.1, ?_⟩
    have hb := hm.2
    rw [centered_lpNorm_swapLaw, lpNorm_gradient_swap_of_ae_differentiable hd] at hb
    exact hb

end PeriodicAttractiveLogGas.RectangleRotation
