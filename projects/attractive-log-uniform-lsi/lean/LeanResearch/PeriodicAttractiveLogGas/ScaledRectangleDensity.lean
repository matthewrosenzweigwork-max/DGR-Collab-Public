import LeanResearch.PeriodicAttractiveLogGas.RectangleDensity
import LeanResearch.PeriodicAttractiveLogGas.RectangleDilation

/-! The source density estimates on actual affine planar rectangles.
The derivative and measure transports are proved in RectangleDilation;
the input inequalities are discharged here by RectangleDensity. Identifying
these rectangles with periodic mesh cells is a separate geometric obligation. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.RectangleDilation

open DensityEntropy

def sobolevConstant : Kind → ℝ → ℝ
  | .square => squareSobolevConstant
  | .double => rectangleSobolevConstant

theorem reference_density_estimates (b : Kind) (p : PlanarSpace → ℝ)
    [IsProbabilityMeasure (referenceLaw b p)] {c q K : ℝ}
    (hc : 0 < c) (hpc : ∀ᵐ x ∂referenceMeasure b, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) (referenceMeasure b))
    (hK : lpNorm p (ENNReal.ofReal q) (referenceMeasure b) ≤ K)
    {f : PlanarSpace → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (closed b)) :
    MemLp (rectangleOrdinaryGradient f) 2 (referenceLaw b p) ∧ MemLp f 2 (referenceLaw b p) ∧
      ProbabilityTheory.variance f (referenceLaw b p) ≤ poincareConstant (sobolevConstant b) c q K *
        (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂referenceLaw b p) ∧
      entropy (referenceLaw b p) (fun x ↦ f x ^ 2) ≤
        ((logSobolevConstant (sobolevConstant b) c q K *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂referenceLaw b p) : ℝ) : EReal) ∧
      ∀ s : ℝ, 2 ≤ s →
        MemLp (fun x ↦ f x - ∫ y, f y ∂referenceLaw b p) (ENNReal.ofReal s) (referenceLaw b p) ∧
          lpNorm (fun x ↦ f x - ∫ y, f y ∂referenceLaw b p) (ENNReal.ofReal s) (referenceLaw b p) ≤
            momentConstant (sobolevConstant b) c q K s *
              lpNorm (rectangleOrdinaryGradient f) 2 (referenceLaw b p) := by
  cases b
  · exact square_density_estimates (ν := referenceLaw .square p) rfl hc hpc hq hpq hK hf
  · exact rectangle_density_estimates (ν := referenceLaw .double p) rfl hc hpc hq hpq hK hf

/-- All three inequalities with their exact J factors. No reference
inequality, differentiability, or integrability assumption remains. -/
theorem scaled_density_estimates (b : Kind) (a : PlanarSpace) {J : ℝ} (hJ : 0 < J)
    (p : PlanarSpace → ℝ) [IsProbabilityMeasure (referenceLaw b p)] {c q K : ℝ}
    (hc : 0 < c) (hpc : ∀ᵐ x ∂referenceMeasure b, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) (referenceMeasure b))
    (hK : lpNorm p (ENNReal.ofReal q) (referenceMeasure b) ≤ K)
    {f : PlanarSpace → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (scaledClosed b a J)) :
    MemLp (rectangleOrdinaryGradient f) 2 (scaledLaw b a J p) ∧ MemLp f 2 (scaledLaw b a J p) ∧
      ProbabilityTheory.variance f (scaledLaw b a J p) ≤
        (poincareConstant (sobolevConstant b) c q K / J ^ 2) *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂scaledLaw b a J p) ∧
      entropy (scaledLaw b a J p) (fun x ↦ f x ^ 2) ≤
        (((logSobolevConstant (sobolevConstant b) c q K / J ^ 2) *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂scaledLaw b a J p) : ℝ) : EReal) ∧
      ∀ s : ℝ, 2 ≤ s →
        MemLp (fun x ↦ f x - ∫ y, f y ∂scaledLaw b a J p) (ENNReal.ofReal s) (scaledLaw b a J p) ∧
          lpNorm (fun x ↦ f x - ∫ y, f y ∂scaledLaw b a J p) (ENNReal.ofReal s) (scaledLaw b a J p) ≤
            (momentConstant (sobolevConstant b) c q K s / J) *
              lpNorm (rectangleOrdinaryGradient f) 2 (scaledLaw b a J p) := by
  let := scaledLaw_probability b a hJ p
  have hfinite := density_dilation_finite b a hJ p hf
  refine ⟨hfinite.2.2.1, hfinite.1 2, ?_, ?_, ?_⟩
  · apply transport_poincare b a hJ p (poincareConstant (sobolevConstant b) c q K) _ hf
    intro u L hu
    exact (reference_density_estimates b p hc hpc hq hpq hK hu).2.2.1
  · apply transport_logSobolev b a hJ p (logSobolevConstant (sobolevConstant b) c q K) _ hf
    intro u L hu
    exact (reference_density_estimates b p hc hpc hq hpq hK hu).2.2.2.1
  · intro s hs
    refine ⟨(hfinite.1 (ENNReal.ofReal s)).sub (memLp_const _), ?_⟩
    apply transport_moment b a hJ p (momentConstant (sobolevConstant b) c q K s) hs _ hf
    intro u L hu
    exact ((reference_density_estimates b p hc hpc hq hpq hK hu).2.2.2.2 s hs).2

end PeriodicAttractiveLogGas.RectangleDilation
