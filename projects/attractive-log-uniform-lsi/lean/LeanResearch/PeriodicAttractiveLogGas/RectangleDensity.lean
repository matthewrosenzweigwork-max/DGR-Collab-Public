import LeanResearch.PeriodicAttractiveLogGas.RectangleSobolev
import LeanResearch.PeriodicAttractiveLogGas.DensityEntropy

/-! Source Lemma 3.2 on both reference rectangles. The actual ordinary Riesz
gradient is used, and its weighted integrability follows from the Lipschitz
bound. No bounded upper density or separation hypothesis is imposed. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas

open DensityEntropy

theorem ae_bounded_square {f : PlanarSpace → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f closedUnitSquare) :
    ∃ M : ℝ, ∀ᵐ x ∂squareLebesgue, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_closedUnitSquare.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_closedUnitSquare] with x hx
  simpa only [Real.norm_eq_abs] using hM x hx

theorem ae_bounded_rectangle {f : PlanarSpace → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f closedDoubleRectangle) :
    ∃ M : ℝ, ∀ᵐ x ∂rectangleLebesgue, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_closedDoubleRectangle.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, ?_⟩
  filter_upwards [ae_mem_openDoubleRectangle] with x hx
  simpa only [Real.norm_eq_abs] using
    hM x (fun j hj ↦ ⟨(hx j hj).1.le, (hx j hj).2.le⟩)

theorem memLp_gradient_square_weighted {ν : Measure PlanarSpace} [IsFiniteMeasure ν]
    (hν : ν ≪ squareLebesgue) {f : PlanarSpace → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f closedUnitSquare) (r : ℝ≥0∞) :
    MemLp (rectangleOrdinaryGradient f) r ν := by
  apply MemLp.of_bound (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable (L : ℝ)
  filter_upwards [hν.ae_le (ae_norm_fderiv_on_square_le hf)] with x hx
  simpa only [norm_rectangleOrdinaryGradient] using hx

theorem memLp_gradient_rectangle_weighted {ν : Measure PlanarSpace} [IsFiniteMeasure ν]
    (hν : ν ≪ rectangleLebesgue) {f : PlanarSpace → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f closedDoubleRectangle) (r : ℝ≥0∞) :
    MemLp (rectangleOrdinaryGradient f) r ν := by
  apply MemLp.of_bound (measurable_rectangleOrdinaryGradient f).aestronglyMeasurable (L : ℝ)
  filter_upwards [hν.ae_le (ae_norm_fderiv_on_rectangle_le hf)] with x hx
  simpa only [norm_rectangleOrdinaryGradient] using hx

/-- All three source estimates on the unit square, for arbitrary actual
probability densities satisfying just the lower and finite-Lq bounds. -/
theorem square_density_estimates {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    {p f : PlanarSpace → ℝ} {c q K : ℝ} {L : ℝ≥0}
    (hν : ν = squareLebesgue.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hc : 0 < c) (hpc : ∀ᵐ x ∂squareLebesgue, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) squareLebesgue)
    (hK : lpNorm p (ENNReal.ofReal q) squareLebesgue ≤ K)
    (hf : LipschitzOnWith L f closedUnitSquare) :
    MemLp (rectangleOrdinaryGradient f) 2 ν ∧ MemLp f 2 ν ∧
      ProbabilityTheory.variance f ν ≤ poincareConstant squareSobolevConstant c q K *
        (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂ν) ∧
      entropy ν (fun x ↦ f x ^ 2) ≤
        ((logSobolevConstant squareSobolevConstant c q K *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂ν) : ℝ) : EReal) ∧
      ∀ s : ℝ, 2 ≤ s →
        MemLp (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ∧
          lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ≤
            momentConstant squareSobolevConstant c q K s *
              lpNorm (rectangleOrdinaryGradient f) 2 ν := by
  have hG := memLp_gradient_square_weighted (DensityMoments.density_absolutelyContinuous hν) hf 2
  refine ⟨hG, ?_⟩
  exact density_estimates hν hc hpc hq hpq hK
    (aestronglyMeasurable_square hf).aemeasurable (ae_bounded_square hf) hG
    (fun r _ ↦ squareSobolevConstant_nonneg r) (fun _ hr ↦ square_lipschitz_sobolev hr hf)

/-- All three source estimates on the double rectangle. The ordinary
gradient and normalized reference measure have the source conventions. -/
theorem rectangle_density_estimates {ν : Measure PlanarSpace} [IsProbabilityMeasure ν]
    {p f : PlanarSpace → ℝ} {c q K : ℝ} {L : ℝ≥0}
    (hν : ν = rectangleLebesgue.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hc : 0 < c) (hpc : ∀ᵐ x ∂rectangleLebesgue, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) rectangleLebesgue)
    (hK : lpNorm p (ENNReal.ofReal q) rectangleLebesgue ≤ K)
    (hf : LipschitzOnWith L f closedDoubleRectangle) :
    MemLp (rectangleOrdinaryGradient f) 2 ν ∧ MemLp f 2 ν ∧
      ProbabilityTheory.variance f ν ≤ poincareConstant rectangleSobolevConstant c q K *
        (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂ν) ∧
      entropy ν (fun x ↦ f x ^ 2) ≤
        ((logSobolevConstant rectangleSobolevConstant c q K *
          (∫ x, ‖rectangleOrdinaryGradient f x‖ ^ 2 ∂ν) : ℝ) : EReal) ∧
      ∀ s : ℝ, 2 ≤ s →
        MemLp (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ∧
          lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ≤
            momentConstant rectangleSobolevConstant c q K s *
              lpNorm (rectangleOrdinaryGradient f) 2 ν := by
  have hG := memLp_gradient_rectangle_weighted (DensityMoments.density_absolutelyContinuous hν) hf 2
  refine ⟨hG, ?_⟩
  exact density_estimates hν hc hpc hq hpq hK
    (aestronglyMeasurable_rectangle hf).aemeasurable (ae_bounded_rectangle hf) hG
    (fun r _ ↦ rectangleSobolevConstant_nonneg r) (fun _ hr ↦ rectangle_lipschitz_sobolev hr hf)

end PeriodicAttractiveLogGas
