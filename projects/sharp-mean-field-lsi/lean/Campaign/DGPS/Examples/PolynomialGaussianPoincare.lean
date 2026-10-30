import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Structural.AmplitudeComparison

/-! The actual polynomial positive interaction gives H >= Id on every centered
L2 space, hence its inverse covariance is bounded above by Id. This compares
the native Gaussian and Poincare rates on the full original weak-H1 domain.
No commutation, eigenbasis, or desired spectral comparison is assumed. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
open DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private theorem hessian_lower (h : ℝ) (μ : ProbabilityMeasure (Torus 1))
    (f : centeredL2 μ) :
    ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian (canonical_elementary_polynomial_model h) μ f) := by
  rw [inner_densityHessian]
  have hn := quadratic_W_nonneg_EX055 h μ
    (f : Lp ℝ 2 (μ : Measure (Torus 1))) (integrable_lp μ f) ((mem_centeredL2 _).1 f.2)
  linarith

/-- The covariance contraction is derived for the actual polynomial kernel at
any reference probability, independently of the coercivity proof used to name
its inverse. -/
theorem polynomial_densityCovariance_form_le (h : ℝ) (μ : ProbabilityMeasure (Torus 1))
    (hH : IsCoerciveDensityHessian (canonical_elementary_polynomial_model h) μ)
    (f : centeredL2 μ) :
    inner ℝ f (densityCovariance (canonical_elementary_polynomial_model h) μ hH f) ≤ ‖f‖ ^ 2 := by
  let A := canonical_elementary_polynomial_model h
  let v := densityCovariance A μ hH f
  have hv : densityHessian A μ v = f := densityHessian_densityCovariance A μ hH f
  have hl := hessian_lower h μ v
  change ‖v‖ ^ 2 ≤ inner ℝ v (densityHessian A μ v) at hl
  rw [hv, real_inner_comm] at hl
  have hs := sq_nonneg ‖f - v‖
  rw [norm_sub_sq_real] at hs
  change inner ℝ f v ≤ ‖f‖ ^ 2
  linarith

/-- Native Gaussian >= native Poincare for the actual positive polynomial
kernel. The probability and coercivity witness are arbitrary; every original
weighted weak-H1 test remains available. -/
theorem polynomial_poincareRate_le_gaussianRate (h : ℝ) (μ : ProbabilityMeasure (Torus 1))
    (hH : IsCoerciveDensityHessian (canonical_elementary_polynomial_model h) μ) :
    poincareRate μ ≤ gaussianRate (canonical_elementary_polynomial_model h) μ hH := by
  apply (le_gaussianRate_iff_forall (canonical_elementary_polynomial_model h) μ hH _).2
  intro f hf
  have hvar : weightedVariance μ f.fn = ∫ x, f.fn x ^ 2 ∂(μ : Measure (Torus 1)) := by
    unfold weightedVariance
    simp only [hf.1, sub_zero]
  have hnorm : ‖f.toCentered μ hf.1‖ ^ 2 = weightedVariance μ f.fn := by
    show ‖((f.toCentered μ hf.1 : centeredL2 μ) : Lp ℝ 2 (μ : Measure (Torus 1)))‖ ^ 2 = _
    rw [DGPS.Structural.norm_sq_eq_integral_sq]
    rw [hvar]
    refine integral_congr_ae ?_
    filter_upwards [f.isWeak.memLp.coeFn_toLp] with x hx
    simp only [WeakH1Test.toCentered] at *
    rw [hx]
  have hden : gaussianDenominator (canonical_elementary_polynomial_model h) μ hH f hf.1 ≤
      weightedVariance μ f.fn := by
    rw [← hnorm]
    exact polynomial_densityCovariance_form_le h μ hH (f.toCentered μ hf.1)
  have hv : 0 < weightedVariance μ f.fn :=
    (gaussianDenominator_pos (canonical_elementary_polynomial_model h) μ hH hf).trans_le hden
  have hp := (le_poincareRate_iff_forall μ (poincareRate μ)).1 le_rfl f hv
  exact (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hden)).trans hp

end DGPS.Examples.PolynomialSpecies
