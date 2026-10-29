import LeanResearch.PeriodicAttractiveLogGas.PeriodicMollifier
import LeanResearch.PeriodicAttractiveLogGas.KernelLemma
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! The actual prescribed Green convolution family from source Lemma 2.2.
The torus integral is proved equal to the Euclidean convolution of the periodic
Green lift with the compact planar mollifier. This yields ordinary smoothness
of the lift. Evenness, zero mean and the scale-independent lower bound are
proved with actual integrability. The upper, gradient and convergence estimates
are separate obligations. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Convolution ContDiff

namespace PeriodicAttractiveLogGas

theorem hasCompactSupport_periodicMollifier (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (periodicMollifier ε hε) :=
  (isClosed_tsupport _).isCompact

def regularizedGreen (ε : ℝ) (hε : 0 < ε) : Torus → ℝ :=
  regularGreenRepresentative ⋆[ContinuousLinearMap.mul ℝ ℝ, torusMeasure]
    periodicMollifier ε hε

theorem regularizedGreen_convolutionExists (ε : ℝ) (hε : 0 < ε) :
    ConvolutionExists regularGreenRepresentative (periodicMollifier ε hε)
      (ContinuousLinearMap.mul ℝ ℝ) torusMeasure :=
  (hasCompactSupport_periodicMollifier ε hε).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) regularGreenRepresentative_integrable.locallyIntegrable
    (continuous_periodicMollifier ε hε)

theorem regularizedGreen_integrand_integrable (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    Integrable (fun w => regularGreenRepresentative w * periodicMollifier ε hε (z - w))
      torusMeasure :=
  regularizedGreen_convolutionExists ε hε z

theorem regularizedGreen_integrand_swap_integrable (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    Integrable (fun w => regularGreenRepresentative (z - w) * periodicMollifier ε hε w)
      torusMeasure :=
  (regularizedGreen_convolutionExists ε hε z).integrable_swap

theorem regularizedGreen_eq_integral (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    regularizedGreen ε hε z =
      ∫ w, regularGreenRepresentative w * periodicMollifier ε hε (z - w) ∂torusMeasure := rfl

theorem regularizedGreen_eq_integral_sub (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    regularizedGreen ε hε z =
      ∫ w, regularGreenRepresentative (z - w) * periodicMollifier ε hε w ∂torusMeasure :=
  convolution_mul_swap

theorem continuous_regularizedGreen (ε : ℝ) (hε : 0 < ε) :
    Continuous (regularizedGreen ε hε) :=
  (hasCompactSupport_periodicMollifier ε hε).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) regularGreenRepresentative_integrable.locallyIntegrable
    (continuous_periodicMollifier ε hε)

theorem integrable_regularizedGreen (ε : ℝ) (hε : 0 < ε) :
    Integrable (regularizedGreen ε hε) torusMeasure :=
  regularGreenRepresentative_integrable.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (integrable_periodicMollifier ε hε)

theorem regularizedGreen_even (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    regularizedGreen ε hε (-z) = regularizedGreen ε hε z :=
  convolution_neg_of_neg_eq (L := ContinuousLinearMap.mul ℝ ℝ)
    (Filter.Eventually.of_forall regularGreenRepresentative_even)
    (Filter.Eventually.of_forall (periodicMollifier_neg ε hε))

theorem regularizedGreen_integral_zero (ε : ℝ) (hε : 0 < ε) :
    ∫ z, regularizedGreen ε hε z ∂torusMeasure = 0 := by
  rw [regularizedGreen, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    regularGreenRepresentative_integrable (integrable_periodicMollifier ε hε),
    regularGreenRepresentative_integral_zero]
  simp

theorem locallyIntegrable_regularGreenLift : LocallyIntegrable regularGreenLift volume := by
  simpa only [regularGreenRepresentative_lift] using
    locallyIntegrable_torus_lift regularGreenRepresentative_integrable

/-- Exact torus/Euclidean convolution correspondence; no new normalization. -/
theorem regularizedGreen_lift_eq_convolution (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) (x : PlanarSpace) :
    regularizedGreen ε hε (torusQuotient x) =
      (regularGreenLift ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] scaledRadialMollifier ε) x := by
  rw [regularizedGreen_eq_integral_sub, convolution_mul_swap]
  calc
    (∫ w, regularGreenRepresentative (torusQuotient x - w) *
        periodicMollifier ε hε w ∂torusMeasure) =
      ∫ y in euclideanFundamentalBox (centeredBoxAnchor 0),
        regularGreenRepresentative (torusQuotient x - torusQuotient y) *
          periodicMollifier ε hε (torusQuotient y) :=
      (integral_torus_lift_on_box
        (regularizedGreen_integrand_swap_integrable ε hε (torusQuotient x)) _).symm
    _ = ∫ y in euclideanFundamentalBox (centeredBoxAnchor 0),
        regularGreenLift (x - y) * scaledRadialMollifier ε y := by
      apply setIntegral_congr_fun (measurableSet_euclideanFundamentalBox _)
      intro y hy
      change regularGreenRepresentative (torusQuotient x - torusQuotient y) *
        periodicMollifier ε hε (torusQuotient y) =
          regularGreenLift (x - y) * scaledRadialMollifier ε y
      rw [← torusQuotient_sub, regularGreenRepresentative_lift,
        periodicMollifier_lift_eq_scaled_on_box ε hε hεsmall hy]
    _ = ∫ y, regularGreenLift (x - y) * scaledRadialMollifier ε y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hn : y ∉ tsupport (scaledRadialMollifier ε) :=
        fun hs => hy (tsupport_scaledRadialMollifier_subset_centeredBox ε hε hεsmall hs)
      rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]

theorem contDiff_regularizedGreen_lift (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) :
    ContDiff ℝ ∞ (fun x : PlanarSpace => regularizedGreen ε hε (torusQuotient x)) := by
  have heq : (fun x : PlanarSpace => regularizedGreen ε hε (torusQuotient x)) =
      regularGreenLift ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] scaledRadialMollifier ε :=
    funext (regularizedGreen_lift_eq_convolution ε hε hεsmall)
  rw [heq]
  exact (hasCompactSupport_scaledRadialMollifier ε hε).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) locallyIntegrable_regularGreenLift
    (contDiff_scaledRadialMollifier ε)

theorem regularizedGreen_lower_bound {C : ℝ}
    (hC : ∀ z : Torus, -C ≤ regularGreenRepresentative z)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    -C ≤ regularizedGreen ε hε z := by
  rw [regularizedGreen_eq_integral_sub]
  calc
    -C = ∫ w, -C * periodicMollifier ε hε w ∂torusMeasure := by
      rw [integral_const_mul, integral_periodicMollifier ε hε hεsmall, mul_one]
    _ ≤ ∫ w, regularGreenRepresentative (z - w) * periodicMollifier ε hε w ∂torusMeasure :=
      integral_mono ((integrable_periodicMollifier ε hε).const_mul (-C))
        (regularizedGreen_integrand_swap_integrable ε hε z)
        (fun w => mul_le_mul_of_nonneg_right (hC (z - w)) (periodicMollifier_nonneg ε hε w))

theorem exists_regularizedGreen_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
      ∀ z : Torus, -C ≤ regularizedGreen ε hε z := by
  obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_lower_bound
  exact ⟨C, hC, fun ε hε hsmall z => regularizedGreen_lower_bound hb ε hε hsmall z⟩

end PeriodicAttractiveLogGas
