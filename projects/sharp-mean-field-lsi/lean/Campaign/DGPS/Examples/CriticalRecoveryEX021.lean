import DGPS.Equilibrium.Hessian
import DGPS.Structural.MinimizerHessian
import DGPS.Examples.AttractiveXYCritical

/-!
# Critical XY Hessian identities (EX021)

The endpoint interaction has centered kernel `-2 cos(2π(x-y))` at Haar. This is the finite-rank
identity used to identify its first-harmonic null directions.
-/

open MeasureTheory

namespace DGPS.Examples.CriticalRecoveryEX021

open DGPS.Examples.AttractiveXY
open DGPS.Examples.AttractiveXYCritical

/-- The critical XY interaction has constant Haar convolution. -/
theorem interactionConvolution_critical_xy021 (x : DGPS.Torus 1) :
    DGPS.interactionConvolution (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) x = 2 := by
  unfold DGPS.interactionConvolution
  change ∫ z, (DGPS.Models.attractiveXY 2 0).W x z ∂(DGPS.haar 1) = 2
  simp_rw [DGPS.Examples.AttractiveXY.attractiveXY_W 2 0, xyMode_re_sub]
  have hmode := DGPS.Examples.AttractiveXYCritical.integral_xyMode_haar_xyc
  have hmean : ∫ y, (xyMode y).re ∂(DGPS.haar 1) = 0 := by
    calc
      ∫ y, (xyMode y).re ∂(DGPS.haar 1) =
          (∫ y, xyMode y ∂(DGPS.haar 1)).re :=
        (integral_re (DGPS.Examples.AttractiveXYCritical.integrable_xyMode_xyc _))
      _ = 0 := by
        rw [DGPS.Examples.AttractiveXYCritical.integral_xyMode_haar_xyc]
        simp
  have him : ∫ y, (xyMode y).im ∂(DGPS.haar 1) = 0 := by
    calc
      ∫ y, (xyMode y).im ∂(DGPS.haar 1) =
          (∫ y, xyMode y ∂(DGPS.haar 1)).im :=
        (integral_im (DGPS.Examples.AttractiveXYCritical.integrable_xyMode_xyc _))
      _ = 0 := by
        rw [DGPS.Examples.AttractiveXYCritical.integral_xyMode_haar_xyc]
        simp
  have hre : Integrable (fun z : DGPS.Torus 1 => (xyMode x).re * (xyMode z).re)
      (DGPS.haar 1) :=
    ((continuous_const.mul (Complex.continuous_re.comp continuous_xyMode)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have himI : Integrable (fun z : DGPS.Torus 1 => (xyMode x).im * (xyMode z).im)
      (DGPS.haar 1) :=
    ((continuous_const.mul (Complex.continuous_im.comp continuous_xyMode)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hsum : Integrable (fun z : DGPS.Torus 1 =>
      (xyMode x).re * (xyMode z).re + (xyMode x).im * (xyMode z).im) (DGPS.haar 1) :=
    hre.add himI
  have hsum0 : ∫ z, (xyMode x).re * (xyMode z).re +
      (xyMode x).im * (xyMode z).im ∂DGPS.haar 1 = 0 := by
    rw [integral_add hre himI, integral_const_mul, integral_const_mul, hmean, him]
    simp
  rw [integral_const_mul, integral_sub (integrable_const _) hsum,
    integral_const, hsum0]
  simp

/-- At Haar, the critical centered interaction is the negative first-harmonic kernel. -/
theorem centeredKernel_critical_xy021 (x y : DGPS.Torus 1) :
    DGPS.centeredKernel (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) x y =
      -2 * (xyMode (x - y)).re := by
  have hconvx := interactionConvolution_critical_xy021 x
  have hconvy := interactionConvolution_critical_xy021 y
  have hmean : DGPS.meanInteraction (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) = 2 := by
    rw [← DGPS.integral_interactionConvolution]
    simp [interactionConvolution_critical_xy021]
  rw [DGPS.centeredKernel, hconvx, hconvy, hmean, attractiveXY_W]
  ring

/-- The exact critical Hessian is nonnegative at Haar, by the proved global-minimizer theorem. -/
theorem critical_hessian_nonneg_xy021 :
    ∀ f : DGPS.centeredL2 (DGPS.haarProbability 1),
      0 ≤ inner ℝ f (DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
        (DGPS.haarProbability 1) f) := by
  have hmin := DGPS.Examples.strict_entropy_fourier_inequality_at_criticality
  have hF : DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) =
      ((1 : ℝ) : EReal) := DGPS.Examples.AttractiveXYCritical.freeEnergy_haar_xyc
  have hM : DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY 2 0) = ((1 : ℝ) : EReal) :=
    hmin.2.2.2.2.1
  have heq : DGPS.freeEnergy (DGPS.Models.attractiveXY 2 0) (DGPS.haarProbability 1) =
      DGPS.freeEnergyMinimum (DGPS.Models.attractiveXY 2 0) := hF.trans hM.symm
  exact (DGPS.Structural.minimizer_centeredHessian_nonneg _ heq).2.2

end DGPS.Examples.CriticalRecoveryEX021
