import DGPS.SingularCounterexample.Interfaces
import DGPS.Examples.PositiveH1.Fourier
import FullLabeledLSI.Examples.E01h1_Poisson

open MeasureTheory
open scoped ContDiff

namespace DGPS.SingularCounterexample

open SharpLSI.FL.Ex.LaneD

/-- The existing repulsive cosine interaction, restricted to the circle kernel. -/
noncomputable def cosineBaselineKernel (x : Circle) : ℝ :=
  SharpLSI.FL.Ex.LaneD.cm 1 x - 1

theorem cosineBaselineKernel_smooth_periodic : IsSmoothPeriodic cosineBaselineKernel := by
  unfold IsSmoothPeriodic
  change ContDiff ℝ ∞
    (fun v : Fin 1 → ℝ => cosineBaselineKernel (DGPS.torusLift v))
  have hform : (fun v : Fin 1 → ℝ => cosineBaselineKernel (DGPS.torusLift v)) =
      fun v => Real.cos (2 * Real.pi * v 0) - 1 := by
    funext v
    rw [show DGPS.torusLift v = torusPoint (v 0) by
      simpa [torusPoint, DGPS.torusLift] using SharpLSI.FL.Ex.LaneD.lift_eq v]
    simpa [cosineBaselineKernel, torusPoint] using SharpLSI.FL.Ex.LaneD.cm_lift 1 (v 0)
  rw [hform]
  exact (Real.contDiff_cos.comp
    (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).sub contDiff_const

private theorem cosineBaselineKernel_fourier (n : ℤ) :
    coeff1 cosineBaselineKernel n =
      ((((if 1 - n = 0 then 1 else 0) + (if -1 - n = 0 then 1 else 0)) / 2 : ℝ) : ℂ) -
        (if -n = 0 then (1 : ℂ) else 0) := by
  have hfreq (x : Circle) :
      UnitAddTorus.mFourier (-freqZ n) x = fourier (-n) (x 0) := by
    have hi : -freqZ n = SharpLSI.FL.Ex.LaneD.K1 (-n) := by
      funext i
      simp [freqZ, SharpLSI.FL.Ex.LaneD.K1]
    rw [hi, SharpLSI.FL.Ex.LaneD.mFourier_K1]
  have hcm : Integrable
      (fun x : Circle => fourier (-n) (x 0) * (SharpLSI.FL.Ex.LaneD.cm 1 x : ℂ))
      (DGPS.haar 1) := by
    apply ((SharpLSI.FL.Ex.LaneD.four_cont (-n)).mul
      (Complex.continuous_ofReal.comp (SharpLSI.FL.Ex.LaneD.cm_cont 1))).integrable_of_hasCompactSupport
    exact HasCompactSupport.of_compactSpace _
  have hfour : Integrable (fun x : Circle => fourier (-n) (x 0)) (DGPS.haar 1) := by
    apply (SharpLSI.FL.Ex.LaneD.four_cont (-n)).integrable_of_hasCompactSupport
    exact HasCompactSupport.of_compactSpace _
  calc
    coeff1 cosineBaselineKernel n =
        ∫ x, UnitAddTorus.mFourier (-freqZ n) x * (cosineBaselineKernel x : ℂ) ∂DGPS.haar 1 := by
          rw [coeff1_eq_fourierCoeff, DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
    _ = ∫ x, (fourier (-n) (x 0) * (SharpLSI.FL.Ex.LaneD.cm 1 x : ℂ) -
          fourier (-n) (x 0)) ∂DGPS.haar 1 := by
          congr 1
          funext x
          rw [hfreq x, cosineBaselineKernel, Complex.ofReal_sub, Complex.ofReal_one]
          ring
    _ = _ := by
          rw [integral_sub hcm hfour, SharpLSI.FL.Ex.LaneD.int_fourier_mul_cm n 1,
            SharpLSI.FL.Ex.LaneD.int_fourier (-n)]
          by_cases h0 : n = 0
          · subst n
            norm_num
          · by_cases h1 : n = 1
            · subst n
              norm_num
            · by_cases hm1 : n = -1
              · subst n
                norm_num
              · have h1n : 1 - n ≠ 0 := by omega
                have hm1n : -1 - n ≠ 0 := by omega
                have hn0 : -n ≠ 0 := by simpa using h0
                simp [h1n, hm1n, hn0]

private theorem cosineBaselineKernel_fourier_nonzero (n : ℤ) (hn : n ≠ 0) :
    coeff1 cosineBaselineKernel n =
      if n = 1 ∨ n = -1 then ((1 / 2 : ℝ) : ℂ) else 0 := by
  rw [cosineBaselineKernel_fourier]
  by_cases h1 : n = 1
  · simp [h1]
  · by_cases hm1 : n = -1
    · simp [hm1]
    · have hpos : 1 - n ≠ 0 := by omega
      have hneg : -1 - n ≠ 0 := by omega
      simp [h1, hm1, hn, hpos, hneg]

/-- The cosine baseline as the admissible kernel used by the singular perturbation. -/
noncomputable def cosineBaseline : BaselineKernel where
  g := cosineBaselineKernel
  measurable_g := by
    exact ((SharpLSI.FL.Ex.LaneD.cm_cont 1).sub continuous_const).measurable
  bounded_g := by
    refine ⟨2, by norm_num, fun x => ?_⟩
    rw [cosineBaselineKernel]
    calc
      |SharpLSI.FL.Ex.LaneD.cm 1 x - 1| ≤ |SharpLSI.FL.Ex.LaneD.cm 1 x| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 := by have h := SharpLSI.FL.Ex.LaneD.cm_abs_le 1 x; norm_num at h ⊢; linarith
  even_g := by
    intro x
    simp [cosineBaselineKernel, SharpLSI.FL.Ex.LaneD.cm_neg]
  zero_g := by
    simp [cosineBaselineKernel, SharpLSI.FL.Ex.LaneD.cm]
  fourier_nonneg := by
    intro n hn
    rw [cosineBaselineKernel_fourier_nonzero n hn]
    by_cases h : n = 1 ∨ n = -1 <;> simp [h]

end DGPS.SingularCounterexample
