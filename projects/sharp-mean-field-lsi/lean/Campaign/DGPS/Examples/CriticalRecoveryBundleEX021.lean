import DGPS.Examples.CriticalRecoveryBridgesEX021
import DGPS.Examples.CriticalRecoveryAsymptoticsEX021
import DGPS.Examples.CriticalHessianKernelEX021
import DGPS.Examples.CriticalRecoveryEX021

/-!
# Critical von Mises recovery and the singular Hessian kernel (EX021)
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Examples

/-- EX021 at the critical attractive XY model (κ = 2, h = 0). The trial is the normalized,
strictly positive von Mises density. Its canonical DEF010 gap, dissipation, and quotient have the
displayed right-sided small-parameter asymptotics. At Haar, the centered Hessian is nonnegative,
and its literal kernel is the real span of the first cosine and sine modes. -/
theorem critical_recovery_and_exact_hessian_kernel :
    (∀ t : ℝ, 0 < t → t ≤ 1 / 100 →
      |((DGPS.scalarGap (DGPS.Models.attractiveXY 2 0)
          (CriticalRecoveryBridgesEX021.vonMisesAbsoluteDensityEX021 t) : ℝ≥0) : ℝ) -
          t ^ 4 / 64| ≤ 5 * t ^ 6 ∧
        0 < DGPS.scalarGap (DGPS.Models.attractiveXY 2 0)
          (CriticalRecoveryBridgesEX021.vonMisesAbsoluteDensityEX021 t) ∧
        |ENNReal.toReal (DGPS.scalarDissipation (DGPS.Models.attractiveXY 2 0)
          CriticalRecoveryBridgesEX021.vonMisesDriftEX021
          (CriticalRecoveryBridgesEX021.vonMisesAbsoluteDensityEX021 t)) -
          (4 * Real.pi ^ 2) * t ^ 6 / 128| ≤
          3 * (4 * Real.pi ^ 2) * t ^ 8 ∧
        |ENNReal.toReal (DGPS.scalarQuotient (DGPS.Models.attractiveXY 2 0)
          CriticalRecoveryBridgesEX021.vonMisesDriftEX021
          (CriticalRecoveryBridgesEX021.vonMisesAbsoluteDensityEX021 t)) -
          (4 * Real.pi ^ 2) * t ^ 2 / 4| ≤
          400 * (4 * Real.pi ^ 2) * t ^ 4) ∧
    (∀ t : ℝ,
      (∀ x : DGPS.Torus 1,
        0 < CriticalRecoveryAsymptoticsEX021.vonMisesTorusDensityEX021 t x) ∧
      (∀ x : DGPS.Torus 1,
        (CriticalRecoveryBridgesEX021.vonMisesAbsoluteDensityEX021 t).sqrt x ^ 2 =
          CriticalRecoveryAsymptoticsEX021.vonMisesTorusDensityEX021 t x) ∧
      ∫ x, CriticalRecoveryAsymptoticsEX021.vonMisesTorusDensityEX021 t x
        ∂DGPS.haar 1 = 1) ∧
    (∀ f : DGPS.centeredL2 (DGPS.haarProbability 1),
      0 ≤ inner ℝ f (DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
        (DGPS.haarProbability 1) f)) ∧
    (∀ f : DGPS.centeredL2 (DGPS.haarProbability 1),
      DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
          (DGPS.haarProbability 1) f = 0 ↔
        ∃ a b : ℝ,
          f.1 =
            CriticalRecoveryBridgesEX021.firstHarmonicCombinationEX021 a b) := by
  refine ⟨?_, ?_, CriticalRecoveryEX021.critical_hessian_nonneg_xy021, ?_⟩
  · intro t ht0 ht1
    exact ⟨CriticalRecoveryBridgesEX021.vonMises_scalarGap_jetEX021 t ht0 ht1,
      CriticalRecoveryBridgesEX021.vonMises_scalarGap_posEX021 t ht0 ht1,
      CriticalRecoveryBridgesEX021.vonMises_scalarDissipation_real_jetEX021 t ht0 ht1,
      CriticalRecoveryBridgesEX021.vonMises_scalarQuotient_real_jetEX021 t ht0 ht1⟩
  · intro t
    exact ⟨fun x => CriticalRecoveryAsymptoticsEX021.vonMisesTorusDensity_pos_EX021 t x,
      fun x => CriticalRecoveryBridgesEX021.vonMisesRoot_sqEX021 t x,
      CriticalRecoveryAsymptoticsEX021.vonMisesTorusDensity_mass_EX021 t⟩
  · exact CriticalRecoveryBridgesEX021.exact_hessian_kernel_spanEX021

end DGPS.Examples
