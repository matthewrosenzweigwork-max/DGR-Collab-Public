import DGRHS.Gaussian.PeriodicGlobalMinimization
import DGRHS.Gaussian.PeriodicD11RelativeEntropy

/-! The source strict global-minimization bound in its full all-AC-law domain.
Only the explicit trial requires proper entropy and energy; those properties
are proved, not transferred to arbitrary competitors. -/
noncomputable section
open MeasureTheory InformationTheory Set
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian.D11Imported.HighDim
open DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma periodicD11Measure_extendedGreenEnergy :
    periodicGreenEnergyExtended periodicD11Measure=(periodicD11GreenEnergy:EReal) := by
  rw [signedGreen_extended_eq_integral periodicD11Measure periodicD11Measure_pair_integrable,
    periodicD11Measure_pair_integral]

lemma periodicD11Measure_extendedGreenEnergy_centered :
    periodicGreenEnergyExtended periodicD11Measure=
      (((∫ x,(periodizedProfile x-1)*(∫ y,(periodizedProfile y-1)*periodicLogKernel (x-y)
        ∂periodicHaar (Fin 11)) ∂periodicHaar (Fin 11)):ℝ):EReal) := by
  rw [periodicD11_centeredGreenEnergy_eq,periodicD11Measure_extendedGreenEnergy]

lemma periodicD11Measure_entropyEnergyComparison_iff (β : ℝ) :
    ((β/2:ℝ):EReal)*periodicGreenEnergyExtended periodicD11Measure≤
      (klDiv periodicD11Measure (periodicHaar (Fin 11))).toEReal ↔
      β/2*periodicD11GreenEnergy≤entropy competitorDensity := by
  rw [periodicD11Measure_extendedGreenEnergy,periodicD11Measure_klDiv]
  change ((β/2:ℝ):EReal)*(periodicD11GreenEnergy:EReal)≤
    (ENNReal.ofReal (entropy competitorDensity):EReal) ↔ _
  rw [EReal.coe_ennreal_ofReal,max_eq_left periodicD11_entropy_nonneg,←EReal.coe_mul]
  norm_cast

lemma periodic_d11_global_minimizer_lt_trial (β : ℝ)
    (hβ : β∈periodicGlobalMinimizerTemperatures (Fin 11)) :
    β<(8653/8680:ℝ)*periodicStabilityThreshold (Fin 11) := by
  have hc := hβ.2.2 periodicD11Measure periodicD11Measure_probability
    periodicD11Measure_absolutelyContinuous
  rw [periodicD11Measure_entropyEnergyComparison_iff] at hc
  by_contra h
  have hn := periodicD11_negative_free_energy_of_le β (le_of_not_gt h)
  linarith

theorem periodic_d11_global_threshold_le_trial :
    periodicGlobalMinimizationThreshold (Fin 11)≤
      (8653/8680:ℝ)*periodicStabilityThreshold (Fin 11) := by
  apply csSup_le ⟨0,periodicGlobalMinimizerTemperatures_zero (Fin 11)⟩
  intro β hβ
  exact (periodic_d11_global_minimizer_lt_trial β hβ).le

/-- Exact source ratio and normalization, with every AC probability law in
the variational class and native extended relative entropy. -/
theorem periodic_d11_global_threshold_strict :
    periodicGlobalMinimizationThreshold (Fin 11)<
        (8653/8673:ℝ)*periodicStabilityThreshold (Fin 11) ∧
      (8653/8673:ℝ)*periodicStabilityThreshold (Fin 11)=
        (8653/8673:ℝ)*(64*Real.pi^5/945) ∧
      (8653/8673:ℝ)*periodicStabilityThreshold (Fin 11)<periodicStabilityThreshold (Fin 11) := by
  have hs := periodicStabilityThreshold_pos (ι := Fin 11)
  refine ⟨?_,by rw [periodicStabilityThreshold_eleven],?_⟩
  · nlinarith [periodic_d11_global_threshold_le_trial]
  · nlinarith

end DGRHS.Periodic
#check @DGRHS.Periodic.periodicD11Measure_extendedGreenEnergy_centered
#check @DGRHS.Periodic.periodic_d11_global_threshold_strict
#print axioms DGRHS.Periodic.periodicD11Measure_extendedGreenEnergy_centered
#print axioms DGRHS.Periodic.periodicD11Measure_entropyEnergyComparison_iff
#print axioms DGRHS.Periodic.periodic_d11_global_threshold_strict
