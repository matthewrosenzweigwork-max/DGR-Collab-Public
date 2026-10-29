import DGRHS.Gaussian.D11Imported.ElevenLabelDefinitions
import DGRHS.Gaussian.D11Imported.ElevenPeriodizedMass
import DGRHS.Gaussian.D11Imported.PeriodizationIntegral
import DGRHS.Gaussian.D11Imported.PeriodizationCubeFubini
import DGRHS.Gaussian.D11Imported.ElevenCoordinateLaw

/-! The genuine joint lattice-label law and its coordinate marginals. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma translated_euclideanProfile_integrable (n : Frequency 11) :
    Integrable (fun y : Fin 11 → ℝ => euclideanProfile (fun i => y i+(n i:ℝ))) := by
  exact (measurePreserving_add_right volume (fun i => (n i:ℝ))).integrable_comp_of_integrable
    euclideanProfile_integrable

lemma labelProbability_nonneg (n : Frequency 11) : 0 ≤ labelProbability n :=
  integral_nonneg (fun _ => (euclideanProfile_pos _).le)

lemma labelProbability_ofReal (n : Frequency 11) :
    ENNReal.ofReal (labelProbability n) =
      ∫⁻ y in labelCube, ENNReal.ofReal (euclideanProfile (fun i => y i+(n i:ℝ))) :=
  ofReal_integral_eq_lintegral_ofReal (translated_euclideanProfile_integrable n).integrableOn
    (ae_of_all _ (fun _ => (euclideanProfile_pos _).le))

lemma labelProbability_lsum : (∑' n : Frequency 11, ENNReal.ofReal (labelProbability n)) = 1 := by
  simp_rw [labelProbability_ofReal]
  rw [← lintegral_tsum (fun n : Frequency 11 =>
    (show Measurable (fun y : Fin 11 → ℝ => ENNReal.ofReal (euclideanProfile (fun i => y i+(n i:ℝ)))) from
      euclideanProfile_continuous.measurable.ennreal_ofReal.comp (by fun_prop)).aemeasurable)]
  change (∫⁻ y in PeriodizationCube.cube 11, ∑' n : Frequency 11,
    ENNReal.ofReal (euclideanProfile (fun i => y i+(n i:ℝ)))) = 1
  rw [PeriodizationCube.unfold_lintegral 11 _ euclideanProfile_continuous.measurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal euclideanProfile_integrable
      (ae_of_all _ (fun _ => (euclideanProfile_pos _).le)), euclideanProfile_integral, ENNReal.ofReal_one]

lemma labelProbability_hasSum : HasSum labelProbability 1 := by
  have hs : Summable labelProbability := by
    have h := ENNReal.summable_toReal (f := fun n => ENNReal.ofReal (labelProbability n))
      (by rw [labelProbability_lsum]; simp)
    simpa only [ENNReal.toReal_ofReal (labelProbability_nonneg _)] using h
  have hmass : (∑' n, labelProbability n) = 1 := by
    have h := labelProbability_lsum
    rw [← ENNReal.ofReal_tsum_of_nonneg labelProbability_nonneg hs] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg labelProbability_nonneg) zero_le_one).mp (by simpa using h)
  exact hmass ▸ hs.hasSum

lemma euclideanProfile_insertNth (i : Fin 11) (t : ℝ) (y : Fin 10 → ℝ) :
    euclideanProfile (i.insertNth t y) = euclideanProfile (Fin.cons t y) := by
  have h1 : (∑ j : Fin 11, (i.insertNth t y j)^2) = t^2+∑ j : Fin 10, (y j)^2 := by
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have h2 : (∑ j : Fin 11, (Fin.cons t y j)^2) = t^2+∑ j : Fin 10, (y j)^2 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  unfold euclideanProfile
  rw [h1, h2]

#print axioms labelProbability_hasSum
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
