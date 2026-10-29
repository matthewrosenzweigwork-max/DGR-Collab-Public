import DGRHS.Gaussian.D11Imported.ElevenEntropyChain
import DGRHS.Gaussian.D11Imported.ElevenJointEntropy
import DGRHS.Gaussian.D11Imported.CountableIntegral

/-! Nonnegativity of mutual information for the genuine lattice decomposition,
including absolute-integral justification for the countable cross entropy. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma labelCube_volume : (volume : Measure (Fin 11 → ℝ)) labelCube = 1 := by
  change (Measure.pi (fun _ : Fin 11 => (volume : Measure ℝ)))
    (univ.pi (fun _ => Ico (-(1/2:ℝ)) (1/2))) = 1
  rw [Measure.pi_pi]
  norm_num [Real.volume_Ico]

lemma labelProbability_pos (n : Frequency 11) : 0 < labelProbability n := by
  unfold labelProbability
  rw [integral_pos_iff_support_of_nonneg (fun y => (euclideanProfile_pos _).le)
    (translated_euclideanProfile_integrable n).integrableOn]
  have hs : Function.support (fun y : Fin 11 → ℝ => euclideanProfile (fun i => y i+(n i:ℝ))) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (euclideanProfile_pos _).ne'
  rw [hs, Measure.restrict_apply_univ, labelCube_volume]
  norm_num

def labelLogIntegrand (n : Frequency 11) (y : Fin 11 → ℝ) : ℝ :=
  euclideanProfile (fun i => y i+(n i:ℝ)) * Real.log (labelProbability n)

lemma labelLogIntegrand_measurable (n : Frequency 11) : Measurable (labelLogIntegrand n) := by
  exact (euclideanProfile_continuous.measurable.comp (by fun_prop)).mul_const _

lemma labelLogIntegrand_integrable (n : Frequency 11) :
    IntegrableOn (labelLogIntegrand n) labelCube :=
  (translated_euclideanProfile_integrable n).integrableOn.mul_const _

lemma labelLogIntegrand_integral (n : Frequency 11) :
    (∫ y in labelCube, labelLogIntegrand n y) = labelProbability n * Real.log (labelProbability n) := by
  unfold labelLogIntegrand
  rw [integral_mul_const]
  rfl

lemma labelLogIntegrand_norm_integral (n : Frequency 11) :
    (∫ y in labelCube, ‖labelLogIntegrand n y‖) = ‖labelProbability n * Real.log (labelProbability n)‖ := by
  simp only [labelLogIntegrand, norm_mul, Real.norm_of_nonneg (euclideanProfile_pos _).le,
    Real.norm_of_nonneg (labelProbability_nonneg n)]
  rw [integral_mul_const]
  rfl

lemma labelLogIntegrand_norm_summable :
    Summable (fun n : Frequency 11 => ∫ y in labelCube, ‖labelLogIntegrand n y‖) := by
  simpa only [labelLogIntegrand_norm_integral] using labelEntropy_subadditive.1.norm

lemma labelLogIntegrand_series :
    (∀ᵐ y ∂volume.restrict labelCube, Summable (fun n => labelLogIntegrand n y)) ∧
      IntegrableOn (fun y => ∑' n, labelLogIntegrand n y) labelCube :=
  CountableIntegral.series_integrable_ae _ _ labelLogIntegrand_measurable
    (CountableIntegral.sum_lintegral_enorm_ne_top _ _ labelLogIntegrand_integrable labelLogIntegrand_norm_summable)

lemma labelLogIntegrand_series_integral :
    (∫ y in labelCube, ∑' n, labelLogIntegrand n y) =
      ∑' n, labelProbability n * Real.log (labelProbability n) := by
  rw [← integral_tsum_of_summable_integral_norm labelLogIntegrand_integrable labelLogIntegrand_norm_summable]
  simp_rw [labelLogIntegrand_integral]

lemma conditional_cross_term (y : Fin 11 → ℝ) (n : Frequency 11) :
    conditionalLabel y n * Real.log (labelProbability n) =
      labelLogIntegrand n y / periodizedProfile (fun i => (y i : UnitAddCircle)) := by
  unfold conditionalLabel labelLogIntegrand
  ring

lemma conditionalLabelEntropy_le_labelEntropy : conditionalLabelEntropy ≤ labelEntropy := by
  have hae : ∀ᵐ y ∂volume.restrict labelCube,
      (∑' n, labelLogIntegrand n y) ≤
      periodizedProfile (fun i => (y i : UnitAddCircle)) *
        (∑' n : Frequency 11, conditionalLabel y n * Real.log (conditionalLabel y n)) := by
    filter_upwards [ae_restrict_mem (PeriodizationCube.cube_measurable 11), labelLogIntegrand_series.1] with y hy hs
    have hmass : HasSum (conditionalLabel y) 1 :=
      (conditionalLabel_mass hy) ▸ (conditionalLabel_summable y).hasSum
    have hcross : Summable (fun n => conditionalLabel y n * Real.log (labelProbability n)) := by
      simp_rw [conditional_cross_term]
      exact hs.div_const _
    have h := CountableShannon.entropy_comparison (conditionalLabel y) labelProbability
      (fun n => (conditionalLabel_pos y n).le) labelProbability_pos hmass labelProbability_hasSum hcross
    have hm := mul_le_mul_of_nonneg_left (neg_le_neg_iff.mp h.2)
      (periodizedProfile_pos (fun i => (y i : UnitAddCircle))).le
    simp_rw [conditional_cross_term] at hm
    rw [tsum_div_const, mul_div_cancel₀ _ (periodizedProfile_pos _).ne'] at hm
    exact hm
  have hint := integral_mono_ae labelLogIntegrand_series.2 conditional_entropy_integrable hae
  rw [labelLogIntegrand_series_integral] at hint
  exact neg_le_neg hint

lemma conditionalLabelEntropy_lt : conditionalLabelEntropy < (1/600:ℝ) :=
  conditionalLabelEntropy_le_labelEntropy.trans_lt labelEntropy_lt

lemma competitor_entropy_bound : entropy competitorDensity < (8653/600:ℝ) := by
  rw [periodization_entropy_identity]
  linarith [euclideanProfile_entropy_lt, conditionalLabelEntropy_lt]

lemma competitor_entropy_fine : entropy competitorDensity <
    (7305164/10^6 + 17897/2520 + 1/600:ℝ) := by
  rw [periodization_entropy_identity]
  linarith [euclideanProfile_entropy_fine, conditionalLabelEntropy_lt]

theorem competitor_entropy (ρ : ProbabilityDensity 11) (hρ : ρ.value = periodizedProfile) :
    entropy ρ < (8653/600:ℝ) := by
  have he : entropy ρ = entropy competitorDensity := by unfold entropy; rw [hρ]; rfl
  rw [he]
  exact competitor_entropy_bound

#print axioms conditionalLabelEntropy_le_labelEntropy
#print axioms competitor_entropy
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
