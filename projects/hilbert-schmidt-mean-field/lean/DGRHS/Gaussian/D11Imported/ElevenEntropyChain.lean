import DGRHS.Gaussian.D11Imported.ElevenLabelDefinitions
import DGRHS.Gaussian.D11Imported.ElevenEuclideanEntropy
import DGRHS.Gaussian.D11Imported.ElevenPeriodizedMass
import DGRHS.Gaussian.D11Imported.PeriodizationIntegral

/-! Absolute-integral justification of the actual conditional entropy chain rule. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma conditionalLabel_pos (y : Fin 11 → ℝ) (n : Frequency 11) :
    0 < conditionalLabel y n :=
  div_pos (euclideanProfile_pos _) (periodizedProfile_pos _)

lemma conditionalLabel_summable (y : Fin 11 → ℝ) : Summable (conditionalLabel y) :=
  (translated_profile_summable y).div_const _

lemma conditionalLabel_mass {y : Fin 11 → ℝ} (hy : y ∈ labelCube) :
    (∑' n : Frequency 11, conditionalLabel y n) = 1 := by
  unfold conditionalLabel
  rw [tsum_div_const, ← periodizedProfile_on_cube hy]
  exact div_self (periodizedProfile_pos _).ne'

lemma profile_entropy_measurable :
    Measurable (fun x : Fin 11 → ℝ => euclideanProfile x * Real.log (euclideanProfile x)) :=
  euclideanProfile_continuous.measurable.mul euclideanProfile_continuous.measurable.log

lemma periodized_entropy_measurable :
    Measurable (fun x => periodizedProfile x * Real.log (periodizedProfile x)) :=
  periodizedProfile_measurable.mul periodizedProfile_measurable.log

lemma periodized_entropy_on_cube_integrable :
    IntegrableOn (fun y : Fin 11 → ℝ =>
      periodizedProfile (fun i => (y i : UnitAddCircle)) *
        Real.log (periodizedProfile (fun i => (y i : UnitAddCircle)))) labelCube :=
  (PeriodizationCube.quotient_measurePreserving 11).integrable_comp_of_integrable
    competitorDensity_finiteEntropy

lemma periodized_entropy_on_cube :
    (∫ y in labelCube, periodizedProfile (fun i => (y i : UnitAddCircle)) *
      Real.log (periodizedProfile (fun i => (y i : UnitAddCircle)))) = entropy competitorDensity := by
  have hm := PeriodizationCube.quotient_measurePreserving 11
  change MeasurePreserving (fun x : Fin 11 → ℝ => fun i => (x i : UnitAddCircle))
    (volume.restrict labelCube) (torusMeasure 11) at hm
  have h := integral_map (μ := volume.restrict labelCube) hm.measurable.aemeasurable
    periodized_entropy_measurable.aestronglyMeasurable
  rw [hm.map_eq] at h
  exact h.symm

lemma conditional_entropy_pointwise {y : Fin 11 → ℝ} (hy : y ∈ labelCube)
    (hf : Summable (fun n : Frequency 11 =>
      euclideanProfile (fun i => y i+(n i:ℝ)) * Real.log (euclideanProfile (fun i => y i+(n i:ℝ))))) :
    Summable (fun n : Frequency 11 => conditionalLabel y n * Real.log (conditionalLabel y n)) ∧
      periodizedProfile (fun i => (y i : UnitAddCircle)) *
        (∑' n : Frequency 11, conditionalLabel y n * Real.log (conditionalLabel y n)) =
      (∑' n : Frequency 11, euclideanProfile (fun i => y i+(n i:ℝ)) *
        Real.log (euclideanProfile (fun i => y i+(n i:ℝ)))) -
        periodizedProfile (fun i => (y i : UnitAddCircle)) *
          Real.log (periodizedProfile (fun i => (y i : UnitAddCircle))) := by
  let R := periodizedProfile (fun i => (y i : UnitAddCircle))
  have hR : 0 < R := periodizedProfile_pos _
  have he (n : Frequency 11) : conditionalLabel y n * Real.log (conditionalLabel y n) =
      (euclideanProfile (fun i => y i+(n i:ℝ)) * Real.log (euclideanProfile (fun i => y i+(n i:ℝ))) -
        euclideanProfile (fun i => y i+(n i:ℝ)) * Real.log R) / R := by
    unfold conditionalLabel
    change (_/R)*Real.log (_/R) = _
    rw [Real.log_div (euclideanProfile_pos _).ne' hR.ne']
    ring
  have hs := (translated_profile_summable y).mul_right (Real.log R)
  constructor
  · simpa only [he] using (hf.sub hs).div_const R
  · simp_rw [he]
    rw [tsum_div_const, hf.tsum_sub hs, tsum_mul_right, ← periodizedProfile_on_cube hy]
    change R*((_ - R*Real.log R)/R) = _
    field_simp
    rfl

lemma conditional_entropy_identity_ae :
    (fun y : Fin 11 → ℝ => periodizedProfile (fun i => (y i : UnitAddCircle)) *
      ∑' n : Frequency 11, conditionalLabel y n * Real.log (conditionalLabel y n))
      =ᵐ[volume.restrict labelCube]
    (fun y => (∑' n : Frequency 11, euclideanProfile (fun i => y i+(n i:ℝ)) *
      Real.log (euclideanProfile (fun i => y i+(n i:ℝ)))) -
      periodizedProfile (fun i => (y i : UnitAddCircle)) *
        Real.log (periodizedProfile (fun i => (y i : UnitAddCircle)))) := by
  filter_upwards [ae_restrict_mem (PeriodizationCube.cube_measurable 11),
    PeriodizationCube.translated_summable_ae 11 _ profile_entropy_measurable
      euclideanProfile_entropy_integrable] with y hy hsum
  exact (conditional_entropy_pointwise hy hsum).2

lemma conditional_entropy_integrable :
    IntegrableOn (fun y : Fin 11 → ℝ => periodizedProfile (fun i => (y i : UnitAddCircle)) *
      ∑' n : Frequency 11, conditionalLabel y n * Real.log (conditionalLabel y n)) labelCube := by
  have h := (PeriodizationCube.periodization_integrable 11 _ profile_entropy_measurable
    euclideanProfile_entropy_integrable).sub periodized_entropy_on_cube_integrable
  exact h.congr conditional_entropy_identity_ae.symm

lemma periodization_entropy_identity :
    entropy competitorDensity =
      (∫ x : Fin 11 → ℝ, euclideanProfile x * Real.log (euclideanProfile x)) +
        conditionalLabelEntropy := by
  unfold conditionalLabelEntropy
  have hsum : IntegrableOn (fun y : Fin 11 → ℝ => ∑' n : Frequency 11,
      euclideanProfile (fun i => y i+(n i:ℝ)) * Real.log (euclideanProfile (fun i => y i+(n i:ℝ)))) labelCube :=
    PeriodizationCube.periodization_integrable 11 _ profile_entropy_measurable euclideanProfile_entropy_integrable
  have he : (∫ y in labelCube, ∑' n : Frequency 11,
      euclideanProfile (fun i => y i+(n i:ℝ)) * Real.log (euclideanProfile (fun i => y i+(n i:ℝ)))) =
      ∫ x : Fin 11 → ℝ, euclideanProfile x * Real.log (euclideanProfile x) :=
    PeriodizationCube.unfold_integral 11 _ profile_entropy_measurable euclideanProfile_entropy_integrable
  rw [integral_congr_ae conditional_entropy_identity_ae,
    integral_sub hsum periodized_entropy_on_cube_integrable, he, periodized_entropy_on_cube]
  ring

#print axioms periodization_entropy_identity
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
