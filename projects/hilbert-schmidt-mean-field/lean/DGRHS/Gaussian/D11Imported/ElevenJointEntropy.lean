import DGRHS.Gaussian.D11Imported.ElevenLabelExpectations
import DGRHS.Gaussian.D11Imported.ElevenLabelMoment
import DGRHS.Gaussian.D11Imported.CountableProductLaw

/-! Entropy subadditivity for the actual eleven-dimensional lattice-label law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma coordinateLabelProbability_pos (n : ℤ) : 0 < coordinateLabelProbability n := by
  rw [coordinateLabelProbability_interval]
  apply intervalIntegral.integral_pos (by linarith) coordinateProfile_continuous.continuousOn
    (fun t _ => (coordinateProfile_pos t).le)
  exact ⟨(n:ℝ), ⟨by linarith, by linarith⟩, coordinateProfile_pos _⟩

lemma coordinateLabel_log_summable :
    Summable (fun n : ℤ => coordinateLabelProbability n * ‖Real.log (coordinateLabelProbability n)‖) := by
  have h := coordinateLabel_entropy_lt.1.norm
  simpa only [norm_mul, Real.norm_of_nonneg (coordinateLabelProbability_nonneg _)] using h

lemma label_product_cross_summable :
    Summable (fun n : Frequency 11 => labelProbability n *
      Real.log (∏ i : Fin 11, coordinateLabelProbability (n i))) := by
  have he (n : Frequency 11) : labelProbability n *
      Real.log (∏ i : Fin 11, coordinateLabelProbability (n i)) =
      ∑ i : Fin 11, labelProbability n * Real.log (coordinateLabelProbability (n i)) := by
    rw [Real.log_prod (fun i _ => (coordinateLabelProbability_pos _).ne'), Finset.mul_sum]
  simp_rw [he]
  exact summable_sum (fun i _ => (label_coordinate_expectation i _ coordinateLabel_log_summable).1)

lemma label_product_cross_sum :
    (∑' n : Frequency 11, labelProbability n *
      Real.log (∏ i : Fin 11, coordinateLabelProbability (n i))) =
      11 * (∑' n : ℤ, coordinateLabelProbability n * Real.log (coordinateLabelProbability n)) := by
  have he (n : Frequency 11) : labelProbability n *
      Real.log (∏ i : Fin 11, coordinateLabelProbability (n i)) =
      ∑ i : Fin 11, labelProbability n * Real.log (coordinateLabelProbability (n i)) := by
    rw [Real.log_prod (fun i _ => (coordinateLabelProbability_pos _).ne'), Finset.mul_sum]
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun i _ =>
    (label_coordinate_expectation i _ coordinateLabel_log_summable).1)]
  simp_rw [(label_coordinate_expectation _ _ coordinateLabel_log_summable).2]
  simp

lemma labelEntropy_subadditive :
    Summable (fun n : Frequency 11 => labelProbability n * Real.log (labelProbability n)) ∧
      labelEntropy ≤ 11 * (-(∑' n : ℤ,
        coordinateLabelProbability n * Real.log (coordinateLabelProbability n))) := by
  have h := CountableShannon.entropy_comparison labelProbability
    (fun n : Frequency 11 => ∏ i : Fin 11, coordinateLabelProbability (n i))
    labelProbability_nonneg (fun n => Finset.prod_pos (fun _ _ => coordinateLabelProbability_pos _))
    labelProbability_hasSum (CountableShannon.product_probability_hasSum coordinateLabelProbability
      coordinateLabelProbability_nonneg coordinateLabelProbability_hasSum 11) label_product_cross_summable
  refine ⟨h.1, ?_⟩
  rw [label_product_cross_sum] at h
  exact h.2.trans_eq (by ring)

lemma labelEntropy_lt : labelEntropy < (1/600:ℝ) :=
  labelEntropy_subadditive.2.trans_lt coordinateLabel_entropy_lt.2

#print axioms labelEntropy_subadditive
#print axioms labelEntropy_lt
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
