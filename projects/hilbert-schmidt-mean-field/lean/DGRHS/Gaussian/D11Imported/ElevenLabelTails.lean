import DGRHS.Gaussian.D11Imported.ElevenCoordinateTail
import DGRHS.Gaussian.D11Imported.ElevenLabelSeries
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma coordinateLabel_positive_tail_summable (k : ℕ) :
    Summable (fun m : ℕ => coordinateLabelProbability ((m+k+1:ℕ):ℤ)) :=
  coordinateLabelProbability_hasSum.summable.comp_injective (by
    intro a b h
    dsimp only at h
    have h' : a+k+1=b+k+1 := by exact_mod_cast h
    omega)

lemma coordinateLabel_positive_tail (k : ℕ) :
    (∑' m : ℕ, coordinateLabelProbability ((m+k+1:ℕ):ℤ)) =
      ∫ t in Ioi ((k:ℝ)+1/2), coordinateProfile t := by
  have hcell (m : ℕ) : coordinateLabelProbability ((m+k+1:ℕ):ℤ) =
      ∫ t in ((m:ℝ)+(k:ℝ)+1/2)..((m+1:ℕ):ℝ)+(k:ℝ)+1/2, coordinateProfile t := by
    rw [coordinateLabelProbability_interval]
    congr 1 <;> push_cast <;> ring
  have hsum (N : ℕ) : (∑ m ∈ Finset.range N, coordinateLabelProbability ((m+k+1:ℕ):ℤ)) =
      ∫ t in ((k:ℝ)+1/2)..((N:ℝ)+(k:ℝ)+1/2), coordinateProfile t := by
    simp_rw [hcell]
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n : ℕ => (n:ℝ)+(k:ℝ)+1/2) (n := N)
      (fun _ _ => coordinateProfile_integrable.intervalIntegrable)
    simpa using h
  have ht : Tendsto (fun N : ℕ => (N:ℝ)+(k:ℝ)+1/2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hlim := intervalIntegral_tendsto_integral_Ioi ((k:ℝ)+1/2)
    coordinateProfile_integrable.integrableOn ht
  have hlim' : Tendsto (fun N => ∑ m ∈ Finset.range N, coordinateLabelProbability ((m+k+1:ℕ):ℤ))
      atTop (𝓝 (∫ t in Ioi ((k:ℝ)+1/2), coordinateProfile t)) := by
    simpa only [hsum] using hlim
  exact tendsto_nhds_unique (coordinateLabel_positive_tail_summable k).hasSum.tendsto_sum_nat hlim'

lemma coordinateLabel_positive_tail_bound (k : ℕ) :
    (∑' m : ℕ, coordinateLabelProbability ((m+k+1:ℕ):ℤ)) ≤
      (1280/(693*Real.pi*25^6)) * (((k:ℝ)+1/2)^11)⁻¹ := by
  rw [coordinateLabel_positive_tail]
  simpa only [zpow_neg, zpow_ofNat] using coordinateProfile_tail (by positivity : (0:ℝ)<(k:ℝ)+1/2)

lemma shifted_inverse_summable : Summable (fun k : ℕ => (((k:ℝ)+1/2)^11)⁻¹) := by
  have ho := eleven_inverse_summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2*n+1) by intro a b h; dsimp only at h; omega)
  apply (ho.mul_left (2048:ℝ)).congr
  intro k
  have heq : (k:ℝ)+1/2 = (((2*k+1:ℕ):ℝ))/2 := by push_cast; ring
  rw [heq, div_pow, inv_div]
  norm_num
  ring

lemma coordinateLabel_tail_series_summable :
    Summable (fun k : ℕ => ∑' m : ℕ, coordinateLabelProbability ((m+k+1:ℕ):ℤ)) := by
  apply (shifted_inverse_summable.mul_left (1280/(693*Real.pi*25^6))).of_nonneg_of_le
  · intro k
    exact tsum_nonneg (fun _ => coordinateLabelProbability_nonneg _)
  · exact coordinateLabel_positive_tail_bound

lemma coordinateLabel_tail_series_bound :
    (∑' k : ℕ, ∑' m : ℕ, coordinateLabelProbability ((m+k+1:ℕ):ℤ)) <
      (1280/(693*Real.pi*25^6)) * (2047*1025/1024) := by
  calc
    _ ≤ ∑' k : ℕ, (1280/(693*Real.pi*25^6)) * (((k:ℝ)+1/2)^11)⁻¹ :=
      coordinateLabel_tail_series_summable.tsum_le_tsum coordinateLabel_positive_tail_bound
        (shifted_inverse_summable.mul_left _)
    _ = (1280/(693*Real.pi*25^6)) * (∑' k : ℕ, (((k:ℝ)+1/2)^11)⁻¹) := tsum_mul_left
    _ < _ := mul_lt_mul_of_pos_left eleven_shifted_series_bound (by positivity)

#print axioms coordinateLabel_tail_series_bound
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
