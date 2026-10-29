import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace DGRHS.Gaussian.D11Imported.CountableIntegral

lemma sum_lintegral_enorm_ne_top {ι α : Type*} [Countable ι] [MeasurableSpace α]
    (μ : Measure α) (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    (∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ) ≠ ⊤ := by
  have he (i : ι) : (∫⁻ x, ‖f i x‖ₑ ∂μ) = ENNReal.ofReal (∫ x, ‖f i x‖ ∂μ) := by
    simpa only [ofReal_norm] using (ofReal_integral_eq_lintegral_ofReal (hf i).norm
      (ae_of_all _ (fun x => norm_nonneg (f i x)))).symm
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (fun x => norm_nonneg (f i x))) hs]
  exact ENNReal.ofReal_ne_top

lemma series_integrable_ae {ι α : Type*} [Countable ι] [MeasurableSpace α]
    (μ : Measure α) (f : ι → α → ℝ) (hm : ∀ i, Measurable (f i))
    (hn : (∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ) ≠ ⊤) :
    (∀ᵐ x ∂μ, Summable (fun i => f i x)) ∧ Integrable (fun x => ∑' i, f i x) μ := by
  have hnorm : (∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ) ≠ ⊤ := by
    rwa [lintegral_tsum (fun i => (hm i).enorm.aemeasurable)]
  constructor
  · have ha := ae_lt_top' (Measurable.tsum (fun i => (hm i).enorm)).aemeasurable hnorm
    filter_upwards [ha] with x hx
    exact (tsum_enorm_ne_top_iff_summable_norm.mp hx.ne).of_norm
  · refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)) hnorm.lt_top

#print axioms series_integrable_ae
end DGRHS.Gaussian.D11Imported.CountableIntegral
