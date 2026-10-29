import DGRHS.Gaussian.PeriodicHeatMellinIntegrable

/-! A common full-measure set supports every nonnegative heat parameter.
The regularization comparison follows from positivity of the actual heat
kernel and a proved, integrable negative-part envelope. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicMellinHeatIntegrand_norm_le_zero (p τ s : ℝ) (hp : 0≤p) (hτ : 0≤τ)
    (hs : 0<s) (x : PeriodicTorus ι) :
    ‖periodicMellinHeatIntegrand p τ s x‖≤‖periodicMellinHeatIntegrand p 0 s x‖ := by
  simp only [periodicMellinHeatIntegrand,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (periodicHeatMellinWeight_nonneg p τ s),
    Real.norm_of_nonneg (periodicHeatMellinWeight_nonneg p 0 s),periodicHeatMellinWeight_zero p s hs,Real.norm_of_nonneg (Real.rpow_nonneg hs.le p)]
  exact mul_le_mul_of_nonneg_right (periodicHeatMellinWeight_le p τ s hp hτ hs.le) (norm_nonneg _)

lemma periodicMellinHeatIntegrand_section_integrable (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ)
    (x : PeriodicTorus ι) (hx : IntegrableOn (fun s => periodicMellinHeatIntegrand p 0 s x) (Ioi 0)) :
    IntegrableOn (fun s => periodicMellinHeatIntegrand p τ s x) (Ioi 0) := by
  apply hx.norm.mono' ((periodicMellinHeatIntegrand_measurable p τ).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact periodicMellinHeatIntegrand_norm_le_zero p τ s hp hτ hs x

lemma periodicMellinHeatIntegrand_real_integrable (p τ : ℝ) (x : PeriodicTorus ι)
    (hx : IntegrableOn (fun s => periodicMellinHeatIntegrand p τ s x) (Ioi 0)) :
    IntegrableOn (fun s => periodicHeatMellinWeight p τ s*((periodicGaussianHeat s x).re-1)) (Ioi 0) := by
  have hi := hx.re
  change IntegrableOn (fun s => (periodicMellinHeatIntegrand p τ s x).re) (Ioi 0) at hi
  simpa only [periodicMellinHeatIntegrand,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.sub_re,Complex.one_re,zero_mul,sub_zero] using hi

def periodicHeatMellinComparisonConstant (ι : Type u) [Fintype ι] (p : ℝ) : ℝ :=
  ∫ s : ℝ in Ioi 0,s^p*periodicHeatTimeEnvelope ι s

lemma periodicMellinHeatGreen_le_zero_add (p τ : ℝ) (hp : 0≤p) (hτ : 0≤τ)
    (x : PeriodicTorus ι) (hx : IntegrableOn (fun s => periodicMellinHeatIntegrand p 0 s x) (Ioi 0)) :
    periodicMellinHeatGreen p τ x≤periodicMellinHeatGreen p 0 x+periodicHeatMellinComparisonConstant ι p := by
  have hi0 := periodicMellinHeatIntegrand_real_integrable p 0 x hx
  have hiτ := periodicMellinHeatIntegrand_real_integrable p τ x
    (periodicMellinHeatIntegrand_section_integrable p τ hp hτ x hx)
  have hbound := periodicHeatTimeEnvelope_weight_integrable (ι := ι) p (by linarith)
  have hle : (∫ s : ℝ in Ioi 0,
      periodicHeatMellinWeight p τ s*((periodicGaussianHeat s x).re-1)-
        periodicHeatMellinWeight p 0 s*((periodicGaussianHeat s x).re-1)) ≤
      periodicHeatMellinComparisonConstant ι p := by
    apply integral_mono_ae (hiτ.sub hi0) hbound
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    dsimp only [Pi.sub_apply]
    rw [periodicHeatMellinWeight_zero p s hs]
    have hw := periodicHeatMellinWeight_le p τ s hp hτ hs.le
    have hw0 := periodicHeatMellinWeight_nonneg p τ s
    have he0 := periodicHeatTimeEnvelope_nonneg (ι := ι) s
    have he := periodicGaussianHeat_centered_envelope_lower s hs x
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (by linarith : 0≤(periodicGaussianHeat s x).re-1+periodicHeatTimeEnvelope ι s),
      mul_nonneg hw0 he0]
  rw [integral_sub hiτ hi0] at hle
  change periodicMellinHeatGreen p τ x-periodicMellinHeatGreen p 0 x≤_ at hle
  linarith

/-- The common full-measure set is independent of the regularization time. -/
theorem periodicMellinHeatGreen_comparison_ae (p : ℝ) (hp : 0≤p) :
    ∀ᵐ x ∂periodicHaar ι,∀ τ : ℝ,0≤τ →
      periodicMellinHeatGreen p τ x≤periodicMellinHeatGreen p 0 x+periodicHeatMellinComparisonConstant ι p := by
  filter_upwards [(periodicMellinHeatIntegrand_product_integrable (ι := ι) p 0 hp le_rfl).prod_left_ae] with x hx
  exact fun τ hτ => periodicMellinHeatGreen_le_zero_add p τ hp hτ x hx

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicMellinHeatIntegrand_section_integrable
#print axioms DGRHS.Periodic.periodicMellinHeatGreen_comparison_ae
#check @DGRHS.Periodic.periodicMellinHeatGreen_comparison_ae
