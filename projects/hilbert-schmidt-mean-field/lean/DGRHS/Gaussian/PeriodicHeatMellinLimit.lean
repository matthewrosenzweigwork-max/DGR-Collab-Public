import DGRHS.Gaussian.PeriodicHeatMellinComparison

/-! Actual almost-everywhere heat-parameter convergence by dominated
convergence on the same proper time sections used for the comparison. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicMellinHeatGreen_tendsto (p : ℝ) (hp : 0≤p) (x : PeriodicTorus ι)
    (hx : IntegrableOn (fun s => periodicMellinHeatIntegrand p 0 s x) (Ioi 0)) :
    Tendsto (fun τ : ℝ => periodicMellinHeatGreen p τ x) (𝓝[Ici 0] 0)
      (𝓝 (periodicMellinHeatGreen p 0 x)) := by
  have hlim : Tendsto (fun τ : ℝ => ∫ s : ℝ in Ioi 0,periodicMellinHeatIntegrand p τ s x)
      (𝓝[Ici 0] 0) (𝓝 (∫ s : ℝ in Ioi 0,periodicMellinHeatIntegrand p 0 s x)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun s => ‖periodicMellinHeatIntegrand p 0 s x‖)
    · exact Eventually.of_forall (fun τ => ((periodicMellinHeatIntegrand_measurable p τ).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact periodicMellinHeatIntegrand_norm_le_zero p τ s hp hτ hs x
    · exact hx.norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have ht := ((Complex.continuous_ofReal.tendsto (s^p)).comp (periodicHeatMellinWeight_tendsto p s hs)).mul_const
        (periodicGaussianHeat s x-1)
      simpa only [Function.comp_def,periodicMellinHeatIntegrand,periodicHeatMellinWeight_zero p s hs] using
        ht.mono_left nhdsWithin_le_nhds
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hlim
  simpa only [Function.comp_def,← periodicMellinHeatGreen_coe_integral,Complex.ofReal_re] using hr

/-- The parameter limit holds for the actual integral, on a common Haar-full set. -/
theorem periodicMellinHeatGreen_tendsto_ae (p : ℝ) (hp : 0≤p) :
    ∀ᵐ x ∂periodicHaar ι,Tendsto (fun τ : ℝ => periodicMellinHeatGreen p τ x) (𝓝[Ici 0] 0)
      (𝓝 (periodicMellinHeatGreen p 0 x)) := by
  filter_upwards [(periodicMellinHeatIntegrand_product_integrable (ι := ι) p 0 hp le_rfl).prod_left_ae] with x hx
  exact periodicMellinHeatGreen_tendsto p hp x hx

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicMellinHeatGreen_tendsto_ae
#check @DGRHS.Periodic.periodicMellinHeatGreen_tendsto_ae
