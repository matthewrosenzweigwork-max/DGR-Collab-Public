import DGRHS.Gaussian.PeriodicHeatRegularizationFourier

/-! The source-normalized comparison and parameter limit, on a single Haar
full-measure set, transported to every genuine particle difference. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatComparisonConstant (ι : Type u) [Fintype ι] : ℝ :=
  periodicHeatMellinFactor ι*periodicHeatMellinComparisonConstant ι (periodicHeatMellinExponent ι)

lemma periodicHeatComparisonConstant_nonneg : 0≤periodicHeatComparisonConstant ι := by
  apply mul_nonneg periodicHeatMellinFactor_pos.le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_nonneg (Real.rpow_nonneg hs.le _) (periodicHeatTimeEnvelope_nonneg s)

/-- Both conclusions hold on the same set, independently of the heat time. -/
theorem periodicHeatRegularizedGreen_good_ae (hd : 2≤Fintype.card ι) :
    ∀ᵐ x ∂periodicHaar ι,
      (∀ τ : ℝ,0≤τ → periodicHeatRegularizedGreen τ x≤periodicLogKernel x+periodicHeatComparisonConstant ι) ∧
      Tendsto (fun τ : ℝ => periodicHeatRegularizedGreen τ x) (𝓝[Ici 0] 0) (𝓝 (periodicLogKernel x)) := by
  have hp := periodicHeatMellinExponent_nonneg hd
  filter_upwards [periodicMellinHeatGreen_comparison_ae _ hp,periodicMellinHeatGreen_tendsto_ae _ hp,
    periodicHeatRegularizedGreen_zero_eq_ae hd] with x hcomp hlim hzero
  constructor
  · intro τ hτ
    have h := mul_le_mul_of_nonneg_left (hcomp τ hτ) (periodicHeatMellinFactor_pos (ι := ι)).le
    rw [mul_add] at h
    change periodicHeatRegularizedGreen τ x≤periodicHeatRegularizedGreen 0 x+periodicHeatComparisonConstant ι at h
    simpa only [hzero] using h
  · have h := hlim.const_mul (periodicHeatMellinFactor ι)
    change Tendsto (fun τ => periodicHeatRegularizedGreen τ x) (𝓝[Ici 0] 0) (𝓝 (periodicHeatRegularizedGreen 0 x)) at h
    simpa only [hzero] using h

theorem periodicHeatRegularizedGreen_particle_good_ae (hd : 2≤Fintype.card ι) (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus ι ∂Measure.pi (fun _ : Fin N => periodicHaar ι),
      ∀ i j : Fin N,i≠j →
        (∀ τ : ℝ,0≤τ → periodicHeatRegularizedGreen τ (x i-x j)≤
          periodicLogKernel (x i-x j)+periodicHeatComparisonConstant ι) ∧
        Tendsto (fun τ : ℝ => periodicHeatRegularizedGreen τ (x i-x j))
          (𝓝[Ici 0] 0) (𝓝 (periodicLogKernel (x i-x j))) := by
  have hp := (periodicHaar_preserving_difference (ι := ι)).quasiMeasurePreserving.ae
    (periodicHeatRegularizedGreen_good_ae hd)
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i=j
  · exact Eventually.of_forall (fun _ h => False.elim (h hij))
  · exact ((DGRHS.Decoupling.pair_eval_measurePreserving (periodicHaar ι) i j hij).quasiMeasurePreserving.ae hp).mono
      (fun _ hx _ => hx)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatRegularizedGreen_good_ae
#print axioms DGRHS.Periodic.periodicHeatRegularizedGreen_particle_good_ae
#check @DGRHS.Periodic.periodicHeatRegularizedGreen_good_ae
