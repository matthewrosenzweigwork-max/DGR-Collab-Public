import DGRHS.Gaussian.PeriodicHeatTimeEnvelope

/-! The translated Mellin weight for genuine heat regularization. Its
 domination is uniform in the heat parameter, including the zero limit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic

def periodicHeatMellinWeight (p τ s : ℝ) : ℝ :=
  (Ioi τ).indicator (fun s => (s-τ)^p) s

lemma periodicHeatMellinWeight_measurable (p τ : ℝ) :
    Measurable (periodicHeatMellinWeight p τ) := by
  unfold periodicHeatMellinWeight
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

lemma periodicHeatMellinWeight_nonneg (p τ s : ℝ) : 0≤periodicHeatMellinWeight p τ s := by
  unfold periodicHeatMellinWeight
  by_cases h : s∈Ioi τ
  · rw [indicator_of_mem h]
    exact Real.rpow_nonneg (sub_nonneg.mpr h.le) _
  · rw [indicator_of_notMem h]

lemma periodicHeatMellinWeight_le (p τ s : ℝ) (hp : 0≤p) (hτ : 0≤τ) (hs : 0≤s) :
    periodicHeatMellinWeight p τ s≤s^p := by
  unfold periodicHeatMellinWeight
  by_cases h : s∈Ioi τ
  · rw [indicator_of_mem h]
    exact Real.rpow_le_rpow (sub_nonneg.mpr h.le) (sub_le_self _ hτ) hp
  · rw [indicator_of_notMem h]
    exact Real.rpow_nonneg hs _

lemma periodicHeatMellinWeight_zero (p s : ℝ) (hs : 0<s) :
    periodicHeatMellinWeight p 0 s=s^p := by
  rw [periodicHeatMellinWeight,indicator_of_mem (show s∈Ioi 0 from hs),sub_zero]

lemma periodicHeatMellinWeight_tendsto (p s : ℝ) (hs : 0<s) :
    Tendsto (fun τ : ℝ => periodicHeatMellinWeight p τ s) (𝓝 0) (𝓝 (s^p)) := by
  have hc : ContinuousAt (fun τ : ℝ => (s-τ)^p) 0 :=
    (Real.continuousAt_rpow_const (s-0) p (Or.inl (by simpa using ne_of_gt hs))).comp
      (show ContinuousAt (fun τ : ℝ => s-τ) 0 from (continuous_const.sub continuous_id).continuousAt)
  apply (show Tendsto (fun τ : ℝ => (s-τ)^p) (𝓝 0) (𝓝 (s^p)) from by simpa using hc.tendsto).congr'
  filter_upwards [eventually_lt_nhds hs] with τ hτ
  rw [periodicHeatMellinWeight,indicator_of_mem (show s∈Ioi τ from hτ)]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatMellinWeight_le
#print axioms DGRHS.Periodic.periodicHeatMellinWeight_tendsto
