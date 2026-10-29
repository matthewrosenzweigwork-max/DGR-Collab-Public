import DGRHS.Gaussian.PeriodicHeatPartitionLimit
import DGRHS.Gaussian.PeriodicDimensionThreshold

/-! Exact manuscript heat time and critical regularized-partition limit.
On the unit torus, the Laplacian multiplier is exp(-4*pi^2*t*|k|^2). -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicSourceHeatGreen (t : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicHeatRegularizedGreen (4*Real.pi^2*t) x

def periodicSourceHeatPartition (β t : ℝ) (N : ℕ) : ℝ≥0∞ :=
  periodicHeatAttractivePartition (ι := ι) β (4*Real.pi^2*t) N

lemma periodicSourceHeatGreen_fourierCoeff (hd : 2≤Fintype.card ι) (t : ℝ) (ht : 0≤t)
    (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicSourceHeatGreen t x:ℂ)) k =
      (Real.exp (-(4*Real.pi^2*t)*‖periodicFrequencyVector k‖^2):ℂ)*periodicLogFourierCoeff k :=
  periodicHeatRegularizedGreen_fourierCoeff hd _ (by positivity) k

lemma periodicSourceHeatTime_tendsto :
    Tendsto (fun t : ℝ => 4*Real.pi^2*t) (𝓝[Ici 0] 0) (𝓝[Ici 0] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun t : ℝ => 4*Real.pi^2*t) (𝓝 0) (𝓝 (4*Real.pi^2*0)) :=
      tendsto_id.const_mul _
    simpa only [mul_zero] using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0≤4*Real.pi^2*t
    exact mul_nonneg (by positivity) ht

theorem periodicSourceHeatPartition_tendsto (hd : 2≤Fintype.card ι) (β : ℝ) (hβ : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    Tendsto (fun t : ℝ => periodicSourceHeatPartition (ι := ι) β t N)
      (𝓝[Ici 0] 0) (𝓝 (periodicAttractivePartition (ι := ι) β N)) :=
  (periodicHeatAttractivePartition_tendsto hd β hβ hβd N hN).comp periodicSourceHeatTime_tendsto

/-- Exact source equation regularizedPartitionConvergence, with properness of
all nonnegative-time partitions and the true critical limit. -/
theorem periodic_critical_heat_partition_source (d : ℕ) (hd : 11≤d) (N : ℕ) (hN : 1≤N) :
    letI : NeZero d := ⟨by omega⟩
    (∀ t : ℝ,0≤t → periodicSourceHeatPartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) t N<∞) ∧
      Tendsto (fun t : ℝ => periodicSourceHeatPartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) t N)
        (𝓝[Ici 0] 0) (𝓝 (periodicAttractivePartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) N)) := by
  letI : NeZero d := ⟨by omega⟩
  have hd2 : 2≤Fintype.card (Fin d) := by simp only [Fintype.card_fin];omega
  have hβ := (periodicStabilityThreshold_pos (ι := Fin d)).le
  have hβd : periodicStabilityThreshold (Fin d)<2*(Fintype.card (Fin d):ℝ) := by
    simpa only [Fintype.card_fin] using periodicStabilityThreshold_lt_collision d hd
  exact ⟨fun t ht => periodicHeatAttractivePartition_finite hd2 _ _ hβ hβd (by positivity) N hN,
    periodicSourceHeatPartition_tendsto hd2 _ hβ hβd N hN⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicSourceHeatGreen_fourierCoeff
#print axioms DGRHS.Periodic.periodic_critical_heat_partition_source
#check @DGRHS.Periodic.periodic_critical_heat_partition_source
