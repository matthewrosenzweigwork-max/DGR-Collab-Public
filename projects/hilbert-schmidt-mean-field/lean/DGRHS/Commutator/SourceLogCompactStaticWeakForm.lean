import DGRHS.Commutator.SourceLogCompactC2Limit

/-! RECORDS-ONLY / UNCOMPILED. Every-time compact C2 integrated weak testing
implies the existing every-time bounded C2 integrated weak class. Only
probability of each actual time slice is added to the compact weak class.
There is no density upper bound, moment, law continuity, time-space joint
measurability, force integrability, or desired bounded-C2 identity premise.
This does not convert compact C-infinity testing to compact C2 testing and
does not reconstruct a representative from a distributional PDE. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The starting compact-test identity, with actual every-time traces. -/
def SourceLogCompactStaticWeakMeanField (β T : ℝ) (ρ : ℝ → E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
    IntervalIntegrable (fun r => sourceLogStaticMeanTestDrift β (ρ r) ψ) volume 0 T ∧
    ∀ r ∈ Icc 0 T,
      (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ r)) =
        (∫ x, ψ x ∂gaussianRieszDensityMeasure (ρ 0)) +
          ∫ u in 0..r, sourceLogStaticMeanTestDrift β (ρ u) ψ

/-- Separate proper time-DCT step; time measurability follows from the
compact drifts, rather than being an additional trajectory hypothesis. -/
lemma SourceLogCompactC2Approximation.time_limit
    {φ : E → ℝ} (a : SourceLogCompactC2Approximation φ)
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t)))
    (hi : ∀ n, IntervalIntegrable
      (fun t => sourceLogStaticMeanTestDrift β (ρ t) (a.test n)) volume 0 T)
    (r : ℝ) (hr : r ∈ Icc 0 T) :
    IntervalIntegrable (fun t => sourceLogStaticMeanTestDrift β (ρ t) φ) volume 0 r ∧
    Tendsto (fun n => ∫ t in 0..r, sourceLogStaticMeanTestDrift β (ρ t) (a.test n))
      atTop (𝓝 (∫ t in 0..r, sourceLogStaticMeanTestDrift β (ρ t) φ)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 r)
  have hsub : Ioc 0 r ⊆ Ioc 0 T := fun t ht => ⟨ht.1,ht.2.trans hr.2⟩
  have him n : AEStronglyMeasurable
      (fun t => sourceLogStaticMeanTestDrift β (ρ t) (a.test n)) μ :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hi n)).mono_set hsub).1
  have hb n : ∀ᵐ t ∂μ,
      ‖sourceLogStaticMeanTestDrift β (ρ t) (a.test n)‖ ≤
        |β⁻¹| * ((Fintype.card ι : ℝ)*a.bound)+(1/2:ℝ)*a.bound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    letI := hprob t ⟨ht.1.le,ht.2.trans hr.2⟩
    simpa only [Real.norm_eq_abs] using a.drift_bound β (ρ t) n
  have hl : ∀ᵐ t ∂μ,
      Tendsto (fun n => sourceLogStaticMeanTestDrift β (ρ t) (a.test n))
        atTop (𝓝 (sourceLogStaticMeanTestDrift β (ρ t) φ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    letI := hprob t ⟨ht.1.le,ht.2.trans hr.2⟩
    exact a.drift_tendsto β (ρ t)
  obtain ⟨hproper,hlim⟩ := sourceLog_integrable_tendsto_of_bounded μ
    (fun n t => sourceLogStaticMeanTestDrift β (ρ t) (a.test n))
    (fun t => sourceLogStaticMeanTestDrift β (ρ t) φ) _ him hb hl
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).mpr hproper,?_⟩
  simpa only [intervalIntegral.integral_of_le hr.1] using hlim

/-- No desired bounded-test weak identity is a premise. -/
theorem SourceLogCompactStaticWeakMeanField.to_bounded
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hweak : SourceLogCompactStaticWeakMeanField β T ρ) :
    SourceLogStaticWeakMeanField β T ρ := by
  intro φ hφ
  obtain ⟨a⟩ := exists_sourceLogCompactC2Approximation φ hφ
  have hc n := hweak (a.test n) (a.smooth n) (a.compact n)
  have ht := a.time_limit β T hT ρ hprob (fun n => (hc n).1)
  refine ⟨(ht T ⟨hT,le_rfl⟩).1,?_⟩
  intro r hr
  letI := hprob r hr
  letI := hprob 0 ⟨le_rfl,hT⟩
  have hleft := (a.spatial_limits (gaussianRieszDensityMeasure (ρ r))).1
  have hright := ((a.spatial_limits (gaussianRieszDensityMeasure (ρ 0))).1).add
    (ht r hr).2
  have hsame : (fun n => (∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ 0)) +
      ∫ t in 0..r, sourceLogStaticMeanTestDrift β (ρ t) (a.test n)) =
      (fun n => ∫ x, a.test n x ∂gaussianRieszDensityMeasure (ρ r)) := by
    funext n
    exact ((hc n).2 r hr).symm
  rw [hsame] at hright
  exact tendsto_nhds_unique hleft hright

end DGRHS.Commutator
