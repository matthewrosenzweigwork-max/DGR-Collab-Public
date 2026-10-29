import DGRHS.Gaussian.PeriodicDimensionThreshold
import DGRHS.Gaussian.PeriodicCriticalPartitionLower
import DGRHS.Gaussian.PeriodicCollisionDivergence

/-! All three original periodic attractive lower-bound clauses, with genuine
critical properness. The critical liminf is extended-valued, as required when
no finite upper bound for its normalization is part of the proposition. The
stronger every-N real lower bound is also stated after properness is proved. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic

theorem periodic_critical_partition_finite_source (d : ℕ) (hd : 11≤d) (N : ℕ) (hN : 1≤N) :
    letI : NeZero d := ⟨by omega⟩
    periodicAttractivePartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) N<∞ := by
  letI : NeZero d := ⟨by omega⟩
  exact (periodicAttractivePartition_finite_upper _ periodicStabilityThreshold_pos.le
    (by simpa only [Fintype.card_fin] using periodicStabilityThreshold_lt_collision d hd) N hN).2

/-- A proper real partition and the exact critical constant for every N>=1. -/
theorem periodic_critical_real_normalized_lower_source (d : ℕ) (hd : 11≤d) (N : ℕ) (hN : 1≤N) :
    letI : NeZero d := ⟨by omega⟩
    (Real.sqrt Real.pi/Real.exp 1)^d≤(N:ℝ)^(-(d:ℝ)/2)*
      (periodicAttractivePartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) N).toReal := by
  letI : NeZero d := ⟨by omega⟩
  have hf := periodic_critical_partition_finite_source d hd N hN
  have hl := ENNReal.toReal_mono hf.ne (periodic_critical_full_sqrt_lower (ι := Fin d) N hN)
  rw [ENNReal.toReal_ofReal (by positivity)] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg (Nat.cast_nonneg N) (-(Fintype.card (Fin d):ℝ)/2))
  rw [periodic_critical_normalizing_identity N hN] at hm
  simpa only [Fintype.card_fin] using hm

/-- Source proposition periodicAttractiveLowerBounds, all three clauses and
actual critical finiteness. No pressure limit or finite critical liminf is
asserted; neither is required by the source proposition. -/
theorem periodicAttractiveLowerBounds_source (d : ℕ) (hd : 11≤d) :
    letI : NeZero d := ⟨by omega⟩
    (∀ N : ℕ,1≤N → periodicAttractivePartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) N<∞) ∧
    (ENNReal.ofReal ((Real.sqrt Real.pi/Real.exp 1)^d)≤
      liminf (fun N : ℕ => ENNReal.ofReal ((N:ℝ)^(-(d:ℝ)/2))*
        periodicAttractivePartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) N) atTop) ∧
    (∀ β : ℝ,periodicStabilityThreshold (Fin d)<β → β<2*(d:ℝ) →
      (∀ N : ℕ,1≤N → periodicAttractivePartition (ι := Fin d) β N<∞) ∧
      0<liminf (periodicPressure (ι := Fin d) β) atTop) ∧
    (∀ β : ℝ,2*(d:ℝ)≤β → ∀ N : ℕ,2≤N → periodicAttractivePartition (ι := Fin d) β N=∞) := by
  letI : NeZero d := ⟨by omega⟩
  exact ⟨periodic_critical_partition_finite_source d hd,periodic_critical_partition_source d hd,
    periodic_supercritical_pressure_source d hd,periodic_collision_partition_source d hd⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_critical_partition_finite_source
#print axioms DGRHS.Periodic.periodic_critical_real_normalized_lower_source
#print axioms DGRHS.Periodic.periodicAttractiveLowerBounds_source
#check @DGRHS.Periodic.periodicAttractiveLowerBounds_source
