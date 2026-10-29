import LeanResearch.PeriodicAttractiveLogGas.WeightedCubeBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual locally finite weighted measure and its integral correspondence.
These facts are derived from the periodic weight's proved local integrability. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace PeriodicAttractiveLogGas.WeightedCubeBounds
variable {ι : Type*} [Fintype ι]
variable {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)}

lemma Bounds.locallyFinite (h : Bounds w A Z) : IsLocallyFiniteMeasure (weightedMeasure w) :=
  ⟨fun x => ⟨closedBall x 1, closedBall_mem_nhds x zero_lt_one, h.measure_closedBall_lt_top x 1⟩⟩

lemma Bounds.setIntegral_weightedMeasure (h : Bounds w A Z) {S : Set (EuclideanSpace ℝ ι)}
    (hS : MeasurableSet S) (f : EuclideanSpace ℝ ι → ℝ) :
    (∫ x in S, f x ∂weightedMeasure w) = ∫ x in S, w x * f x := by
  rw [weightedMeasure, restrict_withDensity hS,
    integral_withDensity_eq_integral_toReal_smul h.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [ENNReal.toReal_ofReal (h.nonneg x), smul_eq_mul]

lemma Bounds.integrableOn_continuous (h : Bounds w A Z) {S : Set (EuclideanSpace ℝ ι)}
    (hS : IsCompact S) {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f) :
    IntegrableOn f S (weightedMeasure w) := by
  letI := h.locallyFinite
  exact hf.continuousOn.integrableOn_compact hS

end PeriodicAttractiveLogGas.WeightedCubeBounds
