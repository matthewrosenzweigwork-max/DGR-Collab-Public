import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The square unit torus, labelled configurations, and the actual Euclidean
gradient norm. Source: eq:kernel, eq:gas and eq:energy. No Gibbs kernel or
closed gradient operator is assumed or constructed in this foundational file. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PeriodicAttractiveLogGas

abbrev Torus := Fin 2 → UnitAddCircle
abbrev Configuration (N : ℕ) := Fin N → Torus
abbrev Gradient (N : ℕ) := EuclideanSpace ℝ (Fin N × Fin 2)

def torusMeasure : Measure Torus := Measure.pi fun _ ↦ AddCircle.haarAddCircle

instance : IsProbabilityMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

def referenceMeasure (N : ℕ) : Measure (Configuration N) := Measure.pi fun _ ↦ torusMeasure

instance (N : ℕ) : IsProbabilityMeasure (referenceMeasure N) := by
  unfold referenceMeasure
  infer_instance

theorem referenceMeasure_univ (N : ℕ) : referenceMeasure N Set.univ = 1 := measure_univ

/-- The pointwise energy is the sum of the two coordinate squares for each
labelled particle; there is no factor inverse in the number of particles. -/
theorem gradient_norm_sq (N : ℕ) (v : Gradient N) :
    ‖v‖ ^ 2 = ∑ i : Fin N, ∑ k : Fin 2, (v (i, k)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_product ..

end PeriodicAttractiveLogGas
