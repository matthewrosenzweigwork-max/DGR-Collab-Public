import LeanResearch.PeriodicAttractiveLogGas.Geometry
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The labelled attractive Gibbs construction, before the specific Green
kernel is constructed. Source: eq:gas and prop:normalization. The finite
partition hypothesis below is explicit and is NOT yet proved for the singular
kernel. These general identities do not assert the manuscript theorem. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

def pairEnergy (g : Torus → ℝ) (N : ℕ) (x : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, g (x i - x j)

def gibbsWeight (g : Torus → ℝ) (N : ℕ) (β : ℝ) (x : Configuration N) : ℝ :=
  Real.exp ((β / (N : ℝ)) * pairEnergy g N x)

/-- The normalizer is an extended integral; finiteness is a separate theorem. -/
def partitionFunction (g : Torus → ℝ) (N : ℕ) (β : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (gibbsWeight g N β x) ∂referenceMeasure N

def gibbsMeasure (g : Torus → ℝ) (N : ℕ) (β : ℝ) : Measure (Configuration N) :=
  (partitionFunction g N β)⁻¹ •
    (referenceMeasure N).withDensity (fun x ↦ ENNReal.ofReal (gibbsWeight g N β x))

theorem gibbsWeight_pos (g : Torus → ℝ) (N : ℕ) (β : ℝ) (x : Configuration N) :
    0 < gibbsWeight g N β x := Real.exp_pos _

theorem measurable_pairEnergy {g : Torus → ℝ} (hg : Measurable g) (N : ℕ) :
    Measurable (pairEnergy g N) := by
  unfold pairEnergy
  fun_prop

theorem measurable_gibbsWeight {g : Torus → ℝ} (hg : Measurable g) (N : ℕ) (β : ℝ) :
    Measurable (gibbsWeight g N β) := by
  exact Real.continuous_exp.measurable.comp ((measurable_pairEnergy hg N).const_mul _)

theorem partitionFunction_ne_zero {g : Torus → ℝ} (hg : Measurable g) (N : ℕ) (β : ℝ) :
    partitionFunction g N β ≠ 0 := by
  intro hz
  have hae := (lintegral_eq_zero_iff (measurable_gibbsWeight hg N β).ennreal_ofReal).mp hz
  obtain ⟨x, hx⟩ := hae.exists
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (gibbsWeight_pos g N β x))) hx

theorem gibbsMeasure_univ {g : Torus → ℝ} (hg : Measurable g) (N : ℕ) (β : ℝ)
    (hfin : partitionFunction g N β ≠ ⊤) : gibbsMeasure g N β Set.univ = 1 := by
  unfold gibbsMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (partitionFunction_ne_zero hg N β) hfin

theorem isProbabilityMeasure_gibbsMeasure {g : Torus → ℝ} (hg : Measurable g) (N : ℕ) (β : ℝ)
    (hfin : partitionFunction g N β ≠ ⊤) : IsProbabilityMeasure (gibbsMeasure g N β) :=
  ⟨gibbsMeasure_univ hg N β hfin⟩

@[simp] theorem gibbsWeight_zero (g : Torus → ℝ) (N : ℕ) (x : Configuration N) :
    gibbsWeight g N 0 x = 1 := by simp [gibbsWeight]

@[simp] theorem partitionFunction_zero (g : Torus → ℝ) (N : ℕ) :
    partitionFunction g N 0 = 1 := by simp [partitionFunction]

@[simp] theorem gibbsMeasure_zero (g : Torus → ℝ) (N : ℕ) :
    gibbsMeasure g N 0 = referenceMeasure N := by
  simp [gibbsMeasure]

theorem gibbsMeasure_absolutelyContinuous (g : Torus → ℝ) (N : ℕ) (β : ℝ) :
    gibbsMeasure g N β ≪ referenceMeasure N :=
  (withDensity_absolutelyContinuous _ _).smul_left _

end PeriodicAttractiveLogGas
