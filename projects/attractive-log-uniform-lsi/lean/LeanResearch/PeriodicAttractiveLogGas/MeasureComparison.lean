import LeanResearch.PeriodicAttractiveLogGas.SmoothCore
import LeanResearch.PeriodicAttractiveLogGas.Density

/-! The actual continuous L2 comparison map used in prop:ambient. It does not
replace the ordinary gradient by differentiation against the weighted measure. -/

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

theorem measureComparison_injective {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ ν : Measure α} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (h : μ ≤ c • ν) (hνμ : ν ≪ μ) :
    Function.Injective (Lp.LpToLpOfMeasureLeSMul hc h : Lp E 2 ν →L[ℝ] Lp E 2 μ) := by
  intro f g heq
  apply Lp.ext
  apply hνμ.ae_eq
  have hf := Lp.coeFn_LpToLpOfMeasureLeSMul hc h f
  have hg := Lp.coeFn_LpToLpOfMeasureLeSMul hc h g
  rw [heq] at hf
  exact hf.symm.trans hg

theorem measureComparison_toLp {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ ν : Measure (Configuration N)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : μ ≤ c • ν) (f : C(Configuration N, E)) :
    Lp.LpToLpOfMeasureLeSMul hc h (ContinuousMap.toLp 2 ν ℝ f) =
      ContinuousMap.toLp 2 μ ℝ f := by
  apply Lp.ext
  have hμν : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc h _).trans
    ((hμν.ae_eq (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν f)).trans
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f).symm)

end PeriodicAttractiveLogGas
