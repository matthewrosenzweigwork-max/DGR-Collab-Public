import LeanResearch.PeriodicAttractiveLogGas.WeakGradient
import LeanResearch.PeriodicAttractiveLogGas.SmoothDensity

/-! Closability of the actual ambient smooth-gradient graph, under the measure
comparison hypotheses used in prop:ambient. GreenNormalization proves the
actual Green kernel's finiteness and measure comparisons, and GreenAmbientDomain
supplies the resulting Gibbs specialization. -/

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

theorem HasReferenceWeakGradient.unique {N : ℕ} {u : Lp ℝ 2 (referenceMeasure N)}
    {G H : Lp (Gradient N) 2 (referenceMeasure N)}
    (hG : HasReferenceWeakGradient N u G) (hH : HasReferenceWeakGradient N u H) : G = H := by
  apply directionalLp_ext
  intro v
  have hd : Dense (Set.range (fun f : SmoothPair N ↦
      ContinuousMap.toLp 2 (referenceMeasure N) ℝ f.value)) :=
    denseRange_smoothPair_toLp N (referenceMeasure N)
  apply hd.eq_of_inner_right ℝ
  rintro _ ⟨φ, rfl⟩
  have h₁ := hG φ v
  have h₂ := hH φ v
  linarith

theorem closedGradientGraph_unique_gradient {N : ℕ}
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (h : referenceMeasure N ≤ c • μ) (hμ : μ ≪ referenceMeasure N)
    {u : Lp ℝ 2 μ} {G H : Lp (Gradient N) 2 μ}
    (hG : (u, G) ∈ closedGradientGraph N μ) (hH : (u, H) ∈ closedGradientGraph N μ) : G = H := by
  apply measureComparison_injective hc h hμ
  have hG' := closedGradientGraph_hasReferenceWeakGradient (z := (u, G)) hc h hG
  have hH' := closedGradientGraph_hasReferenceWeakGradient (z := (u, H)) hc h hH
  exact HasReferenceWeakGradient.unique hG' hH'

theorem closedGradientGraph_zero_fiber {N : ℕ}
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (h : referenceMeasure N ≤ c • μ) (hμ : μ ≪ referenceMeasure N)
    {G : Lp (Gradient N) 2 μ} (hG : (0, G) ∈ closedGradientGraph N μ) : G = 0 := by
  apply closedGradientGraph_unique_gradient hc h hμ hG
  exact (closedGradientSubmodule N μ).zero_mem

theorem closedGradientGraph_scalar_projection_injective {N : ℕ}
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (h : referenceMeasure N ≤ c • μ) (hμ : μ ≪ referenceMeasure N) :
    Function.Injective (fun z : closedGradientSubmodule N μ ↦ z.1.1) := by
  intro z w hzw
  change z.1.1 = w.1.1 at hzw
  apply Subtype.ext
  apply Prod.ext hzw
  have hz : (w.1.1, z.1.2) ∈ closedGradientGraph N μ := by
    rw [← hzw]
    exact z.2
  exact closedGradientGraph_unique_gradient hc h hμ hz w.2

theorem smoothGradient_closable {N : ℕ}
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (h : referenceMeasure N ≤ c • μ) (hμ : μ ≪ referenceMeasure N)
    (f : ℕ → SmoothPair N)
    (hf : Filter.Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (f n).value)
      Filter.atTop (𝓝 0))
    (hgrad : CauchySeq (fun n ↦ ContinuousMap.toLp 2 μ ℝ (f n).gradient)) :
    Filter.Tendsto (fun n ↦ ContinuousMap.toLp 2 μ ℝ (f n).gradient) Filter.atTop (𝓝 0) := by
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hgrad
  have hmem : (0, G) ∈ closedGradientGraph N μ := by
    exact mem_closure_of_tendsto (hf.prodMk_nhds hG)
      (Filter.Eventually.of_forall fun n ↦ ⟨f n, rfl⟩)
  have hzero := closedGradientGraph_zero_fiber hc h hμ hmem
  simpa only [hzero] using hG

end PeriodicAttractiveLogGas
