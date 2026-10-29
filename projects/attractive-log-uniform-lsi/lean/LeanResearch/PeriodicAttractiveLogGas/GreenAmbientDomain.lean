import LeanResearch.PeriodicAttractiveLogGas.GreenNormalization
import LeanResearch.PeriodicAttractiveLogGas.SmoothRepresentation

/-! Specialization of the checked closed ambient graph to the actual
subcritical Green probability law. Its scalar projection is injective and
contains nonconstant functions. The Lipschitz and Markov assertions of source
Proposition 2.6 are separate remaining obligations. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

theorem greenGibbs_null_iff (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hs : β < 4) (s : Set (Configuration N)) :
    gibbsMeasure greenRealRepresentative N β s = 0 ↔ referenceMeasure N s = 0 :=
  gibbsMeasure_null_iff greenRealRepresentative_measurable N β
    (green_partitionFunction_ne_top N hN hβ hs) s

theorem green_ambientValue_injective (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hs : β < 4) :
    Function.Injective (ambientValue (N := N) (μ := gibbsMeasure greenRealRepresentative N β)) := by
  obtain ⟨c, hc, hb⟩ := exists_reference_le_greenGibbs N hN hβ hs
  exact ambientValue_injective hc hb (gibbsMeasure_absolutelyContinuous _ N β)

theorem green_smoothGradient_closable (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hs : β < 4) (f : ℕ → SmoothPair N)
    (hf : Tendsto (fun n ↦ ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ
      (f n).value) atTop (𝓝 0))
    (hgrad : CauchySeq (fun n ↦ ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ
      (f n).gradient)) :
    Tendsto (fun n ↦ ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ
      (f n).gradient) atTop (𝓝 0) := by
  obtain ⟨c, hc, hb⟩ := exists_reference_le_greenGibbs N hN hβ hs
  exact smoothGradient_closable hc hb (gibbsMeasure_absolutelyContinuous _ N β) f hf hgrad

theorem green_ambient_hasReferenceWeakGradient (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hs : β < 4) :
    ∃ c : ℝ≥0∞, ∃ hc : c ≠ ⊤,
      ∃ hb : referenceMeasure N ≤ c • gibbsMeasure greenRealRepresentative N β,
        ∀ f : GreenAmbientFormDomain N β,
          HasReferenceWeakGradient N (Lp.LpToLpOfMeasureLeSMul hc hb (ambientValue f))
            (Lp.LpToLpOfMeasureLeSMul hc hb (ambientGradient f)) := by
  obtain ⟨c, hc, hb⟩ := exists_reference_le_greenGibbs N hN hβ hs
  exact ⟨c, hc, hb, fun f ↦ closedGradientGraph_hasReferenceWeakGradient hc hb f.2⟩

theorem green_ambient_nonconstant (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hs : β < 4) :
    ∃ f : GreenAmbientFormDomain N β, ∀ c : ℝ,
      ambientValue f ≠ ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ
        (ContinuousMap.const (Configuration N) c) := by
  let : (gibbsMeasure greenRealRepresentative N β).IsOpenPosMeasure :=
    isOpenPosMeasure_gibbsMeasure greenRealRepresentative_measurable N β
      (green_partitionFunction_ne_top N hN hβ hs)
  let i : Fin N := ⟨0, by omega⟩
  refine ⟨(SmoothPair.cosine N i 0).toAmbient _, ?_⟩
  intro c
  exact labelledCosine_toLp_ne_const (gibbsMeasure greenRealRepresentative N β) i 0 c

theorem green_smooth_core_dense (N : ℕ) (β : ℝ) :
    DenseRange (fun f : SmoothPair N ↦
      ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ f.value) :=
  denseRange_smoothPair_toLp N (gibbsMeasure greenRealRepresentative N β)

theorem green_ambient_energy_eq_integral (N : ℕ) (β : ℝ) (f : GreenAmbientFormDomain N β) :
    ambientEnergy f = ∫ x, ∑ i : Fin N, ∑ k : Fin 2,
      (ambientGradient f x (i, k)) ^ 2 ∂gibbsMeasure greenRealRepresentative N β :=
  ambientEnergy_eq_integral f

end PeriodicAttractiveLogGas
