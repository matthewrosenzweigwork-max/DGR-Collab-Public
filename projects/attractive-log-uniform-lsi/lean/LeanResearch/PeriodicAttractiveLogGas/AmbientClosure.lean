import LeanResearch.PeriodicAttractiveLogGas.Closability

/-! The completion of the actual ambient smooth gradient graph. Elements are
represented by function/gradient pairs. The proved scalar projection injectivity
identifies them with functions when the source measure comparisons hold.
The full scalar smooth-class correspondence is proved in SmoothRepresentation.
The actual Green measure comparisons and scalar-domain identification are
discharged in GreenNormalization and GreenAmbientDomain. Lipschitz inclusion
and the Markov property remain separate obligations. -/

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

abbrev AmbientFormDomain (N : ℕ) (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :=
  closedGradientSubmodule N μ

def SmoothPair.toAmbient {N : ℕ} (f : SmoothPair N)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] : AmbientFormDomain N μ :=
  ⟨(ContinuousMap.toLp 2 μ ℝ f.value, ContinuousMap.toLp 2 μ ℝ f.gradient),
    smoothPair_mem_closedGradientGraph N μ f⟩

def ambientValue {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : AmbientFormDomain N μ) : Lp ℝ 2 μ := f.1.1

def ambientGradient {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : AmbientFormDomain N μ) : Lp (Gradient N) 2 μ := f.1.2

def ambientEnergy {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : AmbientFormDomain N μ) : ℝ := graphEnergy f.1

theorem ambientEnergy_const (N : ℕ) (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (c : ℝ) : ambientEnergy ((SmoothPair.const N c).toAmbient μ) = 0 := by
  simp [ambientEnergy, graphEnergy, SmoothPair.toAmbient, SmoothPair.const]

instance : torusMeasure.IsOpenPosMeasure := by
  unfold torusMeasure
  infer_instance

instance (N : ℕ) : (referenceMeasure N).IsOpenPosMeasure :=
  Measure.pi.isOpenPosMeasure (fun _ : Fin N ↦ torusMeasure)

theorem isOpenPosMeasure_gibbsMeasure {g : Torus → ℝ} (hg : Measurable g)
    (N : ℕ) (β : ℝ) (hfin : partitionFunction g N β ≠ ⊤) :
    (gibbsMeasure g N β).IsOpenPosMeasure :=
  (referenceMeasure_absolutelyContinuous_gibbsMeasure hg N β hfin).isOpenPosMeasure

theorem labelledCosine_toLp_ne_const {N : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (i : Fin N) (k : Fin 2) (c : ℝ) :
    ContinuousMap.toLp 2 μ ℝ (labelledCosine N i k) ≠
      ContinuousMap.toLp 2 μ ℝ (ContinuousMap.const _ c) := by
  intro heq
  have hf := (ContinuousMap.toLp_inj (p := 2) (𝕜 := ℝ) μ).mp heq
  obtain ⟨x, y, hxy⟩ := labelledCosine_nonconstant N i k
  rw [hf] at hxy
  exact hxy rfl

theorem ambientValue_injective {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : referenceMeasure N ≤ c • μ) (hμ : μ ≪ referenceMeasure N) :
    Function.Injective (ambientValue (N := N) (μ := μ)) :=
  closedGradientGraph_scalar_projection_injective hc h hμ

theorem ambientEnergy_eq_integral {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : AmbientFormDomain N μ) :
    ambientEnergy f = ∫ x, ∑ i : Fin N, ∑ k : Fin 2,
      (ambientGradient f x (i, k)) ^ 2 ∂μ := graphEnergy_eq_integral f.1

theorem exists_smooth_formNorm_approx {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : AmbientFormDomain N μ) : ∃ s : ℕ → SmoothPair N,
      Filter.Tendsto (fun n ↦ graphFormNorm
        ((ContinuousMap.toLp 2 μ ℝ (s n).value, ContinuousMap.toLp 2 μ ℝ (s n).gradient) - f.1))
        Filter.atTop (𝓝 0) := by
  obtain ⟨w, hw, ht⟩ := mem_closure_iff_seq_limit.mp f.2
  choose s hs using hw
  refine ⟨s, tendsto_iff_graphFormNorm_sub_tendsto_zero.mp ?_⟩
  have heq : (fun n ↦
      (ContinuousMap.toLp 2 μ ℝ (s n).value, ContinuousMap.toLp 2 μ ℝ (s n).gradient)) = w :=
    funext hs
  rw [heq]
  exact ht

theorem ambient_entropy_le_of_smooth_bound {N : ℕ} {μ : Measure (Configuration N)}
    [IsFiniteMeasure μ] {C : ℝ}
    (hcore : ∀ s : SmoothPair N,
      entropy μ (fun x ↦ (s.value x) ^ 2) ≤
        ((2 * C * (∫ x, ∑ i : Fin N, ∑ k : Fin 2, (s.gradient x (i, k)) ^ 2 ∂μ) : ℝ) : EReal))
    (f : AmbientFormDomain N μ) :
    entropy μ (fun x ↦ (ambientValue f x) ^ 2) ≤ ((2 * C * ambientEnergy f : ℝ) : EReal) := by
  apply entropy_sq_le_on_graph_closure (core := smoothGradientGraph N μ) (C := C)
  · rintro z ⟨s, rfl⟩
    have heq : entropy μ (fun x ↦ ((ContinuousMap.toLp 2 μ ℝ s.value) x) ^ 2) =
        entropy μ (fun x ↦ (s.value x) ^ 2) :=
      entropy_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ s.value).mono
        fun x hx ↦ congrArg (fun t : ℝ ↦ t ^ 2) hx)
    rw [heq]
    have he := graphEnergy_toLp (μ := μ) s
    change ‖ContinuousMap.toLp 2 μ ℝ s.gradient‖ ^ 2 = _ at he
    rw [he]
    exact hcore s
  · exact f.2

end PeriodicAttractiveLogGas
