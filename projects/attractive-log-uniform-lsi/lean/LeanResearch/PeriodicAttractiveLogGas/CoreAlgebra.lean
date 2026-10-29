import LeanResearch.PeriodicAttractiveLogGas.SmoothCore

/-! Linear structure and energy of the actual smooth gradient graph. The
closed submodule below consists of pairs, until closability identifies a unique
gradient for each scalar component. Source: prop:ambient. -/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

def SmoothPair.add {N : ℕ} (f g : SmoothPair N) : SmoothPair N where
  value := f.value + g.value
  gradient := f.gradient + g.gradient
  smooth := f.smooth.add g.smooth
  differential := by
    intro y
    convert! (f.differential y).add (g.differential y) using 1
    simp

def SmoothPair.smul {N : ℕ} (c : ℝ) (f : SmoothPair N) : SmoothPair N where
  value := c • f.value
  gradient := c • f.gradient
  smooth := f.smooth.const_smul c
  differential := by
    intro y
    convert! (f.differential y).const_smul c using 1
    simp

def SmoothPair.mul {N : ℕ} (f g : SmoothPair N) : SmoothPair N where
  value := f.value * g.value
  gradient := ⟨fun x ↦ g.value x • f.gradient x + f.value x • g.gradient x, by fun_prop⟩
  smooth := f.smooth.mul g.smooth
  differential := by
    intro y
    convert! (f.differential y).mul (g.differential y) using 1
    simp [add_comm]

def smoothGradientSubmodule (N : ℕ) (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    Submodule ℝ (Lp ℝ 2 μ × Lp (Gradient N) 2 μ) where
  carrier := smoothGradientGraph N μ
  zero_mem' := by
    refine ⟨SmoothPair.const N 0, ?_⟩
    simp [SmoothPair.const]
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f.add g, ?_⟩
    simp [SmoothPair.add]
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    refine ⟨f.smul c, ?_⟩
    simp [SmoothPair.smul]

def closedGradientSubmodule (N : ℕ) (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    Submodule ℝ (Lp ℝ 2 μ × Lp (Gradient N) 2 μ) :=
  (smoothGradientSubmodule N μ).topologicalClosure

theorem closedGradientSubmodule_coe (N : ℕ) (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] :
    (closedGradientSubmodule N μ : Set (Lp ℝ 2 μ × Lp (Gradient N) 2 μ)) =
      closedGradientGraph N μ := rfl

instance (N : ℕ) (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    CompleteSpace (closedGradientSubmodule N μ) :=
  Submodule.topologicalClosure.completeSpace _

theorem closedGradientGraph_add {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {f g : Lp ℝ 2 μ × Lp (Gradient N) 2 μ}
    (hf : f ∈ closedGradientGraph N μ) (hg : g ∈ closedGradientGraph N μ) :
    f + g ∈ closedGradientGraph N μ := (closedGradientSubmodule N μ).add_mem hf hg

theorem closedGradientGraph_smul {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (c : ℝ) {f : Lp ℝ 2 μ × Lp (Gradient N) 2 μ}
    (hf : f ∈ closedGradientGraph N μ) :
    c • f ∈ closedGradientGraph N μ := (closedGradientSubmodule N μ).smul_mem c hf

def graphEnergy {N : ℕ} {μ : Measure (Configuration N)}
    (z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) : ℝ := ‖z.2‖ ^ 2

theorem graphEnergy_eq_integral {N : ℕ} {μ : Measure (Configuration N)}
    (z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) :
    graphEnergy z = ∫ x, ∑ i : Fin N, ∑ k : Fin 2, (z.2 x (i, k)) ^ 2 ∂μ := by
  rw [graphEnergy, ← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, gradient_norm_sq]

theorem graphEnergy_toLp {N : ℕ} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (f : SmoothPair N) :
    graphEnergy (ContinuousMap.toLp 2 μ ℝ f.value, ContinuousMap.toLp 2 μ ℝ f.gradient) =
      ∫ x, ∑ i : Fin N, ∑ k : Fin 2, (f.gradient x (i, k)) ^ 2 ∂μ := by
  rw [graphEnergy_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f.gradient] with x hx
  rw [hx]

def graphFormNorm {N : ℕ} {μ : Measure (Configuration N)}
    (z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) : ℝ :=
  Real.sqrt (‖z.1‖ ^ 2 + graphEnergy z)

theorem graphFormNorm_nonneg {N : ℕ} {μ : Measure (Configuration N)}
    (z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) : 0 ≤ graphFormNorm z := Real.sqrt_nonneg _

theorem graphFormNorm_sq {N : ℕ} {μ : Measure (Configuration N)}
    (z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) :
    graphFormNorm z ^ 2 = ‖z.1‖ ^ 2 + graphEnergy z :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem norm_le_graphFormNorm {N : ℕ} {μ : Measure (Configuration N)}
    (z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) : ‖z‖ ≤ graphFormNorm z := by
  have hs := graphFormNorm_sq z
  have hn := graphFormNorm_nonneg z
  unfold graphEnergy at hs
  rw [Prod.norm_def]
  apply max_le
  · nlinarith [norm_nonneg z.1, sq_nonneg ‖z.2‖]
  · nlinarith [norm_nonneg z.2, sq_nonneg ‖z.1‖]

theorem graphFormNorm_le_two_norm {N : ℕ} {μ : Measure (Configuration N)}
    (z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) : graphFormNorm z ≤ 2 * ‖z‖ := by
  have hs := graphFormNorm_sq z
  have hn := graphFormNorm_nonneg z
  have h₁ : ‖z.1‖ ≤ ‖z‖ := le_max_left _ _
  have h₂ : ‖z.2‖ ≤ ‖z‖ := le_max_right _ _
  have hs₁ : ‖z.1‖ ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h₁
  have hs₂ : ‖z.2‖ ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr h₂
  unfold graphEnergy at hs
  nlinarith [norm_nonneg z]

theorem tendsto_iff_graphFormNorm_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    {N : ℕ} {μ : Measure (Configuration N)}
    {z : ι → Lp ℝ 2 μ × Lp (Gradient N) 2 μ} {w : Lp ℝ 2 μ × Lp (Gradient N) 2 μ} :
    Filter.Tendsto z l (𝓝 w) ↔
      Filter.Tendsto (fun n ↦ graphFormNorm (z n - w)) l (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  constructor
  · intro h
    apply squeeze_zero (fun n ↦ graphFormNorm_nonneg (z n - w))
      (fun n ↦ graphFormNorm_le_two_norm (z n - w))
    simpa using h.const_mul 2
  · intro h
    exact squeeze_zero (fun n ↦ norm_nonneg (z n - w))
      (fun n ↦ norm_le_graphFormNorm (z n - w)) h

end PeriodicAttractiveLogGas
