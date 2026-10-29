import LeanResearch.PeriodicAttractiveLogGas.PeriodicCalculus
import LeanResearch.PeriodicAttractiveLogGas.MeasureComparison

/-! Weak gradients are tested against the unweighted Haar measure. The
closed-graph implication is proved from the actual smooth integration by parts;
no differential identity is postulated for the singular weighted measure. -/

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas

def SmoothPair.directionalDerivative {N : ℕ} (f : SmoothPair N) (v : Gradient N) :
    C(Configuration N, ℝ) :=
  ⟨fun x ↦ inner ℝ (f.gradient x) v, f.gradient.continuous.inner continuous_const⟩

def directionalLp {N : ℕ} (μ : Measure (Configuration N)) (v : Gradient N) :
    Lp (Gradient N) 2 μ →L[ℝ] Lp ℝ 2 μ := (innerSL ℝ v).compLpL 2 μ

theorem directionalLp_toLp {N : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : SmoothPair N) (v : Gradient N) :
    directionalLp μ v (ContinuousMap.toLp 2 μ ℝ f.gradient) =
      ContinuousMap.toLp 2 μ ℝ (f.directionalDerivative v) := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ v).coeFn_compLpL (ContinuousMap.toLp 2 μ ℝ f.gradient),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f.gradient,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (f.directionalDerivative v)] with x h₁ h₂ h₃
  change ((innerSL ℝ v).compLpL 2 μ (ContinuousMap.toLp 2 μ ℝ f.gradient)) x = _
  rw [h₁, h₂, h₃]
  exact (real_inner_comm v (f.gradient x)).symm

theorem directionalLp_ext {N : ℕ} {μ : Measure (Configuration N)}
    {G H : Lp (Gradient N) 2 μ} (h : ∀ v, directionalLp μ v G = directionalLp μ v H) : G = H := by
  have hcoord (j : Fin N × Fin 2) : ∀ᵐ x ∂μ, (G x) j = (H x) j := by
    let v : Gradient N := EuclideanSpace.single j 1
    have hG := (innerSL ℝ v).coeFn_compLpL G
    have hH := (innerSL ℝ v).coeFn_compLpL H
    have heq : (innerSL ℝ v).compLpL 2 μ G = (innerSL ℝ v).compLpL 2 μ H := h v
    rw [heq] at hG
    filter_upwards [hG, hH] with x hxG hxH
    have hx := hxG.symm.trans hxH
    simpa [innerSL_apply_apply, v, EuclideanSpace.inner_single_left] using hx
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  ext j
  exact hx j

theorem SmoothPair.integration_by_parts_L2 {N : ℕ} (f φ : SmoothPair N) (v : Gradient N) :
    inner ℝ (ContinuousMap.toLp 2 (referenceMeasure N) ℝ φ.value)
      (directionalLp (referenceMeasure N) v
        (ContinuousMap.toLp 2 (referenceMeasure N) ℝ f.gradient)) +
      inner ℝ (ContinuousMap.toLp 2 (referenceMeasure N) ℝ (φ.directionalDerivative v))
        (ContinuousMap.toLp 2 (referenceMeasure N) ℝ f.value) = 0 := by
  rw [directionalLp_toLp, ContinuousMap.inner_toLp, ContinuousMap.inner_toLp]
  simp only [conj_trivial, SmoothPair.directionalDerivative, ContinuousMap.coe_mk]
  simp_rw [mul_comm (inner ℝ (f.gradient _) v)]
  exact add_eq_zero_iff_eq_neg.mpr (f.integration_by_parts φ v)

def HasReferenceWeakGradient (N : ℕ) (u : Lp ℝ 2 (referenceMeasure N))
    (G : Lp (Gradient N) 2 (referenceMeasure N)) : Prop :=
  ∀ (φ : SmoothPair N) (v : Gradient N),
    inner ℝ (ContinuousMap.toLp 2 (referenceMeasure N) ℝ φ.value)
        (directionalLp (referenceMeasure N) v G) +
      inner ℝ (ContinuousMap.toLp 2 (referenceMeasure N) ℝ (φ.directionalDerivative v)) u = 0

theorem closedGradientGraph_hasReferenceWeakGradient {N : ℕ}
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (h : referenceMeasure N ≤ c • μ)
    {z : Lp ℝ 2 μ × Lp (Gradient N) 2 μ} (hz : z ∈ closedGradientGraph N μ) :
    HasReferenceWeakGradient N (Lp.LpToLpOfMeasureLeSMul hc h z.1)
      (Lp.LpToLpOfMeasureLeSMul hc h z.2) := by
  intro φ v
  let F (w : Lp ℝ 2 μ × Lp (Gradient N) 2 μ) :=
    inner ℝ (ContinuousMap.toLp 2 (referenceMeasure N) ℝ φ.value)
        (directionalLp (referenceMeasure N) v (Lp.LpToLpOfMeasureLeSMul hc h w.2)) +
      inner ℝ (ContinuousMap.toLp 2 (referenceMeasure N) ℝ (φ.directionalDerivative v))
        (Lp.LpToLpOfMeasureLeSMul hc h w.1)
  have hcont : Continuous F := by unfold F; fun_prop
  have hclosed : IsClosed {w | F w = 0} := isClosed_eq hcont continuous_const
  have hcore : smoothGradientGraph N μ ⊆ {w | F w = 0} := by
    rintro w ⟨f, rfl⟩
    change F (ContinuousMap.toLp 2 μ ℝ f.value, ContinuousMap.toLp 2 μ ℝ f.gradient) = 0
    dsimp only [F]
    rw [measureComparison_toLp, measureComparison_toLp]
    exact f.integration_by_parts_L2 φ v
  exact (hclosed.closure_subset_iff.mpr hcore) hz

end PeriodicAttractiveLogGas
