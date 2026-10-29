import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# A sequential Arzelà–Ascoli lemma (Phase 3, lane D; R13)

A uniformly bounded, uniformly Lipschitz sequence of real functions on a compact metric space has
a uniformly convergent subsequence with continuous limit.
-/

open Filter Topology BoundedContinuousFunction
open scoped NNReal

namespace SharpLSI

theorem exists_subseq_unif {X : Type*} [MetricSpace X] [CompactSpace X] (u : ℕ → X → ℝ) {C : ℝ}
    {L : ℝ≥0} (hb : ∀ n x, |u n x| ≤ C) (hL : ∀ n, LipschitzWith L (u n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X → ℝ, Continuous v ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |u (φ n) x - v x| ≤ ε := by
  set f : ℕ → X →ᵇ ℝ := fun n => mkOfCompact ⟨u n, (hL n).continuous⟩ with hf
  set A : Set (X →ᵇ ℝ) := Set.range f
  have hin : ∀ (g : X →ᵇ ℝ) (x : X), g ∈ A → g x ∈ Set.Icc (-C) C := by
    rintro g x ⟨n, rfl⟩
    exact abs_le.mp (hb n x)
  have heq : Equicontinuous ((↑) : A → X → ℝ) := by
    refine (LipschitzWith.uniformEquicontinuous _ L fun g => ?_).equicontinuous
    obtain ⟨n, hn⟩ := g.2
    rw [← hn]
    exact hL n
  have hK := arzela_ascoli (Set.Icc (-C) C) isCompact_Icc A hin heq
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := f) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨φ, hφ, a, a.continuous, fun ε hε => ?_⟩
  have := (Metric.tendsto_atTop.mp hlim) ε hε
  obtain ⟨N, hN⟩ := this
  refine eventually_atTop.mpr ⟨N, fun n hn x => ?_⟩
  have h1 := hN n hn
  have h2 : |f (φ n) x - a x| ≤ dist (f (φ n)) a := by
    rw [← Real.dist_eq]; exact dist_coe_le_dist x
  exact h2.trans h1.le

end SharpLSI
