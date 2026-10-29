import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D13_Equilibrium
import SharpSymmetricLSI.Infra.Heat
import SharpSymmetricLSI.Paper.MinimizerCompact

/-!
# R13: Lemma 4.1 (`lem:minimizers`), regularity of minimizers

Manuscript Lemma 4.1, (4.1), (4.2). Under (1.2) (no assumption on `r_*`): every minimizer `μ`
satisfies the Euler–Lagrange equation `μ = e^{-V-W*μ}/∫ e^{-V-W*μ} dm` (4.1); the densities of
the minimizers have common positive lower bounds and common upper and Lipschitz bounds; and
they form a compact subset of `W^{1,∞}(𝕋^d)` (encoded as sequential compactness for
`w1infDist`, with limits again minimizer densities). The Lipschitz constant is existential, so
Mathlib's sup metric on `(ℝ/ℤ)^d` is used; it is equivalent to the flat metric
(`flatDist_comparison`).
-/

open MeasureTheory Filter Topology

namespace SharpLSI

variable {d : ℕ}

/-- The Euler–Lagrange density `e^{-V-W*μ}/∫ e^{-V-W*μ} dm` (manuscript (4.1)). -/
noncomputable def elDensity (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (x : Torus d) : ℝ :=
  Real.exp (-V x - convMeas W μ x) / ∫ y, Real.exp (-V y - convMeas W μ y) ∂haar d

/-- Lemma 4.1. -/
theorem minimizers_regular {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    (∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      (μ : Measure (Torus d)) = densMeasure (elDensity V W μ)) ∧
    (∃ (c C : ℝ) (L : NNReal), 0 < c ∧ ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      (∀ x, c ≤ elDensity V W μ x ∧ elDensity V W μ x ≤ C) ∧ LipschitzWith L (elDensity V W μ)) ∧
    (∀ μs : ℕ → ProbabilityMeasure (Torus d), (∀ n, IsMinimizer V W (μs n)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ ∧
        Tendsto (fun n => w1infDist (elDensity V W (μs (φ n))) (elDensity V W μ)) atTop
          (𝓝 0)) := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  exact ⟨fun μ hμ => minimizer_eq_elDensity hyp hμ, ⟨c, C, L, hc, fun μ _ => hb μ inferInstance⟩,
    fun μs hμs => minimizers_compact hyp μs hμs⟩

end SharpLSI
