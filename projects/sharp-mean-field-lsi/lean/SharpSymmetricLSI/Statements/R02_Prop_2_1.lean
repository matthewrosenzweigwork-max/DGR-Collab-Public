import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D13_Equilibrium
import SharpSymmetricLSI.Paper.Prop21Assembly1
import SharpSymmetricLSI.Statements.R16_Lemma_4_2

/-!
# R2: Proposition 2.1 (`prop:equilibrium`), mean-field equilibrium and entropy coercivity

Manuscript Proposition 2.1, (2.1), (2.2). Assume (1.2) and `r_* > 0`. Then `F` has a unique
minimizer `μ`, with a strictly positive Lipschitz density; the second variation of `F` at `μ`
in the coordinate `ρ = μ(1+h)` is represented by `I + T`; and there are `σ > 0`, `c ∈ (0,1]`
with `I + T ≥ σ I` on `L²_0(μ)` and `G(ρ) ≥ c H(ρ|μ)` for every finite-entropy probability `ρ`.

Encoding of "the second variation is represented by `I+T`": for every bounded measurable
mean-zero `h`, `G(μ(1+th)) = (t²/2) ⟨h,(I+T)h⟩_{L²(μ)} + o(t²)` as `t → 0` (the first variation
vanishes at a minimizer). REVIEW. Lipschitz (existential constant) is w.r.t. Mathlib's product
(sup) metric on `𝕋^d = (ℝ/ℤ)^d`, equivalent to the flat metric (`flatDist_comparison`).
-/

open MeasureTheory Filter Topology InformationTheory

namespace SharpLSI

variable {d : ℕ}

/-- `μ` has a strictly positive Lipschitz density `p` w.r.t. Haar measure. -/
def HasPosLipDensity (μ : ProbabilityMeasure (Torus d)) (p : Torus d → ℝ) : Prop :=
  (∀ x, 0 < p x) ∧ (∃ L, LipschitzWith L p) ∧ (μ : Measure (Torus d)) = densMeasure p

/-- The conclusion of Proposition 2.1. -/
def EquilibriumConclusion (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  (∃! μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ) ∧
  ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
    ∃ p : Torus d → ℝ, HasPosLipDensity μ p ∧
      -- second variation in the coordinate `ρ = μ(1+h)` is `⟨h,(I+T)h⟩`
      (∀ h : Torus d → ℝ, Measurable h → (∃ B, ∀ x, |h x| ≤ B) → ∫ x, h x ∂(μ : Measure (Torus d)) = 0 →
        Tendsto (fun t : ℝ => (gap V W (densMeasure (fun x => p x * (1 + t * h x)))).toReal / t ^ 2)
          (𝓝[≠] 0) (𝓝 (secondVar W μ h / 2))) ∧
      ∃ σ : ℝ, 0 < σ ∧ ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
        (∀ h, MemL20 μ h → σ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h) ∧
        ∀ ρ : ProbabilityMeasure (Torus d), klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
          (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ENNReal) : EReal) ≤
            gap V W ρ

/-- Proposition 2.1. -/
theorem prop_equilibrium {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    EquilibriumConclusion V W := by
  obtain ⟨⟨μ₀, hμ₀⟩, -, -⟩ := exists_minimizer hyp
  refine ⟨⟨μ₀, hμ₀, fun ν hν => (minSet_singleton hd hyp hr hμ₀).2.1 ν hν⟩, fun μ hμ => ?_⟩
  obtain ⟨-, -, -, σ, hσ, hσ'⟩ := minSet_singleton hd hyp hr hμ
  obtain ⟨c, hc, hc1, hcG⟩ := gap_ge_entropy hd hyp hr hμ
  obtain ⟨cl, Cu, L, hcl, hbd⟩ := elDensity_bounds hyp
  obtain ⟨-, hL⟩ := hbd (μ : Measure (Torus d)) inferInstance
  exact ⟨elDens V W μ, ⟨fun x => (elDensity_props hyp (μ : Measure (Torus d))).2.1 x, ⟨L, hL⟩,
    minimizer_eq_elDensity hyp hμ⟩, fun h hm hb hh0 => tendsto_gap_pert hyp hμ hm hb hh0,
    σ, hσ, c, hc, hc1, hσ', hcG⟩

end SharpLSI
