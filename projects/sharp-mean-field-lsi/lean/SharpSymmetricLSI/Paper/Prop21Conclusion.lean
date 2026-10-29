import SharpSymmetricLSI.Statements.R02_Prop_2_1

/-!
# The consequences of Proposition 2.1 used downstream (Phase 3, lane D)

`Prop21Conclusion V W μ` bundles the conclusions of Proposition 2.1 (R02 `EquilibriumConclusion`)
at a minimizer `μ`: uniqueness, the positive Lipschitz density of `μ` together with the second
variation `⟨h,(I+T)h⟩` in the coordinate `ρ = μ(1+h)`, `I + T ≥ σ I` (4.13), and the entropy
coercivity of Lemma 4.2, each exactly as R02 states it. The
Prop-2.1-dependent results (R19 (5.6)–(5.7), R20 (5.14)–(5.15), R3, R27, R30, R31, R33) are proved
as conditional lemmas taking `h21 : Prop21Conclusion V W μ`; each frozen theorem closes as the
conditional lemma plus Proposition 2.1 (`prop21Conclusion_of_equilibrium`). For the cosine
interaction (R8) the conclusion is obtained directly from convexity.
-/

open MeasureTheory InformationTheory

namespace SharpLSI

variable {d : ℕ}

/-- What the downstream proofs use from Proposition 2.1. -/
structure Prop21Conclusion (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (μ : ProbabilityMeasure (Torus d)) : Prop where
  minimizer : IsMinimizer V W μ
  unique : ∀ ν : ProbabilityMeasure (Torus d), IsMinimizer V W ν → ν = μ
  density : ∃ p : Torus d → ℝ, HasPosLipDensity μ p ∧
    (∀ h : Torus d → ℝ, Measurable h → (∃ B, ∀ x, |h x| ≤ B) →
      ∫ x, h x ∂(μ : Measure (Torus d)) = 0 →
      Filter.Tendsto (fun t : ℝ => (gap V W (densMeasure (fun x => p x * (1 + t * h x)))).toReal /
          t ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (secondVar W μ h / 2)))
  sigma : ∃ σ : ℝ, 0 < σ ∧
    ∀ h, MemL20 μ h → σ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h
  coercive : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ρ : ProbabilityMeasure (Torus d),
    klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
      (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ENNReal) : EReal) ≤
        gap V W ρ

/-- Proposition 2.1 gives `Prop21Conclusion` at its minimizer. -/
theorem prop21Conclusion_of_equilibrium {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    (h : EquilibriumConclusion V W) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    Prop21Conclusion V W μ := by
  obtain ⟨⟨μ0, hμ0, huniq⟩, hall⟩ := h
  obtain ⟨p, hp, hvar, σ, hσ, c, hc, hc1, hsig, hcoer⟩ := hall μ hμ
  have hμμ0 : μ = μ0 := huniq μ hμ
  exact ⟨hμ, fun ν hν => (huniq ν hν).trans hμμ0.symm, ⟨p, hp, hvar⟩, ⟨σ, hσ, hsig⟩,
    ⟨c, hc, hc1, hcoer⟩⟩

end SharpLSI
