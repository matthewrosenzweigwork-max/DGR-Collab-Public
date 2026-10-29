import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D15_Forces
import SharpSymmetricLSI.Paper.CondForce4

/-!
# R21: Lemma 5.4 (`lem:force-comparison`), conditional force comparison

Manuscript Lemma 5.4, (5.17). Assume (1.2), `r_* > 0`, `μ` the minimizer. For a symmetric
probability `ν` with `H_0 = H(ν|μ^{⊗N}) < ∞`, `ℓ = N - M`, `M ≥ 3`, `M/N ≥ δ > 0`:
`∑_{j<ℓ} E_ν |B_j(X_{j+1}) - E_ν[∇_{j+1}U_N | ℱ_j, X_{j+1}]|² ≤ C(1 + √(H_0/δ))`.
The conditional expectation is w.r.t. `σ(X_1, …, X_j, X_{j+1})`, taken componentwise
(`MeasureTheory.condExp`). Particle `j+1` is Lean index `j`.
-/

open MeasureTheory InformationTheory

namespace SharpLSI

variable {d : ℕ}

/-- The σ-algebra `ℱ_j ∨ σ(X_{j+1})` on `(𝕋^d)^N`. -/
abbrev pastAndNext {N : ℕ} (j : ℕ) (hj : j < N) : MeasurableSpace (Config N d) :=
  MeasurableSpace.comap (fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩)) inferInstance

/-- The summand of (5.17) for a fixed `j < N`. -/
noncomputable def forceComparisonTerm (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    {N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (j : ℕ) : ℝ :=
  if hj : j < N then
    ∫ X, ∑ k, (condForce W μ ν j hj (past j hj.le X) (X ⟨j, hj⟩) k -
      (ν[fun Y => weakGradC (Ucentered W μ N) Y ⟨j, hj⟩ k | pastAndNext j hj]) X) ^ 2 ∂ν
  else 0

/-- Lemma 5.4. -/
theorem conditional_force {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ C : ℝ, ∀ (N M : ℕ) (δ : ℝ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      IsSymmetricMeasure ν →
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ →
      M ≤ N → 3 ≤ M → 0 < δ → δ ≤ (M : ℝ) / N →
      ∑ j ∈ Finset.range (N - M), forceComparisonTerm W μ ν j ≤
        C * (1 + Real.sqrt
          ((klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal / δ)) := by
  exact conditional_force_aux hyp hμ

end SharpLSI
