import FullLabeledLSI.Defs.F04_Reveal
import FullLabeledLSI.Paper.Sec5Products2

/-!
# S21: Lemma 5.4 (`lem:random-products`), bounded conditional product tests

Manuscript Lemma 5.4, (5.12). Let `A` be a bounded measurable function of `k` particle variables.
If `ℓ = N - M`, `M ≥ k` and `M/N ≥ τ > 0`, then
`|∑_{j<ℓ} E ∫ A dρ̄_S^{⊗k} - ℓ E_ν ∫ A dL_N^{⊗k}| ≤ C_{k,A,τ} (1 + √H_0)`.

Encodings: `ν` has a smooth positive density (start of Section 5.2) and `H_0 = H(ν|μ^{⊗N}) < ⊤`;
`μ` is any probability on `𝕋^d` (it enters only through `H_0`); the constant is chosen after `k`,
`τ` and `A` and is uniform in `N`, `M`, `ν`. `E` includes the uniform choice of the `j`-subset `S`.
`∫ A dL_N^{⊗k}` is `empiricalTensor k A` (D14).
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- `E ∫ A dρ̄_S^{⊗k}` at level `j` (average over `j`-subsets `S`). -/
noncomputable def condProductMeanS {N : ℕ} (ν : Measure (Config N d)) [IsFiniteMeasure ν]
    (k : ℕ) (A : (Fin k → Torus d) → ℝ) (j : ℕ) : ℝ :=
  ((Nat.choose N j : ℝ)⁻¹) * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    ∫ X, (∫ z, A z ∂Measure.pi (fun _ : Fin k => barCond ν S X)) ∂ν

/-- Lemma 5.4, (5.12). -/
theorem random_products (k : ℕ) (τ : ℝ) (hτ : 0 < τ) (A : (Fin k → Torus d) → ℝ)
    (hA : Measurable A) (hAb : ∃ a, ∀ z, |A z| ≤ a) :
    ∃ C : ℝ, ∀ (N M : ℕ), k ≤ M → M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
        (ν : Measure (Config N d)) [IsProbabilityMeasure ν], HasSmoothPosDensity ν →
        klDiv ν (Measure.pi fun _ => μ) ≠ ⊤ →
        |∑ j ∈ Finset.range (N - M), condProductMeanS ν k A j -
            ((N - M : ℕ) : ℝ) * ∫ X, empiricalTensor k A X ∂ν| ≤
          C * (1 + Real.sqrt (klDiv ν (Measure.pi fun _ => μ)).toReal) := by
  obtain ⟨C, hC⟩ := random_products_aux k τ hτ A hA hAb
  refine ⟨C, fun N M hkM hMN hτM μ _ ν _ _ hH => ?_⟩
  exact hC N M hkM hMN hτM μ ν hH

end SharpLSI.FL
