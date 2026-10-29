import SharpSymmetricLSI.Defs.D14_Conditional
import SharpSymmetricLSI.Paper.CondEntropy4
import SharpSymmetricLSI.Paper.CondEmpirical

/-!
# R18: Lemma 5.1 (`lem:conditional`), summed conditional dependence

Manuscript Lemma 5.1, (5.3)–(5.5). Let `ν` be a symmetric probability on `(𝕋^d)^N` with
`H_0 = H(ν | μ^{⊗N}) < ∞`. Then `h_j` is nonnegative (automatic in `ℝ≥0∞`) and nondecreasing,
`∑_{j<N} h_j = H_0`, and (5.3) `D_{j,k} = ∑_{a<k} h_{j+a} - k h_j ≤ k(h_{j+k-1} - h_j)`;
(5.4) for `ℓ = N - M`, `M ≥ k`: `∑_{j<ℓ} D_{j,k} ≤ k(k-1)H_0/(M-k+2)`; (5.5) for bounded
measurable `B` on `(𝕋^d)^k` and `M/N ≥ δ > 0`:
`|∑_{j<ℓ} E_ν B(ρ_j^{⊗k}) - ℓ E_ν B(L_N^{⊗k})| ≤ C_{k,B}(1 + √(H_0/δ))`.

The reference `μ` is any probability on `𝕋^d` (the manuscript applies the lemma with the
minimizer; the lemma does not use any property of `μ`). REVIEW. In (5.3) the subtraction is
in `ℝ≥0∞` (truncated), exact because `h` is nondecreasing; `H_0 < ∞` makes all terms finite.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- Lemma 5.1. -/
theorem summed_dependence (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ}
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) :
    (∀ j, j + 1 < N → hCondT ν μ j ≤ hCondT ν μ (j + 1)) ∧
    ∑ j ∈ Finset.range N, hCondT ν μ j = klDiv ν (Measure.pi fun _ : Fin N => μ) ∧
    (∀ j k, j < N → j + k ≤ N → 1 ≤ k →
      DCondT ν j k = (∑ a ∈ Finset.range k, hCondT ν μ (j + a)) - k * hCondT ν μ j ∧
      DCondT ν j k ≤ k * (hCondT ν μ (j + k - 1) - hCondT ν μ j)) ∧
    (∀ M k, M ≤ N → k ≤ M → 1 ≤ k →
      ∑ j ∈ Finset.range (N - M), DCondT ν j k ≤
        ((k * (k - 1) : ℕ) : ℝ≥0∞) / ((M - k + 2 : ℕ) : ℝ≥0∞) *
          klDiv ν (Measure.pi fun _ : Fin N => μ)) := by
  exact summed_dependence_aux μ ν hsym hH

/-- Lemma 5.1, (5.5): conditional products versus the empirical tensor power. -/
theorem conditional_empirical (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (k : ℕ)
    (B : (Fin k → Torus d) → ℝ) (hB : Measurable B) (hBb : ∃ c, ∀ z, |B z| ≤ c) :
    ∃ C : ℝ, ∀ (N M : ℕ) (δ : ℝ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      IsSymmetricMeasure ν → klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
      M ≤ N → k ≤ M → 0 < δ → δ ≤ (M : ℝ) / N →
      |∑ j ∈ Finset.range (N - M), condProductMean ν k B j -
          ((N - M : ℕ) : ℝ) * ∫ X, empiricalTensor k B X ∂ν| ≤
        C * (1 + Real.sqrt ((klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal / δ)) := by
  exact conditional_empirical_aux μ k B hB hBb

end SharpLSI
