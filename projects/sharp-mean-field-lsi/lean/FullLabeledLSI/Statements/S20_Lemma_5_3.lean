import FullLabeledLSI.Defs.F04_Reveal
import FullLabeledLSI.Paper.Sec5Chain

/-!
# S20: Lemma 5.3 (`lem:random-chain`), the random chain identities

Manuscript Lemma 5.3, (5.9)–(5.11), for `ν` with a smooth positive density (start of Section 5.2):
`∑_{j<N} h_j = H_0 = H(ν|μ^{⊗N})`, `h_{j+1} - h_j = d_{j,2} ≥ 0`,
`d_{j,k} = ∑_{a<k} (h_{j+a} - h_j)`, and `∑_{j<ℓ} d_{j,k} ≤ k(k-1) H_0 / (M - k + 2)` for `ℓ = N - M`,
`M ≥ k`.

Encodings: the reference `μ` is any probability on `𝕋^d` (the identities do not use the equilibrium
property). Identities are written additively in `ℝ≥0∞`: `h_{j+1} = h_j + d_{j,2}` for `j + 2 ≤ N`, and
`d_{j,k} + k h_j = ∑_{a<k} h_{j+a}` for `1 ≤ k`, `j + k ≤ N`. The ranges of `j`, `k` are those for
which the objects are defined (`j + k ≤ N`).
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-- Lemma 5.3, (5.9) first identity. -/
theorem random_chain_sum (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hν : HasSmoothPosDensity ν) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∑ j ∈ Finset.range N, hRev ν μ j = klDiv ν (Measure.pi fun _ => μ) := by
  exact chain_sum ν μ

/-- Lemma 5.3, (5.9) second identity. -/
theorem random_chain_step (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hν : HasSmoothPosDensity ν) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (j : ℕ) (hj : j + 2 ≤ N) :
    hRev ν μ (j + 1) = hRev ν μ j + dRev ν j 2 := by
  exact chain_step ν μ hj

/-- Lemma 5.3, (5.10). -/
theorem random_chain_k (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hν : HasSmoothPosDensity ν) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (j k : ℕ) (hk : 1 ≤ k) (hjk : j + k ≤ N) :
    dRev ν j k + k * hRev ν μ j = ∑ a ∈ Finset.range k, hRev ν μ (j + a) := by
  exact chain_k ν μ hk hjk

/-- Lemma 5.3, (5.11). -/
theorem random_chain_sum_d (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hν : HasSmoothPosDensity ν) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (k M : ℕ) (hkM : k ≤ M) (hMN : M ≤ N) :
    ∑ j ∈ Finset.range (N - M), dRev ν j k ≤
      (k * (k - 1) : ℝ≥0∞) * klDiv ν (Measure.pi fun _ => μ) / ((M - k + 2 : ℕ) : ℝ≥0∞) := by
  exact chain_sum_d ν μ k M hkM hMN

end SharpLSI.FL
