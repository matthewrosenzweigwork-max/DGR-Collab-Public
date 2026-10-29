import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Defs.D14_Conditional
import SharpSymmetricLSI.Paper.CenteredEntropy
import SharpSymmetricLSI.Paper.Sec5_4
import SharpSymmetricLSI.Statements.R16_Lemma_4_2

/-!
# R19: Lemma 5.2 (`lem:reference-entropy`), reference entropy and the centered partition function

Manuscript Lemma 5.2, (5.6), (5.7), and the identities (5.9), (5.10) of its proof. Assume (1.2),
`r_* > 0`, `μ` the minimizer. There are `C < ∞` and `p > 1`, independent of `N`, with
(5.6) `H(ν|μ^{⊗N}) ≤ C(H(ν|P_N) + 1)` for symmetric `ν`; (5.7) `|log K_N| ≤ C` and
`∫ p_N^p dμ^{⊗N} ≤ C`, `p_N = K_N^{-1} e^{-U_N}`. Also (5.9) `log K_N ≥ -½ ∫ K(x,x) dμ(x)` and
(5.10) `H(ν|P_N) = H_0 + E_ν U_N + log K_N` when `H_0 = H(ν|μ^{⊗N}) < ∞`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- Lemma 5.2. -/
theorem reference_entropy {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ C p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      (∀ ν : Measure (Config N d), IsProbabilityMeasure ν → IsSymmetricMeasure ν →
        klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
          ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1)) ∧
      |Real.log (centeredPartition W μ N)| ≤ C ∧
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C := by
  exact reference_entropy_of hyp hμ (gap_ge_entropy hd hyp hr hμ)

/-- (5.9) and (5.10). -/
theorem centered_entropy_identities {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {N : ℕ} (hN : 1 ≤ N) :
    -(∫ x, centeredKernel W μ x x ∂(μ : Measure (Torus d))) / 2 ≤
        Real.log (centeredPartition W μ N) ∧
    ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ →
      ((klDiv ν (gibbs V W N)).toReal =
        (klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal +
          ∫ X, Ucentered W μ N X ∂ν + Real.log (centeredPartition W μ N)) ∧
      klDiv ν (gibbs V W N) ≠ ⊤ := by
  exact centered_entropy_identities_aux hyp hμ hN

end SharpLSI
