import FullLabeledLSI.Defs.F04_Reveal
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Sec5Perm

/-!
# S19: Lemma 5.2 (`lem:reference-all`), reference estimates without permutation symmetry

Manuscript Lemma 5.2, (5.3)–(5.5). Assume (1.2) and `r_* > 0` (standing in Section 5); `μ` is the
equilibrium, `Q_N = μ^{⊗N}`, `U_N = Ucentered W μ N` (D13). There is `C`, independent of `N` and `ν`,
such that for every probability `ν` of finite relative entropy `H = H(ν|P_N)`, without symmetry:
`H(ν|μ^{⊗N}) ≤ C(H + 1)`, `E_ν|∇U_N|² ≤ C(H + 1)`, and, on the finite-Fisher-information domain,
`I(ν|μ^{⊗N}) ≤ 2 I(ν|P_N) + C(H + 1)`.

Encodings: `|∇U_N|² = ∑ᵢ |∇ᵢU_N|² = gradSqC (Ucentered W μ N)`; `N ≥ 1`; all quantities in `ℝ≥0∞`;
`C` real (`ENNReal.ofReal C`).
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Lemma 5.2. -/
theorem reference_all {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      klDiv ν (gibbs V W N) ≠ ⊤ →
        klDiv ν (Measure.pi fun _ => (μ : Measure (Torus d))) ≤
            ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) ∧
        ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
            ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1) ∧
        (fisherInfoC ν (gibbs V W N) < ⊤ →
          fisherInfoC ν (Measure.pi fun _ => (μ : Measure (Torus d))) ≤
            2 * fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C * (klDiv ν (gibbs V W N) + 1)) := by
  exact reference_all_aux hd hyp hr μ hμ

end SharpLSI.FL
