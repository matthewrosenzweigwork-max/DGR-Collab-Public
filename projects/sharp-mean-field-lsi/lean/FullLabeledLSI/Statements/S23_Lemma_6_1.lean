import FullLabeledLSI.Defs.F05_FiniteRank
import SharpSymmetricLSI.Defs.D07_rStar
import FullLabeledLSI.Paper.Sec6Rank1
import FullLabeledLSI.Paper.Sec6Rank2
import FullLabeledLSI.Paper.Sec6Rank3

/-!
# S23: Lemma 6.1 (`lem:rank-errors`), finite-rank errors and rate limits

Manuscript Lemma 6.1, (6.3), (6.4). Assume (1.2), `r_* > 0`; `μ` the equilibrium, `(e, lam)` a
reference eigenbasis, `K_R` the finite-rank kernels (F5), `C = (I+T)^{-1}`, and for each large `R`,
`C_R = (I + T_R)^{-1}`. For every finite `q ≥ 1`, `sup_N ‖U_N - U_{N,R}‖_{L^q(Q_N)} → 0`; moreover
`κ_R → K_∞`, `λ_{G,R} → λ_G`, `b_R → b`.

Encodings: `U_N = Ucentered W μ N`, `Q_N = μ^{⊗N}`, `N ≥ 1`; the supremum is in `ℝ≥0∞` (`eLpNorm`);
`K_∞ = Kinf W μ Q` for the second chaos `Q` of `T` (D16); `λ_{G,R} = lamG (lamShift lam) (CR R)`.
The manuscript takes ranks `R` large enough that `I + T_R ≥ (σ/2) I`, which makes `I + T_R`
invertible; the statement assumes only the consequence used, that `CR R` inverts `I + T_R` for all
large `R` (a weaker hypothesis, so the Lean statement is at least as strong).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Lemma 6.1. -/
theorem rank_errors {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W μ e) C)
    (Q : (ℕ → ℝ) → ℝ) (hQ : IsSecondChaos (Tmat W μ e) Q)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, IsInverseOfIPlus (A.a R) (CR R)) :
    (∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      Tendsto (fun R => ⨆ N ∈ {N : ℕ | 1 ≤ N},
          eLpNorm (fun X => Ucentered W μ N X - URN A R N X) q
            (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))))
        atTop (𝓝 0)) ∧
    Tendsto (fun R => kappaR A R) atTop (𝓝 (Kinf W μ Q)) ∧
    Tendsto (fun R => lamG (lamShift lam) (CR R)) atTop (𝓝 (lamG (lamShift lam) C)) ∧
    Tendsto (fun R => bRate (μ : Measure (Torus d)) lam (CR R)) atTop
      (𝓝 (bRate (μ : Measure (Torus d)) lam C)) :=
  ⟨rank_errors_part1 hyp μ e lam he A,
    rank_errors_part2 hd hyp hr μ hμ e lam he Q hQ A,
    rank_errors_part3 hd hyp hr μ hμ e lam he C hC A CR hCR,
    rank_errors_part4 hd hyp hr μ hμ e lam he C hC A CR hCR⟩

end SharpLSI.FL
