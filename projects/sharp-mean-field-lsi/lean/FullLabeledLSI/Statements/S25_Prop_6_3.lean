import FullLabeledLSI.Defs.F05_FiniteRank
import SharpSymmetricLSI.Defs.D07_rStar
import FullLabeledLSI.Paper.Hybrid63AltA
import FullLabeledLSI.Paper.Hybrid63AltO

/-!
# S25: Proposition 6.3 (`prop:spectral`), the comparison expression on a spectral range

Manuscript Proposition 6.3, (6.25). Assume (1.2), `r_* > 0` (standing in Sections 6–7). Fix a
sufficiently large interaction rank `R` and a finite spectral level `L`. For every sequence `F_N` in
the range of `Π_{N,L}` with `sup_N ‖F_N‖_{L²(Q_N)} < ∞`, `liminf_N 𝒥_{N,R}(F_N) ≥ 0`.

Encodings: as in S23 for `μ, e, lam, A, CR`; "sufficiently large `R`" is `∃ R₀, ∀ R ≥ R₀`, with
`CR R` the inverse of `I + T_R` for all large `R` (the manuscript takes `R` large enough that
`I + T_R ≥ (σ/2) I`, which gives this inverse); `liminf ≥ 0` is `∀ ε > 0, eventually 𝒥 ≥ -ε`.
`Jexpr_terms_finite`: the three quantities that `Jexpr` reads through `toReal` (`ℰ⁰_N(F)`,
`Ent(F²)`, `b_R`) are finite on the spectral range, so `toReal` loses nothing there.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Proposition 6.3, (6.25). -/
theorem spectral_comparison {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, IsInverseOfIPlus (A.a R) (CR R)) :
    ∃ R₀ : ℕ, ∀ R, R₀ ≤ R → ∀ L : ℝ, ∀ F : (N : ℕ) → Config N d → ℝ,
      (∀ N, InSpectralRange e lam L (F N)) →
      (∃ B : ℝ, ∀ N, eLpNorm (F N) 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal B) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, -ε ≤ Jexpr A lam (CR R) R (F N) := by
  exact spectral_comparison_alt hd hyp hr μ hμ e lam he A CR hCR

/-- The `toReal` terms of `Jexpr` are finite on the spectral range. -/
theorem Jexpr_terms_finite {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    (∀ C : ℕ → ℕ → ℝ, bRate (μ : Measure (Torus d)) lam C < ⊤) ∧
    ∀ (L : ℝ) (N : ℕ) (F : Config N d → ℝ), InSpectralRange e lam L F →
      refEnergy (μ : Measure (Torus d)) F < ⊤ ∧
      ent (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) (fun X => F X ^ 2) < ⊤ := by
  exact Jexpr_terms_finite_alt hd hyp hr μ hμ e lam he

end SharpLSI.FL
