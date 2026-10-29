import FullLabeledLSI.Infra.HypercontrHybrid6
import FullLabeledLSI.Infra.SpectralSetup

/-!
# `hybrid_poly_moment` from the equilibrium hypotheses

Lane-4 interface (plan 2b): for a minimizer `μ`, a reference eigenbasis `(e, lam)`, and `J, L, q`, there is
`K ≥ 0` independent of `N`, `B` and `c` with
`∫⁻ ofReal (|hybPoly e c B|^q) d(hybMeasure μ N J) ≤ ofReal (K * (√(∑ c²))^q)` for `SpectralCoeff lam L c`.
-/

open MeasureTheory SharpLSI
open scoped ENNReal

namespace SharpLSI.FL.Hyb

variable {d : ℕ}

theorem hybrid_poly_moment_min {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (J : ℕ) (L : ℝ) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam L c →
      ∫⁻ ω, ENNReal.ofReal (|hybPoly e c B ω| ^ q) ∂(hybMeasure (μ : Measure (Torus d)) N J) ≤
        ENNReal.ofReal (K * (Real.sqrt (∑ j, c j ^ 2)) ^ q) := by
  obtain ⟨eC, a, hac, hca, hC1, hae, ha, hrls, hlam0, hnn, h1, hmono, -⟩ :=
    Gross.torus_standing hd hyp hr μ hμ e lam he
  exact hybrid_poly_moment hac hca he hC1 hae ha hrls hlam0 hnn h1 hmono J L q

end SharpLSI.FL.Hyb
