import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D13_Equilibrium
import FullLabeledLSI.Paper.Lem25

/-!
# S6: Lemma 2.5 (`lem:PI`), an unrestricted Poincaré lower bound

Manuscript Lemma 2.5, (2.5). Assume (1.2) and `r_* > 0`. Then `liminf_N λ_N^all ≥ b`, with
`λ_N^all = lamAll` (D9 of the symmetric project) and `b = min{r_LS(μ), λ_G}` as in S4.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Lemma 2.5, (2.5). -/
theorem liminf_lamAll_ge {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    bRate (μ : Measure (Torus d)) lam C ≤ liminf (fun N => lamAll V W N) atTop := by
  exact liminf_lamAll_ge_aux hd hyp hr μ hμ e lam he C hC

end SharpLSI.FL
