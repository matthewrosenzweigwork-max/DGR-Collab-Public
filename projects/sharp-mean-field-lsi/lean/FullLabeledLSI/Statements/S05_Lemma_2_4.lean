import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Lem24

/-!
# S5: Lemma 2.4 (`lem:UI`), uniform integrability from one defective inequality

Manuscript Lemma 2.4. Assume (1.2) and `r_* > 0`. If `sup_N (‖g_N‖²_{L²(P_N)} + ℰ_N(g_N)) < ∞`,
then `g_N²` is uniformly integrable under `P_N`.

Encodings: as in R4 of the symmetric project, uniform integrability on varying probability spaces is
`∀ ε > 0, ∃ M, ∀ k, ∫_{g_k² > M} g_k² dP_{N_k} ≤ ε`. The lemma is stated for an arbitrary sequence of
particle numbers `Ns k ≥ 1` (the proof uses Proposition 2.2, which is uniform in `N ≥ 1`); this
contains the manuscript's sequence indexed by `N` and the subsequences used in Section 2.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Lemma 2.4. -/
theorem unifIntegrable_sq {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (Ns : ℕ → ℕ) (hNs : ∀ k, 1 ≤ Ns k) (g : (k : ℕ) → Config (Ns k) d → ℝ)
    (hg : ∀ k, MemH1C (gibbs V W (Ns k)) (g k))
    (hB : ∃ B : NNReal, ∀ k,
      (∫⁻ X, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns k)) + energy V W (Ns k) (g k) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
      ∫⁻ X in {X | M < g k X ^ 2}, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (Ns k) ≤
        ENNReal.ofReal ε := by
  exact unifIntegrable_sq_aux hd hyp hr Ns hNs g hg hB

end SharpLSI.FL
