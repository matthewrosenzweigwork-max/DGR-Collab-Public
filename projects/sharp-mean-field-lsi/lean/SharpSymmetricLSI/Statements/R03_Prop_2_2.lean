import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Paper.Defective29
import SharpSymmetricLSI.Statements.R16_Lemma_4_2

/-!
# R3: Proposition 2.2 (`prop:defective`), defective logarithmic Sobolev inequality

Manuscript Proposition 2.2, (2.3). Assume (1.2) and `r_* > 0`. For every `0 < r < r_*` there is
`B_r < ∞`, independent of `N`, with
`Ent_{P_N}(f²) ≤ (2/r) ℰ_N(f) + B_r ∫ f² dP_N` for all `N ≥ 1` and symmetric `f ∈ H^1(P_N)`.
(`B_r` is taken in `ℝ≥0`; a finite real constant can always be replaced by its positive part.)
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- The conclusion of Proposition 2.2. -/
def DefectiveConclusion (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rStar V W →
    ∃ B : NNReal, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f → IsSymmetric f →
        ent (gibbs V W N) (fun X => f X ^ 2) ≤
          ENNReal.ofReal (2 / r) * energy V W N f +
            (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N

/-- Proposition 2.2. -/
theorem prop_defective {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    DefectiveConclusion V W := by
  exact prop_defective_of hd hyp (fun μ hμ => gap_ge_entropy hd hyp hr hμ)

end SharpLSI
