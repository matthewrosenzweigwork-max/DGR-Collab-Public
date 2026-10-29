import FullLabeledLSI.Defs.F02_Constants
import FullLabeledLSI.Paper.Sec5LNJ
import SharpSymmetricLSI.Defs.D09_ParticleRates

/-!
# S3: Proposition 2.2 (`prop:defective`), uniform defective logarithmic Sobolev inequality

Manuscript Proposition 2.2, (2.2). Assume (1.2) and `r_* > 0`. For every `0 < r < r_ms` there is
`B_r < ∞`, independent of `N`, with
`Ent_{P_N}(f²) ≤ (2/r) ℰ_N(f) + B_r ∫ f² dP_N` for every `N ≥ 1` and every real `f ∈ H^1(P_N)`.
This is the symmetric project's `DefectiveConclusion` (R3) with `r_ms` in place of `r_*` and without
the symmetry condition. `B_r` is taken in `ℝ≥0`, as in R3.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The conclusion of Proposition 2.2. -/
def DefectiveConclusionAll (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rMs V W →
    ∃ B : NNReal, ∀ N : ℕ, 1 ≤ N → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f →
        ent (gibbs V W N) (fun X => f X ^ 2) ≤
          ENNReal.ofReal (2 / r) * energy V W N f +
            (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N

/-- Proposition 2.2. -/
theorem prop_defective_all {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    DefectiveConclusionAll V W := by
  exact prop_defective_all_aux hd hyp hr

end SharpLSI.FL
