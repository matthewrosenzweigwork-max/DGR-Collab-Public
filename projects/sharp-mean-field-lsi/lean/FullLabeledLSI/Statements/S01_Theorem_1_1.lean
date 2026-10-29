import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Thm11Assembly

/-!
# S1: Theorem 1.1 (`thm:limit`), sharp full-labeled logarithmic Sobolev limit

Manuscript Theorem 1.1, (1.14), (1.15). Under (1.2), `r_N^all → r_ms`. If `r_* > 0`, then
`r_ms > 0` and for every `0 < r < r_ms` there is `N_r` with
`Ent_{P_N}(f²) ≤ (2/r) ℰ_N(f)` for all `N ≥ N_r` and all real `f ∈ H^1(P_N)` (no symmetry).
If `r_* = 0`, then `r_ms = 0` (and the limit is zero).
As in the symmetric statement (R1), `d ≥ 1` is assumed: for `d = 0` the torus is a point.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The eventual inequality (1.15) for every rate below `r_ms`. -/
def FiniteNConclusionAll (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rMs V W →
    ∃ Nr : ℕ, ∀ N : ℕ, Nr ≤ N → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f →
        ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / r) * energy V W N f

/-- Theorem 1.1, (1.14). -/
theorem full_labeled_lsi_limit {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W)) := by
  exact limit_all_aux hd hyp

/-- Theorem 1.1, the case `r_* > 0`: `r_ms > 0` and (1.15). -/
theorem full_labeled_lsi_finiteN {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    0 < rMs V W ∧ FiniteNConclusionAll V W := by
  exact ⟨rMs_pos_aux hd hyp hr, finiteN_all_core hd hyp hr⟩

/-- Theorem 1.1, the case `r_* = 0`: `r_ms = 0`. -/
theorem rMs_eq_zero_of_rStar_eq_zero {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    {KV KW : ℝ} (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : rStar V W = 0) :
    rMs V W = 0 := by
  exact rMs_eq_zero_aux hr

end SharpLSI.FL
