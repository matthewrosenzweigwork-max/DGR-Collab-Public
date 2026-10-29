import SharpSymmetricLSI.Statements.R02_Prop_2_1
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Paper.Thm11Assembly
import SharpSymmetricLSI.Statements.R03_Prop_2_2
import SharpSymmetricLSI.Statements.R04_Prop_2_3

/-!
# R1: Theorem 1.1 (`thm:sharp`), sharp symmetric logarithmic Sobolev limit

Manuscript Theorem 1.1, (1.9), (1.10). Under (1.2):
* (1.9) `lim_{N→∞} r_N^sym = r_*` (in `ℝ≥0∞`).
* If `r_* > 0`: the minimizer `μ` of `F` is unique, its density is strictly positive and
  Lipschitz, and its second variation is strictly positive on `L²_0(μ)`. The second variation
  is the quadratic form `⟨h,(I+T)h⟩_{L²(μ)}` (`secondVar`; that it represents the second
  variation is part of Proposition 2.1, R2).
* (1.10) for every `0 < r < r_*` there is `N_r < ∞` with `Ent_{P_N}(f²) ≤ (2/r) ℰ_N(f)` for
  `N ≥ N_r` and every real symmetric `f ∈ H^1(P_N)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- The finite-`N` conclusion (1.10) of Theorem 1.1. -/
def FiniteNConclusion (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ENNReal.ofReal r < rStar V W →
    ∃ Nr : ℕ, ∀ N : ℕ, Nr ≤ N → ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f → IsSymmetric f →
        ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / r) * energy V W N f

/-- Theorem 1.1, (1.9). -/
theorem sharp_symmetric_lsi_limit {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    Tendsto (fun N => rSym V W N) atTop (𝓝 (rStar V W)) := by
  exact limit_of_finiteN hd hyp (finiteN_of hd hyp (fun hr => prop_defective hd hyp hr)
    (fun hr => prop_compactness hd hyp hr))

/-- Theorem 1.1, the equilibrium assertions when `r_* > 0`. -/
theorem equilibrium_of_rStar_pos {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    (∃! μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ) ∧
    ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      (∃ p, HasPosLipDensity μ p) ∧
      ∀ h : Torus d → ℝ, MemL20 μ h → ¬ (h =ᵐ[(μ : Measure (Torus d))] 0) →
        0 < secondVar W μ h := by
  exact equilibrium_of_rStar_pos_aux hd hyp hr

/-- Theorem 1.1, (1.10). -/
theorem sharp_symmetric_lsi_finiteN {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) : FiniteNConclusion V W := by
  exact finiteN_of hd hyp (fun hr => prop_defective hd hyp hr)
    (fun hr => prop_compactness hd hyp hr)

end SharpLSI
