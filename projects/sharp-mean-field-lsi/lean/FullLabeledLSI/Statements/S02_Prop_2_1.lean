import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Sec2AssemblyA

/-!
# S2: Proposition 2.1 (`prop:variational-input`), variational upper bound and positivity

Manuscript Proposition 2.1, (2.1). Under (1.2), `limsup_N r_N^all ≤ r_ms ≤ r_*`.
If `r_* > 0`, then `0 < r_ms ≤ r_LS(μ)`, where `μ` is the equilibrium (the unique minimizer of
`F`, Proposition 2.1 of the symmetric manuscript); the statement is made for every minimizer.

Also the sentence after (1.13): simultaneous heat regularization of a finite family gives the same
infimum over families of smooth strictly positive densities (`rMs_eq_smooth_inf`; used in the
proofs of Proposition 3.3 and Corollary 8.1).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Proposition 2.1, (2.1). -/
theorem upper_comparison {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    limsup (fun N => rAll V W N) atTop ≤ rMs V W ∧ rMs V W ≤ rStar V W := by
  exact ⟨limsup_rAll_le_rMs hd hyp, rMs_le_rStar⟩

/-- Proposition 2.1, positivity and the equilibrium bound. -/
theorem rMs_pos_le_rLS {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ) :
    0 < rMs V W ∧ rMs V W ≤ rLS (μ : Measure (Torus d)) := by
  exact rMs_pos_le_rLS_aux hd hyp hr μ hμ

/-- Manuscript, after (1.13): `r_ms` is also the infimum over smooth strictly positive families. -/
theorem rMs_eq_smooth_inf {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    rMs V W = ⨅ F ∈ {F : Family d | MsAdmissible V W F ∧
        ∀ a, IsSmoothT (F.ρ a) ∧ ∀ x, 0 < F.ρ a x},
      msDiss V W F / (2 * (msGap V W F).toENNReal) := by
  exact rMs_eq_smooth_inf_aux hd hyp

end SharpLSI.FL
