import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Paper.Sec3Dilute

/-!
# S9: Proposition 3.3 (`prop:equilibrium-families`), families with average equal to equilibrium

Manuscript Proposition 3.3, (3.8), (3.9). Assume (1.2) and `r_* > 0` (standing in Section 3.3).
The infimum in (1.13) restricted to admissible families with `ρ̄ = μ` (as measures) and positive
gap equals `r_LS(μ)`. ("In particular `r_ms ≤ r_LS(μ)`" is part of S2.)
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- Proposition 3.3. -/
theorem equilibrium_families {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ) :
    (⨅ F ∈ {F : Family d | MsAdmissible V W F ∧ densMeasure F.bar = (μ : Measure (Torus d))},
      msDiss V W F / (2 * (msGap V W F).toENNReal)) = rLS (μ : Measure (Torus d)) := by
  refine le_antisymm (equilibrium_inf_le_rLS hyp hμ) ?_
  exact le_iInf₂ fun F hF => rLS_le_quotient hyp hμ F hF.1.1 hF.2 hF.1.2

end SharpLSI.FL
