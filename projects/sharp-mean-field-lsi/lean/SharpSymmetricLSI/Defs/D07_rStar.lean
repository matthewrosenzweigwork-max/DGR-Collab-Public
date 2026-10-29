import SharpSymmetricLSI.Defs.D06_Dissipation
import SharpSymmetricLSI.Paper.AdmFinite
import SharpSymmetricLSI.Paper.AdmNonempty

/-!
# D7: the mean-field Polyak–Łojasiewicz constant (1.7)

`r_* = inf { D(ρ) / (2 G(ρ)) : ρ ≥ 0, ∫ ρ dm = 1, √ρ ∈ H^1(m), G(ρ) > 0 }`, in `ℝ≥0∞`.
For `d ≥ 1` the admissible set is nonempty (`admissible_nonempty`), so the `⊤` convention for the
empty infimum never applies (for `d = 0` the torus is a point, every candidate has `G = 0`, and
`r_* = ⊤`); admissible densities have finite gap (`gap_lt_top_of_admissible`).
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- The admissible densities of (1.7). -/
def Admissible (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) : Prop :=
  (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x ∂haar d = 1 ∧ MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
    0 < gap V W (densMeasure ρ)

/-- `r_*` (manuscript (1.7)). -/
noncomputable def rStar (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : ℝ≥0∞ :=
  ⨅ ρ ∈ {ρ | Admissible V W ρ}, dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal)

/-- Sanity lemma for D7: under (1.2) and `d ≥ 1` the admissible set of (1.7) is nonempty. -/
theorem admissible_nonempty {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) : ∃ ρ, Admissible V W ρ :=
  admissible_nonempty_aux hd hyp

/-- Sanity lemma for D7 (manuscript, after (1.7)): admissible densities have finite entropy
and dissipation, hence finite gap. -/
theorem gap_lt_top_of_admissible {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρ : Admissible V W ρ) :
    gap V W (densMeasure ρ) < ⊤ ∧ dissipation V W ρ < ⊤ :=
  gap_lt_top_aux hyp hρ.1 hρ.2.1 hρ.2.2.1

end SharpLSI
