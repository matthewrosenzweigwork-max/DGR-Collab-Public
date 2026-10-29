import FullLabeledLSI.Defs.F01_Species

/-!
# F3: relative Fisher information between one-particle densities, score form (Section 3.1)

Manuscript, before Proposition 3.1: for smooth positive densities
`I(ρₐ|ρ̄) = ∫ |∇log ρₐ - ∇log ρ̄|² dρₐ`; on the finite-Fisher-information domain this has "the
corresponding almost-everywhere weighted-score interpretation", with the score of `ρ` equal to
`2∇√ρ/√ρ` on `{ρ > 0}` and `0` elsewhere (proof of Proposition 3.1).

`relFisher ρa ρb = ∫ |2∇√ρa - √ρa · score(ρb)|² dm`, `⊤` unless `ρa m ≪ ρb m` and
`√ρa, √ρb ∈ H^1(m)`. On `{ρa > 0}` the integrand is `|∇log ρa - ∇log ρb|² ρa`. The absolute
continuity guard makes the value `⊤` when `ρa` charges the zero set of `ρb`, as for `I(ρa|ρb)`
(review 1 of the statement layer); for `ρb = ρ̄` it always holds, since `θₐ ρₐ ≤ ρ̄`.

Why not `fisherInfo (densMeasure ρa) (densMeasure ρb)` (Infra/Entropy): that quantity requires
`√(ρa/ρb)` to have a weak gradient on the whole torus. When `ρb` vanishes, `ρa/ρb` can jump across
the zero set of `ρb` (two species supported on complementary half-circles), so `fisherInfo` is `⊤`
while the manuscript's weighted-score value is finite and (3.2) holds with the latter. For densities
bounded above and below the two agree (`relFisher_eq_fisherInfo`, F7). REVIEW.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

open Classical in
/-- The score `2∇√ρ/√ρ` of a density `ρ` on `{ρ > 0}`, `0` elsewhere. -/
noncomputable def score (ρ : Torus d → ℝ) (x : Torus d) (k : Fin d) : ℝ :=
  if 0 < ρ x then 2 * weakGrad (fun y => Real.sqrt (ρ y)) x k / Real.sqrt (ρ x) else 0

open Classical in
/-- `I(ρa|ρb)` in the weighted-score form of Section 3.1. -/
noncomputable def relFisher (ρa ρb : Torus d → ℝ) : ℝ≥0∞ :=
  if densMeasure ρa ≪ densMeasure ρb ∧ MemH1 (haar d) (fun x => Real.sqrt (ρa x)) ∧
      MemH1 (haar d) (fun x => Real.sqrt (ρb x)) then
    ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρa y)) x k -
      Real.sqrt (ρa x) * score ρb x k) ^ 2) ∂haar d
  else ⊤

end SharpLSI.FL
