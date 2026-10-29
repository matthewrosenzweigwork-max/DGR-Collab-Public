import FullLabeledLSI.Defs.F02_Constants
import FullLabeledLSI.Defs.F03_RelFisher
import SharpSymmetricLSI.Defs.D09_ParticleRates
import FullLabeledLSI.Statements.S01_Theorem_1_1
import FullLabeledLSI.Statements.S02_Prop_2_1
import FullLabeledLSI.Paper.Sec8Agree

/-!
# S12: Corollary 8.1 (`cor:agreement`), agreement of the limiting constants

Manuscript Corollary 8.1, (8.1)–(8.3). Assume (1.2). `lim r_N^all = lim r_N^sym` holds iff for every
finite admissible family with `ρ = ∑ₐ θₐ ρₐ`,
`∑ₐ θₐ [I(ρₐ|ρ) - 2 r_* H(ρₐ|ρ)] ≥ -[D(ρ) - 2 r_* G(ρ)]` (8.2).
It suffices to check (8.2) on smooth strictly positive species densities. When `r_* > 0`, a
necessary condition is `r_LS(μ) ≥ r_*` (8.3).

Encodings: "the two limits agree" is `∃ L, r_N^all → L ∧ r_N^sym → L` (both limits exist by S1 and
the symmetric Theorem 1.1). (8.2) is written in `ℝ` through `toReal`; every term is finite for an
admissible family (`criterion_terms_finite`, also asserted here), so `toReal` loses nothing.
`I(ρₐ|ρ)` is `relFisher` (F3).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The criterion (8.2) for one family. -/
def AgreementCriterion (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (F : Family d) : Prop :=
  -((dissipation V W F.bar).toReal - 2 * (rStar V W).toReal * (gap V W (densMeasure F.bar)).toReal)
    ≤ ∑ a, F.θ a * ((relFisher (F.ρ a) F.bar).toReal -
      2 * (rStar V W).toReal * (klDiv (densMeasure (F.ρ a)) (densMeasure F.bar)).toReal)

/-- The terms of (8.2) are finite for admissible families (so the `toReal` encoding is exact). -/
theorem criterion_terms_finite {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible) :
    rStar V W < ⊤ ∧ dissipation V W F.bar < ⊤ ∧ gap V W (densMeasure F.bar) < ⊤ ∧
      ⊥ < gap V W (densMeasure F.bar) ∧
      ∀ a, relFisher (F.ρ a) F.bar < ⊤ ∧ klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) < ⊤ := by
  exact Sec8.terms_finite hd hyp F hF

/-- Corollary 8.1, (8.1) ⟺ (8.2). -/
theorem agreement_iff {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    (∃ L : ℝ≥0∞, Tendsto (fun N => rAll V W N) atTop (𝓝 L) ∧
        Tendsto (fun N => rSym V W N) atTop (𝓝 L)) ↔
      ∀ F : Family d, F.Admissible → AgreementCriterion V W F := by
  exact Sec8.agreement_iff hd hyp (full_labeled_lsi_limit hd hyp)

/-- Corollary 8.1: smooth strictly positive families suffice. -/
theorem agreement_smooth_suffices {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    (∀ F : Family d, F.Admissible → AgreementCriterion V W F) ↔
      ∀ F : Family d, F.Admissible → (∀ a, IsSmoothT (F.ρ a) ∧ ∀ x, 0 < F.ρ a x) →
        AgreementCriterion V W F := by
  exact Sec8.agreement_smooth_suffices hd hyp (rMs_eq_smooth_inf hd hyp)

/-- Corollary 8.1, (8.3): a necessary condition when `r_* > 0`. -/
theorem agreement_necessary {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (hagree : ∃ L : ℝ≥0∞, Tendsto (fun N => rAll V W N) atTop (𝓝 L) ∧
        Tendsto (fun N => rSym V W N) atTop (𝓝 L)) :
    rStar V W ≤ rLS (μ : Measure (Torus d)) := by
  exact Sec8.agreement_necessary hd hyp hr μ hμ (full_labeled_lsi_limit hd hyp) hagree

end SharpLSI.FL
