import FullLabeledLSI.Defs.F03_RelFisher
import FullLabeledLSI.Paper.AdmissibleFinite
import FullLabeledLSI.Paper.Sec3Fisher

/-!
# F7: sanity lemmas for F1 (one group recovers the mean-field quantities)

A family with a single group (`q = 1`, `θ = 1`, `ρ₀ = ρ`) has `ρ̄ = ρ`, multi-species gap equal to
the mean-field gap `G(ρ)` (1.5), multi-species dissipation equal to `D(ρ)` (1.6), and it is
admissible for (1.13) exactly when `ρ` is admissible for (1.7). Under (1.2) and `d ≥ 1`, the
admissible set of (1.13) is therefore nonempty.

Finiteness (manuscript, after (1.13)): every admissible family has finite gap and dissipation, so
the quotient in `rMs` never meets the junk value `x / ⊤ = 0`.

`relFisher` against a density bounded above and below by positive constants is the Fisher
information `fisherInfo` (1.4) of the repo.

These are sanity lemmas for the encoding, not statements of the manuscript.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The family with one group of fraction one and density `ρ`. -/
def Family.single (ρ : Torus d → ℝ) : Family d := ⟨1, fun _ => 1, fun _ => ρ⟩

private theorem single_sum {M : Type*} [AddCommMonoid M] (ρ : Torus d → ℝ)
    (f : Fin (Family.single ρ).q → M) : ∑ a, f a = f ⟨0, Nat.one_pos⟩ :=
  Fin.sum_univ_one f

private theorem single_forall (ρ : Torus d → ℝ) (P : Fin (Family.single ρ).q → Prop) :
    (∀ a, P a) ↔ P ⟨0, Nat.one_pos⟩ :=
  Fin.forall_fin_one

theorem Family.single_bar (ρ : Torus d → ℝ) : (Family.single ρ).bar = ρ := by
  funext x
  rw [Family.bar, single_sum ρ]
  simp [Family.single]

theorem msGap_single (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) :
    msGap V W (Family.single ρ) = gap V W (densMeasure ρ) := by
  have hb : (Family.single ρ).bar = ρ := Family.single_bar ρ
  simp only [msGap, gap, freeEnergy, hb, single_sum ρ]
  simp [Family.single]

theorem msDiss_single (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) :
    msDiss V W (Family.single ρ) = dissipation V W ρ := by
  have hb : (Family.single ρ).bar = ρ := Family.single_bar ρ
  simp only [msDiss, hb, single_sum ρ]
  simp [Family.single, speciesDiss_self]

theorem msAdmissible_single_iff (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Torus d → ℝ) : MsAdmissible V W (Family.single ρ) ↔ Admissible V W ρ := by
  unfold MsAdmissible Family.Admissible Admissible
  rw [msGap_single]
  constructor
  · rintro ⟨⟨_, _, h⟩, hg⟩
    obtain ⟨h1, h2, h3⟩ := (single_forall ρ _).1 h
    exact ⟨h1, h2, h3, hg⟩
  · rintro ⟨h1, h2, h3, hg⟩
    refine ⟨⟨fun _ => one_pos, ?_, (single_forall ρ _).2 ⟨h1, h2, h3⟩⟩, hg⟩
    rw [single_sum ρ]
    rfl

/-- Under (1.2) and `d ≥ 1` the admissible set of (1.13) is nonempty. -/
theorem msAdmissible_nonempty {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) : ∃ F : Family d, MsAdmissible V W F := by
  obtain ⟨ρ, hρ⟩ := SharpLSI.admissible_nonempty hd hyp
  exact ⟨Family.single ρ, (msAdmissible_single_iff V W ρ).2 hρ⟩

/-- Admissible families have finite gap and dissipation (manuscript, after (1.13)). -/
theorem msGap_msDiss_lt_top {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {F : Family d} (hF : F.Admissible) :
    msGap V W F < ⊤ ∧ ⊥ < msGap V W F ∧ msDiss V W F < ⊤ := by
  have hg := msGap_bounds_of_admissible hyp hF
  exact ⟨hg.1, hg.2, msDiss_lt_top_of_admissible hyp hF⟩

/-- `relFisher` agrees with the repo's `fisherInfo` (1.4) when `ρb` is bounded above and below. -/
theorem relFisher_eq_fisherInfo {ρa ρb : Torus d → ℝ} (ha0 : ∀ x, 0 ≤ ρa x)
    (ha1 : ∫ x, ρa x ∂haar d = 1) (hb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ ρb x ∧ ρb x ≤ C)
    (hb1 : ∫ x, ρb x ∂haar d = 1) (ha : MemH1 (haar d) fun x => Real.sqrt (ρa x))
    (hb' : MemH1 (haar d) fun x => Real.sqrt (ρb x)) :
    relFisher ρa ρb = fisherInfo (densMeasure ρa) (densMeasure ρb) := by
  exact relFisher_eq_fisherInfo_aux ha0 ha1 hb hb1 ha hb'

end SharpLSI.FL
