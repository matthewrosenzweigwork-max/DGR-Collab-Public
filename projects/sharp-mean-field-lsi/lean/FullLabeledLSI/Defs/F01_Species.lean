import SharpSymmetricLSI.Defs.D07_rStar

/-!
# F1: prescribed groups of labels and the multi-species constant (1.10)–(1.13)

Manuscript of record: `manuscript/sharp_full_labeled_lsi_public_20261004T170742Z.tex`.

* `Family d`: a finite family `(q, θ, ρ)` of prescribed label groups; `Family.bar` is the average
  density `ρ̄ = ∑ₐ θₐ ρₐ` (1.10).
* `Family.Admissible`: `θₐ > 0`, `∑ₐ θₐ = 1`, each `ρₐ` a probability density with
  `√ρₐ ∈ H^1(m)` (the domain described after (1.13)). `q ≥ 1` follows from `∑ₐ θₐ = 1`.
* `msGap V W F = G_θ(ρ)` (1.11), `EReal`-valued like `gap`.
* `msDiss V W F = D_θ(ρ)` (1.12), `ℝ≥0∞`-valued like `dissipation`; each species term is
  `speciesDiss V W ρₐ ρ̄`, which is `⊤` unless `√ρₐ ∈ H^1(m)` and `V + W*ρ̄` has a weak gradient,
  exactly as in `dissipation` (D6).
* `rMs V W = r_ms` (1.13): the infimum of `D_θ/(2G_θ)` over admissible families with `G_θ > 0`,
  every finite `q`, in `ℝ≥0∞` (the same conventions as `rStar`).
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- A finite family of prescribed groups of labels: `q` groups, fractions `θ`, densities `ρ`
(manuscript, Section 1.2). -/
structure Family (d : ℕ) where
  /-- The number of groups. -/
  q : ℕ
  /-- The fractions `θₐ`. -/
  θ : Fin q → ℝ
  /-- The one-particle densities `ρₐ` with respect to Haar measure. -/
  ρ : Fin q → Torus d → ℝ

/-- The average density `ρ̄ = ∑ₐ θₐ ρₐ` (manuscript (1.10)). -/
noncomputable def Family.bar (F : Family d) (x : Torus d) : ℝ :=
  ∑ a, F.θ a * F.ρ a x

/-- An admissible finite family (manuscript, after (1.13)): positive fractions summing to one,
probability densities `ρₐ` with `√ρₐ ∈ H^1(m)`. -/
def Family.Admissible (F : Family d) : Prop :=
  (∀ a, 0 < F.θ a) ∧ ∑ a, F.θ a = 1 ∧
    ∀ a, (∀ x, 0 ≤ F.ρ a x) ∧ ∫ x, F.ρ a x ∂haar d = 1 ∧
      MemH1 (haar d) (fun x => Real.sqrt (F.ρ a x))

/-- The multi-species free-energy gap `G_θ(ρ)` (manuscript (1.11)). -/
noncomputable def msGap (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (F : Family d) : EReal :=
  ((∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) : ℝ≥0∞) : EReal) +
    ((potE V (densMeasure F.bar) +
        interE W (densMeasure F.bar) (densMeasure F.bar) / 2 : ℝ) : EReal) - Fstar V W

open Classical in
/-- One species term of (1.12): `∫ |2∇√ρₐ + √ρₐ ∇(V + W*ρ̄)|² dm`, `⊤` unless `√ρₐ ∈ H^1(m)`
and `V + W*ρ̄` has a weak gradient (the convention of `dissipation`). -/
noncomputable def speciesDiss (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρa ρbar : Torus d → ℝ) : ℝ≥0∞ :=
  if MemH1 (haar d) (fun x => Real.sqrt (ρa x)) ∧
      HasWeakGrad (fun x => V x + convDens W ρbar x) then
    ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρa y)) x k +
      Real.sqrt (ρa x) * weakGrad (fun y => V y + convDens W ρbar y) x k) ^ 2) ∂haar d
  else ⊤

/-- The multi-species dissipation `D_θ(ρ)` (manuscript (1.12)). -/
noncomputable def msDiss (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (F : Family d) :
    ℝ≥0∞ :=
  ∑ a, ENNReal.ofReal (F.θ a) * speciesDiss V W (F.ρ a) F.bar

/-- The admissible families of (1.13): admissible with positive gap. -/
def MsAdmissible (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (F : Family d) : Prop :=
  F.Admissible ∧ 0 < msGap V W F

/-- `r_ms` (manuscript (1.13)). -/
noncomputable def rMs (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : ℝ≥0∞ :=
  ⨅ F ∈ {F : Family d | MsAdmissible V W F},
    msDiss V W F / (2 * (msGap V W F).toENNReal)

/-- Sanity lemma for F1: a single species is the mean-field dissipation. -/
theorem speciesDiss_self (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) :
    speciesDiss V W ρ ρ = dissipation V W ρ := rfl

end SharpLSI.FL
