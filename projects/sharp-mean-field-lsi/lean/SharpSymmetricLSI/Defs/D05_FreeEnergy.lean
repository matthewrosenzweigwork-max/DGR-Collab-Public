import SharpSymmetricLSI.Infra.Entropy
import SharpSymmetricLSI.Defs.D02_Hypotheses
import SharpSymmetricLSI.Paper.FreeEnergyMin

/-!
# D5: mean-field free energy (1.5)

`F(ρ) = H(ρ|m) + ρ(V) + ½ W(ρ,ρ)`, `F_* = min F`, `G(ρ) = F(ρ) - F_*`, with
`ρ(V) = ∫ V dρ` and `W(ρ,η) = ∬ W(x,y) dρ(x) dη(y)`.

`F` is `EReal`-valued (`⊤` off finite entropy). `F_*` is defined as the infimum over
probability measures; that it is attained (manuscript: compactness and lower semicontinuity)
is the lemma `exists_minimizer`.
-/

open MeasureTheory InformationTheory

namespace SharpLSI

variable {d : ℕ}

/-- `ρ(V) = ∫ V dρ`. -/
noncomputable def potE (V : Torus d → ℝ) (ρ : Measure (Torus d)) : ℝ := ∫ x, V x ∂ρ

/-- `W(ρ,η) = ∬ W(x,y) dρ(x) dη(y)`. -/
noncomputable def interE (W : Torus d → Torus d → ℝ) (ρ η : Measure (Torus d)) : ℝ :=
  ∫ y, ∫ x, W x y ∂ρ ∂η

/-- The mean-field free energy `F(ρ) = H(ρ|m) + ρ(V) + ½ W(ρ,ρ)` (manuscript (1.5)). -/
noncomputable def freeEnergy (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) : EReal :=
  ((klDiv ρ (haar d) : ENNReal) : EReal) + ((potE V ρ + interE W ρ ρ / 2 : ℝ) : EReal)

/-- `F_* = inf_{𝒫(𝕋^d)} F` (a minimum by `exists_minimizer`). -/
noncomputable def Fstar (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) : EReal :=
  ⨅ ρ : ProbabilityMeasure (Torus d), freeEnergy V W ρ

/-- The free-energy gap `G(ρ) = F(ρ) - F_*` (manuscript (1.5)). -/
noncomputable def gap (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Measure (Torus d)) : EReal :=
  freeEnergy V W ρ - Fstar V W

/-- `μ` minimizes `F` over `𝒫(𝕋^d)`. -/
def IsMinimizer (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (μ : ProbabilityMeasure (Torus d)) : Prop :=
  freeEnergy V W μ = Fstar V W

/-- Sanity lemma for D5: under (1.2), `F` attains its infimum (manuscript, after (1.5):
compactness of `𝒫(𝕋^d)` and lower semicontinuity), and `F_*` is finite. -/
theorem exists_minimizer {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) :
    (∃ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ) ∧ Fstar V W ≠ ⊤ ∧
      Fstar V W ≠ ⊥ :=
  exists_minimizer_aux hyp

end SharpLSI
