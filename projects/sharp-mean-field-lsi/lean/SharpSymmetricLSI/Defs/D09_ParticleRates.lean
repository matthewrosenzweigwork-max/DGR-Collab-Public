import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Paper.EntFinite

/-!
# D9–D11 (and the generic part of D20): particle Dirichlet form and optimal constants

* `energy V W N f = ℰ_N(f) = ∫ ∑ᵢ |∇ᵢ f|² dP_N` (manuscript (1.8)), full product gradient,
  no factor `1/N`.
* `rSym N = r_N^sym` (1.8): infimum of `2ℰ_N(f)/Ent_{P_N}(f²)` over real symmetric
  `f ∈ H^1(P_N)` with `Ent_{P_N}(f²) > 0`.
* `rAll N = r_N^all` (3.2): the same without symmetry.
* `lamSym N = λ_N^sym` (2.8): infimum of `ℰ_N(f)/Var_{P_N}(f)` over symmetric `f ∈ H^1(P_N)`
  with `Var > 0`.
* `lamAll N = λ_N^all` ((3.24) for the cosine model): the same without symmetry.

All are `ℝ≥0∞`-valued. Symmetry is pointwise invariance of the chosen representative; since all
quantities depend only on the a.e. class and an a.e.-symmetric function has a symmetric
representative, this gives the same infima. REVIEW.

The ratios `2ℰ/Ent` are taken in `ℝ≥0∞`. Under (1.2), `Ent_{P_N}(f²) < ⊤` for every
`f ∈ H^1(P_N)`, `N ≥ 1` (`ent_sq_lt_top`, the fixed-`N` Sobolev bound), so the `x/⊤ = 0`
convention of `ℝ≥0∞` never enters the infima.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- `ℰ_N(f) = ∫ ∑ᵢ |∇ᵢ f|² dP_N` (manuscript (1.8)). -/
noncomputable def energy (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ)
    (f : Config N d → ℝ) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (gradSqC f X) ∂gibbs V W N

/-- `r_N^sym` (manuscript (1.8)). -/
noncomputable def rSym (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ f ∈ {f : Config N d → ℝ | MemH1C (gibbs V W N) f ∧ IsSymmetric f ∧
      0 < ent (gibbs V W N) (fun X => f X ^ 2)},
    2 * energy V W N f / ent (gibbs V W N) (fun X => f X ^ 2)

/-- `r_N^all` (manuscript (3.2)): `r_N^sym` without the symmetry condition. -/
noncomputable def rAll (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ f ∈ {f : Config N d → ℝ | MemH1C (gibbs V W N) f ∧
      0 < ent (gibbs V W N) (fun X => f X ^ 2)},
    2 * energy V W N f / ent (gibbs V W N) (fun X => f X ^ 2)

/-- `λ_N^sym` (manuscript (2.8)). -/
noncomputable def lamSym (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ f ∈ {f : Config N d → ℝ | MemH1C (gibbs V W N) f ∧ IsSymmetric f ∧
      0 < var (gibbs V W N) f},
    energy V W N f / var (gibbs V W N) f

/-- `λ_N^all`: `λ_N^sym` without the symmetry condition (manuscript (3.24) for the cosine
model). -/
noncomputable def lamAll (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ f ∈ {f : Config N d → ℝ | MemH1C (gibbs V W N) f ∧ 0 < var (gibbs V W N) f},
    energy V W N f / var (gibbs V W N) f

/-- Sanity lemma for D9: under (1.2), `Ent_{P_N}(f²) < ⊤` for `f ∈ H^1(P_N)`, `N ≥ 1`. -/
theorem ent_sq_lt_top {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : ent (gibbs V W N) (fun X => f X ^ 2) < ⊤ := by
  exact ent_sq_lt_top_aux hyp hf

end SharpLSI
