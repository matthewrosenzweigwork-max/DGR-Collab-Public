import FullLabeledLSI.Defs.F01_Species
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Defs.D18_GaussianForm

/-!
# F2: one-particle constants and the comparison rate `b` (1.18), (1.21), (4.19)

* `rLS μ = r_LS(μ)`: the ordinary one-particle logarithmic Sobolev constant of a probability `μ` on
  `𝕋^d`, in the rate normalization of `r_N^all`: the infimum of `2∫|∇f|² dμ / Ent_μ(f²)` over real
  `f ∈ H^1(μ)` with `Ent_μ(f²) > 0` (manuscript (1.18), (1.21) and Section 3.3). For `N = 1` and `W = 0`
  this is the same infimum as `rAll`.
* `poincareConst ρ`: the ordinary Poincaré constant, the infimum of `∫|∇h|² dρ / Var_ρ(h)` over
  `h ∈ H^1(ρ)` with `Var_ρ(h) > 0` (Proposition 8.2; same normalization as `lamAll`).
* `bRate μ lam C = b = min{r_LS(μ), λ_G}` (manuscript (1.21)), where `λ_G = lamG (lamShift lam) C`
  is the Gaussian rate of the symmetric project (D18, manuscript (4.19)) for a reference
  eigenbasis `(e, lam)` of `μ` (D16) and `C = (I+T)^{-1}`.
All three are `ℝ≥0∞`-valued with the conventions of `rAll` and `lamAll`. They accept any measure
and any `lam`, `C`, but carry the manuscript's meaning only for a probability `μ` with a density
bounded above and below (`MemH1 μ` is the weighted `H^1(μ)` only then), `(e, lam)` a reference
eigenbasis of `μ` and `C = (I+T)^{-1}`; every statement uses them only in that situation.
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- `r_LS(μ)`, the one-particle logarithmic Sobolev constant (rate normalization). -/
noncomputable def rLS (μ : Measure (Torus d)) : ℝ≥0∞ :=
  ⨅ f ∈ {f : Torus d → ℝ | MemH1 μ f ∧ 0 < ent μ (fun x => f x ^ 2)},
    2 * dirichlet μ f / ent μ (fun x => f x ^ 2)

/-- The ordinary Poincaré constant of a probability `ρ` on `𝕋^d`. -/
noncomputable def poincareConst (ρ : Measure (Torus d)) : ℝ≥0∞ :=
  ⨅ h ∈ {h : Torus d → ℝ | MemH1 ρ h ∧ 0 < var ρ h}, dirichlet ρ h / var ρ h

/-- `b = min{r_LS(μ), λ_G}` (manuscript (1.21)) for a reference eigenbasis with eigenvalues `lam`
and a covariance `C = (I+T)^{-1}`. -/
noncomputable def bRate (μ : Measure (Torus d)) (lam : ℕ → ℝ) (C : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  min (rLS μ) (lamG (lamShift lam) C)

end SharpLSI.FL
