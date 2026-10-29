import SharpSymmetricLSI.Defs.D05_FreeEnergy

/-!
# D6: free-energy dissipation (1.6)

For a density `ρ` with `√ρ ∈ H^1(m)`:
`D(ρ) = ∫ |2∇√ρ + √ρ ∇(V + W*ρ)|² dm`, `(W*ρ)(x) = ∫ W(x,y) dρ(y)`.
`D(ρ) = ⊤` off this set. `∇(V + W*ρ)` is the weak gradient of the (Lipschitz, under (1.2))
function `V + W*ρ`; its existence is required in the definition (it holds under (1.2)).
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- The measure `ρ m` with density `ρ` w.r.t. Haar measure. -/
noncomputable def densMeasure (ρ : Torus d → ℝ) : Measure (Torus d) :=
  (haar d).withDensity (fun x => ENNReal.ofReal (ρ x))

/-- `(W*ρ)(x) = ∫ W(x,y) dρ(y)` for a density `ρ` (manuscript (1.6)). -/
noncomputable def convDens (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ y, W x y * ρ y ∂haar d

/-- `(W*ρ)(x) = ∫ W(x,y) dρ(y)` for a measure `ρ`. -/
noncomputable def convMeas (W : Torus d → Torus d → ℝ) (ρ : Measure (Torus d)) (x : Torus d) :
    ℝ :=
  ∫ y, W x y ∂ρ

open Classical in
/-- The dissipation `D(ρ)` (manuscript (1.6)), `⊤` unless `√ρ ∈ H^1(m)`. -/
noncomputable def dissipation (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρ : Torus d → ℝ) : ℝ≥0∞ :=
  if MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
      HasWeakGrad (fun x => V x + convDens W ρ x) then
    ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x k +
      Real.sqrt (ρ x) * weakGrad (fun y => V y + convDens W ρ y) x k) ^ 2) ∂haar d
  else ⊤

end SharpLSI
