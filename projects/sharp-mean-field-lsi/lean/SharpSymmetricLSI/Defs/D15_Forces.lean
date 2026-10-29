import SharpSymmetricLSI.Defs.D14_Conditional
import SharpSymmetricLSI.Statements.R06_Upper_Bound

/-!
# D15: forces (5.11), (5.16)

* `bForce W μ = b`, `b(x,y) = ∇₁K(x,y)` (a.e.): the weak gradient of the Lipschitz kernel `K` on
  `(𝕋^d)²` in the first variable (`grad1W`, via `Config 2 d`).
* `bDiag W μ = b_Δ`, `b_Δ(x) = ½ ∇[K(x,x)]`: the weak gradient of the Lipschitz function
  `x ↦ K(x,x)/2`, not a restriction of `∇₁K` to the diagonal.
* `condForce ν μ j = B_j`, `B_j(x) = ∫ b(x,y) dρ_j(y)` (5.16), a function of the past.
-/

open MeasureTheory

namespace SharpLSI

variable {d N : ℕ}

/-- `b(x,y) = ∇₁K(x,y)` (manuscript (5.11)). -/
noncomputable def bForce (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (x y : Torus d)
    (k : Fin d) : ℝ :=
  grad1W (centeredKernel W μ) x y k

/-- `b_Δ(x) = ½ ∇[K(x,x)]` (manuscript (5.11)). -/
noncomputable def bDiag (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (x : Torus d)
    (k : Fin d) : ℝ :=
  weakGrad (fun z => centeredKernel W μ z z / 2) x k

/-- `B_j(x) = ∫ b(x,y) dρ_j(y)` (manuscript (5.16)), for a given past. -/
noncomputable def condForce (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (ν : Measure (Config N d)) [IsFiniteMeasure ν] (j : ℕ) (hj : j < N)
    (p : Fin j → Torus d) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ y, bForce W μ x y k ∂(condNext ν j hj p)

end SharpLSI
