import SharpSymmetricLSI.Infra.Torus
import SharpSymmetricLSI.Paper.LipDual

/-!
# D19: the dual Lipschitz distance (A.2)

`d_Lip(ν,η) = sup { |∫ φ d(ν-η)| : Lip(φ) ≤ 1, φ(x_0) = 0 }` with base point `x_0 = 0`, on
`𝒫(𝕋^d)`, with `Lip` for the flat (Euclidean) distance `flatDist` of the torus, as in the
manuscript (review of block 3).
-/

open MeasureTheory

namespace SharpLSI

variable {d : ℕ}

/-- `d_Lip(ν, η)` (manuscript (A.2)) for finite measures. -/
noncomputable def dLipM (ν η : Measure (Torus d)) : ℝ :=
  sSup {s | ∃ φ : Torus d → ℝ, FlatLipschitzWith 1 φ ∧ φ 0 = 0 ∧
    s = |∫ x, φ x ∂ν - ∫ x, φ x ∂η|}

/-- `d_Lip(ν, η)` (manuscript (A.2)) on `𝒫(𝕋^d)`. -/
noncomputable def dLip (ν η : ProbabilityMeasure (Torus d)) : ℝ :=
  dLipM (ν : Measure (Torus d)) (η : Measure (Torus d))

/-- (A.2), text after it: `d_Lip` metrizes weak convergence on `𝒫(𝕋^d)`. -/
theorem dLip_metrizes (ν : ℕ → ProbabilityMeasure (Torus d)) (η : ProbabilityMeasure (Torus d)) :
    Filter.Tendsto ν Filter.atTop (nhds η) ↔
      Filter.Tendsto (fun n => dLip (ν n) η) Filter.atTop (nhds 0) :=
  dLipAux_metrizes ν η

end SharpLSI
