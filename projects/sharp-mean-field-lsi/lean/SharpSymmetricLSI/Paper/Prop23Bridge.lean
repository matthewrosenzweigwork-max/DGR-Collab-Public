import SharpSymmetricLSI.Paper.Prop23Defs
import SharpSymmetricLSI.Statements.R04_Prop_2_3

/-!
# Proposition 2.3: `CompactnessProperty' = CompactnessProperty`
-/

open MeasureTheory

namespace SharpLSI

variable {d : ℕ}

theorem compactnessProperty'_eq (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (γ : Measure (ℕ → ℝ)) (EInf : ((ℕ → ℝ) → ℝ) → ENNReal) :
    CompactnessProperty' V W γ EInf = CompactnessProperty V W γ EInf := rfl

end SharpLSI
