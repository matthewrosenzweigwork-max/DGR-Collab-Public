import SharpSymmetricLSI.Paper.Prop23Bridge
import SharpSymmetricLSI.Paper.Prop23Assembly2
import SharpSymmetricLSI.Paper.R7Violators
import SharpSymmetricLSI.Paper.R37Rescaling
import SharpSymmetricLSI.Statements.R01_Theorem_1_1
import SharpSymmetricLSI.Statements.R03_Prop_2_2
import SharpSymmetricLSI.Statements.R04_Prop_2_3
import SharpSymmetricLSI.Statements.R31_Force_Approximation
import SharpSymmetricLSI.Statements.R37_Remark_8_1

/-!
# Named `rfl` bridges for the definitional copies

Several Paper files carry verbatim copies of frozen definitions so that they need not import the
statement files (import cycles). Each copy is literally the frozen definition; this file records
that as an explicit `rfl` equality. It is a leaf file (imported only by the root).
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem gaussianInputProperties'_eq (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (γ : Measure (ℕ → ℝ)) (EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞) (lG : ℝ≥0∞) :
    GaussianInputProperties' V W γ EInf lG = GaussianInputProperties V W γ EInf lG := rfl

theorem compactnessConclusion'_eq (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :
    CompactnessConclusion' V W = CompactnessConclusion V W := rfl

theorem finiteNConclusion'_eq (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :
    FiniteNConclusion' V W = FiniteNConclusion V W := rfl

theorem defectiveConclusion'_eq (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :
    DefectiveConclusion' V W = DefectiveConclusion V W := rfl

theorem ukernelF_eq (K : Torus d → Torus d → ℝ) (N : ℕ) : UkernelF K N = Ukernel K N := rfl

theorem physFreeEnergy'_eq (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :
    physFreeEnergy' β V W = physFreeEnergy β V W := rfl

theorem physGap'_eq (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :
    physGap' β V W = physGap β V W := rfl

theorem physDiss'_eq (β : ℝ) (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) :
    physDiss' β V W = physDiss β V W := rfl

end SharpLSI
