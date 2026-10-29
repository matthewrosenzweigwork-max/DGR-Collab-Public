import FullLabeledLSI.Examples.E01g0_Tmat
import FullLabeledLSI.Examples.E01h0_Seq

/-!
# Lane D, Task B: trigonometric functions on the circle `Torus 1`

`cm n x = cos(2π n x)`, `sm n x = sin(2π n x)` as real and imaginary parts of `fourier n (x 0)`.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- `cos(2π n x)` on `Torus 1`. -/
noncomputable def cm (n : ℤ) (x : Torus 1) : ℝ := (fourier n (x 0)).re

/-- `sin(2π n x)` on `Torus 1`. -/
noncomputable def sm (n : ℤ) (x : Torus 1) : ℝ := (fourier n (x 0)).im

theorem cosMode_eq_cm (k : ℕ) (x : Torus 1) : cosMode k x = cm (k : ℤ) x := rfl

end SharpLSI.FL.Ex.LaneD
