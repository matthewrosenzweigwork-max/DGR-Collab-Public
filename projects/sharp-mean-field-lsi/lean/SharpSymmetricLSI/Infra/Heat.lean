import SharpSymmetricLSI.Infra.Classical

/-!
# Heat semigroup on `𝕋^ι`, Lipschitz norms, `W^{1,∞}`-type distances

* `heatKernel t y = (4πt)^{-n/2} exp(-|y|²/(4t))` on `ℝ^ι` (`n = |ι|`), and
  `heatT t f (x) = ∫_{ℝ^ι} f(x - π y) heatKernel t y dy`, the periodic heat semigroup `e^{tΔ}`.
* `divHeatT t F (x) = ∑_k ∫ ∂_k heatKernel t (y) F_k(x - π y) dy`, i.e. `∇·(e^{tΔ}F)`.
* `w1infDist f g = ‖f - g‖_{L^∞(m)} + ‖|∇(f-g)|‖_{L^∞(m)}` (weak gradient).
-/

open MeasureTheory
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian heat kernel of `e^{tΔ}` on `ℝ^ι`. -/
noncomputable def heatKernel (t : ℝ) (y : ι → ℝ) : ℝ :=
  (4 * π * t) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(∑ k, y k ^ 2) / (4 * t))

/-- The periodic heat semigroup `e^{tΔ} f` on `𝕋^ι`. -/
noncomputable def heatT (t : ℝ) (f : UnitAddTorus ι → ℝ) (x : UnitAddTorus ι) : ℝ :=
  ∫ y : ι → ℝ, f (x - liftT y) * heatKernel t y

/-- `∇·(e^{tΔ} F)` for a vector field `F` on `𝕋^ι`. -/
noncomputable def divHeatT (t : ℝ) (F : UnitAddTorus ι → ι → ℝ) (x : UnitAddTorus ι) : ℝ :=
  ∑ k, ∫ y : ι → ℝ, fderiv ℝ (heatKernel t) y (Pi.single k 1) * F (x - liftT y) k

/-- The `W^{1,∞}` distance `‖f-g‖_∞ + ‖∇(f-g)‖_∞` (w.r.t. Haar measure). -/
noncomputable def w1infDist (f g : UnitAddTorus ι → ℝ) : ℝ≥0∞ :=
  eLpNorm (fun x => f x - g x) ⊤ volume +
    eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad (fun y => f y - g y) x))) ⊤ volume

end SharpLSI
