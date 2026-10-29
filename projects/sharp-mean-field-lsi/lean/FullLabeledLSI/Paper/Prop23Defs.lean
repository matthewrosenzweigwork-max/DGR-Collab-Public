import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Defs.D13_Equilibrium
import SharpSymmetricLSI.Paper.GroundT8

/-!
# Proposition 2.3: shared definitions of the lane-2 work packages (WP-A, B, C, D, I)

* `QN μ N = μ^{⊗N}`, `psiG W μ N f = f · √(e^{-U_N}/K_N)` (the ground-state transform `Ψ_N`);
* `PropBoundedCore V W b`: the `N`-indexed core statement of Proposition 2.3 (WP-H), from which
  `BoundedComparison` follows by zero-padding (WP-I).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- `Q_N = μ^{⊗N}`. -/
noncomputable def QN (μ : Measure (Torus d)) (N : ℕ) : Measure (Config N d) :=
  Measure.pi fun _ : Fin N => μ

/-- The ground-state transform `Ψ = f · √(e^{-U_N}/K_N)` (the `let Ψ` of SYM `ground_state_transform_of`). -/
noncomputable def psiG (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ)
    (f : Config N d → ℝ) : Config N d → ℝ := fun X =>
  f X * Real.sqrt (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N)

/-- The `N`-indexed core of Proposition 2.3. -/
def PropBoundedCore (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (b : ℝ≥0∞) : Prop :=
  ∀ f : (N : ℕ) → Config N d → ℝ, (∀ N, MemH1C (gibbs V W N) (f N)) →
    (∃ B : NNReal, ∀ N, (∀ᵐ X ∂gibbs V W N, |f N X| ≤ B) ∧ energy V W N (f N) ≤ B) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      b / 2 * ent (gibbs V W N) (fun X => f N X ^ 2) ≤ energy V W N (f N) + ENNReal.ofReal ε

end SharpLSI.FL
