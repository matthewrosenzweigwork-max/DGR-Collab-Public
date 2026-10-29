import DGPS.Structural.FrozenGibbsIdentities
import DGPS.Structural.FrozenGibbsInformation
import DGPS.Variational.ZeroDissipation

/-!
# Zero dissipation means a frozen Gibbs fixed point (STR003)

Under the STR001 assumptions (Lipschitz interaction data `A`, a weak-drift provider `b`), for an
absolute competitor `ρ`, `D(ρ) = 0` iff `ρ m = P(ρ m)` with `P = frozenGibbs A`; conversely every
probability fixed point `ν = P ν` has a positive Lipschitz density and is the measure `ρ m` of an
absolute-admissible `ρ` with `D(ρ) = 0`.

Route note: the statement is that of DEF033 (`DGPS.zeroDissipation_iff_frozenFixedPoint`), whose
proof already runs through the relative-square-root gradient (the pointwise form of the STR002
information identity) and the connected-torus zero-gradient lemma.  This module re-exports it in
the `DGPS.Structural` namespace, and records the STR002 reading `D(ρ) = I(ρ m | P(ρ m))`.
-/

namespace DGPS.Structural

variable {d : ℕ}

/-- **STR003.** Zero dissipation holds exactly at frozen Gibbs fixed points, and every
probability fixed point is a positive-Lipschitz absolute competitor with zero dissipation. -/
theorem zeroDissipation_iff_frozenFixedPoint (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) :
    (∀ ρ : AbsoluteDensity d, scalarDissipation A b ρ = 0 ↔
      (densityMeasure ρ : MeasureTheory.Measure (Torus d)) =
        (frozenGibbs A (densityMeasure ρ)).measure) ∧
    (∀ ν : MeasureTheory.ProbabilityMeasure (Torus d),
      (ν : MeasureTheory.Measure (Torus d)) = (frozenGibbs A ν).measure →
      (frozenGibbs A ν).hasPositiveLipschitzDensity ∧
        ∃ ρ : AbsoluteDensity d, densityMeasure ρ = ν ∧ scalarDissipation A b ρ = 0) :=
  DGPS.zeroDissipation_iff_frozenFixedPoint A hLip b

end DGPS.Structural
