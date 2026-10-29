import LeanResearch.PeriodicAttractiveLogGas.AmbientClosure
import LeanResearch.PeriodicAttractiveLogGas.GreenEquation
import LeanResearch.PeriodicAttractiveLogGas.KernelRepresentatives

/-! The exact quantifier order and full ambient-domain inequality of thm:main.
`theorem11Statement` is a proposition to be proved, not a theorem or an axiom.
Its positive-coupling normalization is proved in GreenNormalization;
the full logarithmic Sobolev proof remains open.

The totalized Gibbs construction is always a finite subprobability measure.
This only permits forming its L2 graph without an unproved finiteness premise.
In particular, an infinite partition integral totalizes to the zero measure.
Such a degenerate case does NOT qualify as the manuscript's probability law:
the separate `greenNormalizationStatement` is a required acceptance obligation,
now discharged by `green_normalization` in GreenNormalization.
The kernel is the constructed L2 Green representative. Its regular representative
is constructed in GreenRepresentative and preserves the same law, as proved in
GreenEnsemble using `gibbsMeasure_congr_ae_kernel`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PeriodicAttractiveLogGas

theorem gibbsMeasure_univ_le_one (g : Torus → ℝ) (N : ℕ) (β : ℝ) :
    gibbsMeasure g N β Set.univ ≤ 1 := by
  have heq : gibbsMeasure g N β Set.univ =
      (partitionFunction g N β)⁻¹ * partitionFunction g N β := by
    unfold gibbsMeasure
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  rw [heq]
  by_cases hz : partitionFunction g N β = 0
  · simp [hz]
  by_cases ht : partitionFunction g N β = ⊤
  · simp [ht]
  exact le_of_eq (ENNReal.inv_mul_cancel hz ht)

instance isFiniteMeasure_gibbsMeasure (g : Torus → ℝ) (N : ℕ) (β : ℝ) :
    IsFiniteMeasure (gibbsMeasure g N β) :=
  ⟨lt_of_le_of_lt (gibbsMeasure_univ_le_one g N β) ENNReal.one_lt_top⟩

def greenNormalizationStatement : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (β : ℝ), 0 ≤ β → β < 4 →
    partitionFunction greenRealRepresentative N β ≠ ⊤

abbrev GreenAmbientFormDomain (N : ℕ) (β : ℝ) :=
  AmbientFormDomain N (gibbsMeasure greenRealRepresentative N β)

/-- Exact full-domain target, with a finite real constant chosen before N and beta.
No symmetry, centering, extra regularity, or collision-support restriction on f. -/
def theorem11Statement : Prop :=
  ∀ (β₀ : ℝ), 0 ≤ β₀ → β₀ < 4 → ∃ C : ℝ,
    ∀ (N : ℕ), 2 ≤ N → ∀ (β : ℝ), 0 ≤ β → β ≤ β₀ →
      ∀ f : GreenAmbientFormDomain N β,
        entropy (gibbsMeasure greenRealRepresentative N β)
            (fun x ↦ (ambientValue f x) ^ 2) ≤
          ((2 * C * ambientEnergy f : ℝ) : EReal)

end PeriodicAttractiveLogGas
