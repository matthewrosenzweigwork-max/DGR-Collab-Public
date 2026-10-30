import DGPS.Lipschitz.T01PositiveEquilibrium
import DGPS.Lipschitz.T01EquilibriumBridge
import DGPS.Lipschitz.T01Positivity
import DGPS.Structural.PositivityFromResidual

/-!
# T05: exact positive-rate criterion under direct Lipschitz data

Uniqueness is equality of induced probability measures for *all* zero-dissipation
absolute competitors, not uniqueness of square-root representatives and not uniqueness
only among stationary points with coercive Hessian. The reverse implication obtains
the minimizing property from existence of a Gibbs minimizer, rather than assuming it.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Structural

variable {d : ℕ}

/-- Three-way positivity/stationary uniqueness and coercivity criterion, for any
actual weak-drift provider. No semiconvexity or extra equilibrium hypothesis is used. -/
theorem positiveRate_iff_uniqueZeroDissipation_coerciveHessian_of_drift
    (hd : 0 < d) (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) :
    (0 < scalarRate A b ↔ 0 < speciesRate A b) ∧
    (0 < scalarRate A b ↔
      ∃ μ : AbsoluteDensity d,
        scalarDissipation A b μ = 0 ∧
        (∀ ρ : AbsoluteDensity d, scalarDissipation A b ρ = 0 →
          densityMeasure ρ = densityMeasure μ) ∧
        IsCoerciveDensityHessian A (densityMeasure μ)) := by
  refine ⟨⟨Lipschitz.speciesRate_pos_of_scalarRate_pos hd A hLip b,
    fun h => h.trans_le (speciesRate_le_scalarRate A b)⟩, ?_⟩
  constructor
  · intro hrate
    obtain ⟨ν, hν, huniq, hH⟩ :=
      Lipschitz.t01_unique_minimizer_and_coercive_hessian A hLip b hrate
    obtain ⟨-, -, ⟨μ, hμ⟩, hz⟩ := (gibbsMinimizer_exists A hLip b).2.2 ν hν
    refine ⟨μ, hz μ hμ, ?_, ?_⟩
    · intro ρ hρ
      rw [hμ]
      exact huniq (densityMeasure ρ)
        ((Lipschitz.zeroDissipation_iff_minimizer_of_positive_scalarRate
          A hLip b hrate ρ).mp hρ)
    · rw [hμ]
      exact hH
  · rintro ⟨μ, hμzero, huniq, hH⟩
    have hfixeduniq : ∀ ν : ProbabilityMeasure (Torus d),
        (ν : Measure (Torus d)) = (frozenGibbs A ν).measure →
        ν = densityMeasure μ := by
      intro ν hν
      obtain ⟨-, ρ, hρ, hz⟩ :=
        (zeroDissipation_iff_frozenFixedPoint A hLip b).2 ν hν
      rw [← hρ]
      exact huniq ρ hz
    obtain ⟨ν, hν⟩ := DGPS.freeEnergy_minimum_exists A
    have hνμ : ν = densityMeasure μ :=
      hfixeduniq ν (minimizer_eq_frozenGibbs A hν)
    have hmin : freeEnergy A (densityMeasure μ) = freeEnergyMinimum A := by
      rw [← hνμ]
      exact hν
    obtain ⟨C, -, -, hbound⟩ :=
      speciesRate_ge_frozenResidual_bound hd A hLip b hmin hfixeduniq hH
    obtain ⟨Kb, hKb, hK⟩ := DGPS.centeredKernel_bounded A (densityMeasure μ)
    obtain ⟨-, hpos, hle⟩ := hbound Kb hKb hK
    exact ((ENNReal.ofReal_pos.mpr hpos).trans_le hle).trans_le
      (speciesRate_le_scalarRate A b)

/-- **T05 canonical export.** Direct Lipschitz scalar and species rates are positive
exactly when there is a unique zero-dissipation probability density with coercive
centered density Hessian. The uniqueness quantifier covers every absolute competitor. -/
theorem positiveRate_iff_uniqueZeroDissipation_coerciveHessian
    (d : ℕ) (hd : 0 < d) (A : InteractionData d) (hLip : LipschitzData A) :
    let b := lipschitz_absoluteDrift A hLip
    (0 < scalarRate A b ↔ 0 < speciesRate A b) ∧
    (0 < scalarRate A b ↔
      ∃ μ : AbsoluteDensity d,
        scalarDissipation A b μ = 0 ∧
        (∀ ρ : AbsoluteDensity d, scalarDissipation A b ρ = 0 →
          densityMeasure ρ = densityMeasure μ) ∧
        ∃ c : ℝ, 0 < c ∧
          ∀ f : centeredL2 (densityMeasure μ),
            c * ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian A (densityMeasure μ) f)) :=
  positiveRate_iff_uniqueZeroDissipation_coerciveHessian_of_drift hd A hLip
    (lipschitz_absoluteDrift A hLip)

end DGPS.Structural
