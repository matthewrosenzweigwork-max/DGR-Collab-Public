import DGPS.Variational.ScoreDecomposition

/-!
# Species entropy decomposition including zeros (DEF014)

For every finite admissible family `F`, `G_θ = G(ρ̄) + ∑ θ_s H(ρ_s m | ρ̄ m)` in `ℝ≥0∞`; each
species measure is absolutely continuous with respect to `ρ̄ m` and the relative entropies are
finite.  Derived from LIP003 (`square_root_mixture_and_score_decompositions`), whose hypotheses
(an `InteractionData` and an `AbsoluteDrift`) are available for the same data as DEF014 once an
absolute drift is chosen; here the drift-free projections already proved in
`DGPS.SpeciesFamily` are used, which are exactly the LIP003 parts.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS

variable {d : ℕ}

/-- DEF014: absolute continuity of each species with respect to the barycenter. -/
theorem def014_species_absolutelyContinuous (F : SpeciesFamily d) (s : Fin F.count) :
    (densityMeasure (F.density s) : Measure (Torus d)) ≪
      (densityMeasure (barycenter F) : Measure (Torus d)) :=
  (F.relativeEntropy_species s).1

/-- DEF014: the species-to-barycenter relative entropies are finite. -/
theorem def014_relativeEntropy_ne_top (F : SpeciesFamily d) (s : Fin F.count) :
    relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      (densityMeasure (barycenter F) : Measure (Torus d)) ≠ ⊤ :=
  (F.relativeEntropy_species s).2.1

/-- DEF014 (species entropy decomposition including zeros), in `ℝ≥0∞`. -/
theorem speciesGap_decomposition (A : InteractionData d) (F : SpeciesFamily d) :
    (speciesGap A F : ℝ≥0∞) =
      (scalarGap A (barycenter F) : ℝ≥0∞) +
        ∑ s, ENNReal.ofReal (F.weight s) *
          relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
            (densityMeasure (barycenter F) : Measure (Torus d)) := by
  have hR := F.speciesGap_decomposition A
  have hH : ∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      (densityMeasure (barycenter F) : Measure (Torus d)) =
      ENNReal.ofReal (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal := fun s =>
    (ENNReal.ofReal_toReal (def014_relativeEntropy_ne_top F s)).symm
  have hnn : ∀ s, 0 ≤ F.weight s * (relativeEntropy
      (densityMeasure (F.density s) : Measure (Torus d))
      (densityMeasure (barycenter F) : Measure (Torus d))).toReal :=
    fun s => mul_nonneg (F.weight_nonneg s) ENNReal.toReal_nonneg
  have hsum : ∑ s, ENNReal.ofReal (F.weight s) *
        relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
          (densityMeasure (barycenter F) : Measure (Torus d)) =
      ENNReal.ofReal (∑ s, F.weight s * (relativeEntropy
        (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ => hnn s]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hH s, ← ENNReal.ofReal_mul (F.weight_nonneg s), ENNReal.ofReal_toReal
      (def014_relativeEntropy_ne_top F s)]
  have hS := Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) => hnn s
  rw [hsum]
  calc (speciesGap A F : ℝ≥0∞) = ENNReal.ofReal (speciesGap A F : ℝ) :=
        (ENNReal.ofReal_coe_nnreal).symm
    _ = ENNReal.ofReal ((scalarGap A (barycenter F) : ℝ) + _) := by rw [hR]
    _ = _ := by
        rw [ENNReal.ofReal_add (NNReal.coe_nonneg _) hS, ENNReal.ofReal_coe_nnreal]

/-- DEF014: in particular the family gap is nonnegative (real form). -/
theorem def014_speciesGap_nonneg (A : InteractionData d) (F : SpeciesFamily d) :
    0 ≤ (speciesGap A F : ℝ) := (speciesGap A F).2

end DGPS
