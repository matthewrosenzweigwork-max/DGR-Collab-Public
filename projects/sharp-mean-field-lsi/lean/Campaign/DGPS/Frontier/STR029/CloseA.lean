import DGPS.Frontier.STR029.T32

/-!
# STR029.CLOSE-A: exactly three ordinary LSI optimizers and all zero-deficit roots

## Provides

`DGPS.Examples.ThreeSpeciesCircle.threefold_ordinaryLSI_exact_three_roots`:
for every sufficiently small positive field, exactly three pairwise distinct
positive-entropy absolute probability densities optimize the ordinary LSI quotient;
the zero-deficit measures at the canonical ordinary LSI rate are precisely their
three probability measures and the reference probability.

## R5 notes

The frozen specification is informal. This closing statement retains every
optimizer and zero-set clause of STR029.26 and STR029.32, on the same density
witnesses. The rate is `DGPS.ordinaryLSRate (ordinaryReference h)`; its exact
identification with the absolute-domain variational problem is proved in
`ordinaryLSRate_eq_abs_inf_STR02932`. The reference measure is
`threefoldReference h = (ordinaryReference h).measure`, definitionally.
Physical Fisher information is used throughout, retaining the angular-to-physical
normalization from STR029.01. The rate and density expansions belong to CLOSE-B.

Equality of densities is Haar-almost-everywhere equality, as required by STR029.01;
`densityMeasure_eq_iff_STR02901` identifies it with equality of induced probability
measures. The reference is distinct from each positive-entropy branch. Consequently
the displayed union consists of exactly four distinct zero-deficit measures.
The zero-set equivalence quantifies over every measure, with finiteness enforced
by the exact predicate `ZeroDeficit_STR02901` before real-valued subtraction.
-/

open MeasureTheory
open scoped ENNReal
open DGPS DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

theorem threefold_ordinaryLSI_exact_three_roots :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ρ : Fin 3 → AbsoluteDensity 1,
        (∀ j : Fin 3, 0 < ordinaryEntropy h (ρ j)) ∧
        (∀ j : Fin 3, str025_quot h (ρ j) = ordinaryLSRate (ordinaryReference h)) ∧
        (∀ (j : Fin 3) (σ : AbsoluteDensity 1), 0 < ordinaryEntropy h σ →
          str025_quot h (ρ j) ≤ str025_quot h σ) ∧
        (∀ i j : Fin 3, i ≠ j → ¬ (ρ i).density =ᵐ[haar 1] (ρ j).density) ∧
        (∀ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ →
          (∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
            str025_quot h σ ≤ str025_quot h τ) →
          ∃ j : Fin 3, σ.density =ᵐ[haar 1] (ρ j).density) ∧
        (∀ j : Fin 3, (densityMeasure (ρ j) : Measure (Torus 1)) ≠ threefoldReference h) ∧
        (∀ ν : Measure (Torus 1),
          ZeroDeficit_STR02901 h
              (ordinaryLSRate (ordinaryReference h)).toReal ν ↔
            ν = threefoldReference h ∨ ∃ j : Fin 3, ν = (densityMeasure (ρ j) : Measure (Torus 1))) :=
  DGPS.Frontier.STR029.str029_32_zero_deficit_roots

end DGPS.Examples.ThreeSpeciesCircle
