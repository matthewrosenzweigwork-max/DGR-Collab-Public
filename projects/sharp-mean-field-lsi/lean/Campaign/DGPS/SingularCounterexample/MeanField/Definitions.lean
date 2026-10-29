import DGPS.Examples.PositiveH1.Nonlinear
import DGPS.Analysis.CircleLSI

/-!
# Singular-kernel mean-field functionals

The interaction energy is relative to probability Haar measure. On the absolute square-root
`H¹` domain the force differentiates the density rather than the kernel. Gaps and dissipations
are real; only the variational rates take values in `ℝ≥0∞`.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.SingularCounterexample

/-- Circle convolution in the existing probability-Haar convention (SLC-M001). -/
noncomputable abbrev conv (k f : Torus 1 → ℝ) : Torus 1 → ℝ :=
  Examples.PositiveH1.Nonlinear.conv k f

/-- Interaction energy minus its value at Haar (SLC-M002). -/
noncomputable def interactionGap (k : Torus 1 → ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  (∫ x, ρ.density x * conv k ρ.density x ∂haar 1) -
    ∫ x, (1 : ℝ) * conv k (fun _ => 1) x ∂haar 1

/-- Scalar free-energy gap, with the DGPS factor `1/2` (SLC-M003). -/
noncomputable def scalarGap (k : Torus 1 → ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  Analysis.circleEntropy ρ + (1 / 2 : ℝ) * interactionGap k ρ

/-- The weak force `k ⋆ ρ′`, with the existing weak derivative of the density. -/
noncomputable def singularForce (k : Torus 1 → ℝ) (ρ : AbsoluteDensity 1) : Torus 1 → ℝ :=
  conv k (Examples.PositiveH1.Nonlinear.densityDeriv ρ)

/-- The absolute square-root score, including densities that vanish. -/
noncomputable def scalarScore (k : Torus 1 → ℝ) (ρ : AbsoluteDensity 1)
    (x : Torus 1) : ℝ :=
  2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 + ρ.sqrt x * singularForce k ρ x

/-- Scalar dissipation on the absolute square-root `H¹` domain (SLC-M004). -/
noncomputable def scalarDissipation (k : Torus 1 → ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  ∫ x, |scalarScore k ρ x| ^ 2 ∂haar 1

/-- Scalar quotient in the DGPS normalization. -/
noncomputable def scalarQuotient (k : Torus 1 → ℝ) (ρ : AbsoluteDensity 1) : ℝ≥0∞ :=
  ENNReal.ofReal (scalarDissipation k ρ / (2 * scalarGap k ρ))

/-- Scalar PL rate over every positive-gap absolute density; the empty infimum is `⊤`
(SLC-M005). -/
noncomputable def singularScalarPLRate (k : Torus 1 → ℝ) : ℝ≥0∞ :=
  ⨅ ρ : {ρ : AbsoluteDensity 1 // 0 < scalarGap k ρ}, scalarQuotient k ρ.1

/-- Species gap: weighted species entropies and interaction of the barycenter. -/
noncomputable def speciesGap (k : Torus 1 → ℝ) (F : SpeciesFamily 1) : ℝ :=
  (∑ s, F.weight s * Analysis.circleEntropy (F.density s)) +
    (1 / 2 : ℝ) * interactionGap k (barycenter F)

/-- Each species uses the same force, that of the barycenter. -/
noncomputable def speciesScore (k : Torus 1 → ℝ) (F : SpeciesFamily 1)
    (s : Fin F.count) (x : Torus 1) : ℝ :=
  2 * weakGradient (F.density s).sqrt (F.density s).sqrt_mem x 0 +
    (F.density s).sqrt x * singularForce k (barycenter F) x

/-- Weighted species dissipation, with no restriction on positive weights or finite count. -/
noncomputable def speciesDissipation (k : Torus 1 → ℝ) (F : SpeciesFamily 1) : ℝ :=
  ∑ s, F.weight s * ∫ x, |speciesScore k F s x| ^ 2 ∂haar 1

/-- Species quotient in the DGPS normalization. -/
noncomputable def speciesQuotient (k : Torus 1 → ℝ) (F : SpeciesFamily 1) : ℝ≥0∞ :=
  ENNReal.ofReal (speciesDissipation k F / (2 * speciesGap k F))

/-- Species PL rate over all finite positive-weight families with positive gap. -/
noncomputable def singularSpeciesPLRate (k : Torus 1 → ℝ) : ℝ≥0∞ :=
  ⨅ F : {F : SpeciesFamily 1 // 0 < speciesGap k F}, speciesQuotient k F.1

end DGPS.SingularCounterexample
