import DGPS.Examples.PolynomialSmooth
import DGPS.Examples.ThreeSpeciesCircle.ThreeSpeciesCanonicalAssembly

/-! The frozen smooth-positive-density predicate is a consequence of actual
original-H1 optimizer regularity, not an added hypothesis on competitors. -/
noncomputable section
open MeasureTheory Filter
namespace DGPS.Examples.PolynomialSpecies

theorem polynomial_scalarMinimizer_smoothPositiveDensity :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h), ∀ ρ : AbsoluteDensity 1,
        0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
          scalarRate (canonical_elementary_polynomial_model h) b → SmoothPositiveDensity ρ := by
  obtain ⟨δ, hδ, hsmooth⟩ := polynomial_scalarMinimizer_smooth_representative
  refine ⟨δ, hδ, ?_⟩
  intro h hh hsmall b ρ hG hmin
  obtain ⟨v, hv, hae, hpos, _hlog⟩ := hsmooth h hh hsmall b ρ hG hmin
  refine ⟨fun x => v x ^ 2, hv.pow 2, ?_, ?_⟩
  · intro x
    exact pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hpos x)) 2
  · exact hae.mono fun x hx => congrArg (fun z : ℝ => z ^ 2) hx

end DGPS.Examples.PolynomialSpecies
