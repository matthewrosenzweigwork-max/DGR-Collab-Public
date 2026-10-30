import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorAlgebra

/-!
# Actual reference centering of the physical feature generator

The exact reference score and genuine periodic integration by parts give zero mean
for the physical generator applied to every smooth feature. This supplies the second
centered factor in the finite-rank Pinsker estimate, with no commutation assumption.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Smoothness of the actual reference density, obtained from its actual smooth logarithm. -/
theorem elementary_referenceDensity_smooth (h : ℝ) : IsSmoothPeriodic (referenceDensity h) := by
  have he : (referenceDensity h ∘ torusLift) =
      fun y : Fin 1 → ℝ => Real.exp ((ellT h ∘ torusLift) y) := by
    funext y
    exact (Real.exp_log (referenceDensity_pos (h := h) (torusLift y))).symm
  change ContDiff ℝ ∞ (referenceDensity h ∘ torusLift)
  rw [he]
  exact Real.contDiff_exp.comp (isSmoothPeriodic_ellT h)

/-- The derivative of the SAME actual reference density is its exact score times density. -/
theorem elementary_referenceDensity_derivative (h : ℝ) (x : Torus 1) :
    coordPartial 0 (referenceDensity h) x = referenceDensity h x * sigT h x := by
  have hq := elementary_referenceDensity_smooth h
  have hlog := RelativeFisher.coordPartial_comp hq
    (φ := Real.log) (D := fun t => t⁻¹)
    (fun t ht => Real.hasDerivAt_log ht.ne') (fun y => referenceDensity_pos (h := h) y) 0 x
  change sigT h x = (referenceDensity h x)⁻¹ * coordPartial 0 (referenceDensity h) x at hlog
  rw [hlog]
  field_simp [(referenceDensity_pos (h := h) x).ne']

/-- The actual physical generator of a smooth feature is continuous and hence bounded
on the compact torus. No spectral equation is presumed. -/
theorem continuous_elementaryFeatureGenerator (h : ℝ) (φ : Torus 1 → ℝ)
    (hφ : IsSmoothPeriodic φ) : Continuous (elementaryFeatureGenerator h φ) := by
  exact ((hφ.isSmoothPeriodic_coordPartial 0).continuous_coordPartial 0).neg.sub
    ((continuous_sigT h).mul (hφ.continuous_coordPartial 0))

/-- The genuine reference generator is centered against the actual reference probability.
The proof uses both physical derivatives and the actual logarithmic score. -/
theorem elementaryFeatureGenerator_reference_mean_zero (h : ℝ) (φ : Torus 1 → ℝ)
    (hφ : IsSmoothPeriodic φ) :
    (∫ x, elementaryFeatureGenerator h φ x ∂threefoldReference h) = 0 := by
  have hq := elementary_referenceDensity_smooth h
  have hd := hφ.isSmoothPeriodic_coordPartial 0
  have hi : Integrable (fun x => referenceDensity h x * coordPartial 0 (coordPartial 0 φ) x) (haar 1) :=
    ((continuous_referenceDensity h).mul (hd.continuous_coordPartial 0)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x => coordPartial 0 (referenceDensity h) x * coordPartial 0 φ x) (haar 1) :=
    ((hq.continuous_coordPartial 0).mul (hφ.continuous_coordPartial 0)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIBP := integral_mul_coordPartial_of_smooth hq hd (0 : Fin 1)
  have he : ∀ x, referenceDensity h x * elementaryFeatureGenerator h φ x =
      -(referenceDensity h x * coordPartial 0 (coordPartial 0 φ) x) -
        coordPartial 0 (referenceDensity h) x * coordPartial 0 φ x := by
    intro x
    rw [elementary_referenceDensity_derivative]
    unfold elementaryFeatureGenerator
    ring
  rw [integral_threefoldReference]
  simp_rw [he]
  rw [integral_sub
    (f := fun x => -(referenceDensity h x * coordPartial 0 (coordPartial 0 φ) x))
    (g := fun x => coordPartial 0 (referenceDensity h) x * coordPartial 0 φ x) hi.neg hj,
    integral_neg (fun x => referenceDensity h x * coordPartial 0 (coordPartial 0 φ) x), hIBP]
  ring

end DGPS.Examples.ThreeSpeciesCircle
