import DGPS.Examples.ThreeSpeciesCircle.InteractingForceSquareVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingFisherVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarCompactness

/-! Genuine full nonlinear dissipation differentiation along original absolute
H1 paths. Every component is the actual model functional, and its derivative is
provided by a concrete full-H1 theorem, including changing-force moments. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual nonlinear numerator has a genuine derivative on EVERY original
H1 direction. The component derivatives refer to exact model functions; their
explicit integral and finite-moment formulas are proved in the imported leaves.
No differentiability, force-freezing or optimizer-Euler premise is supplied. -/
theorem absoluteRootVariation_scalarDissipation_hasDerivAt (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt
      (fun t : ℝ => (scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ t)).toReal)
      (deriv (fun t : ℝ => (ordinaryFisher h (absoluteRootVariation ρ hφ t)).toReal) 0 +
        ε * deriv (fun t : ℝ => elementaryC h 0 (absoluteRootVariation ρ hφ t)) 0 +
        ε ^ 2 * deriv (fun t : ℝ => elementaryJ h (absoluteRootVariation ρ hφ t)) 0) 0 := by
  have hI := absoluteRootVariation_fisher_hasDerivAt h ρ hφ
  have hC := absoluteRootVariation_elementaryC_hasDerivAt h 0 ρ hφ
  have hJ := absoluteRootVariation_elementaryJ_hasDerivAt h ρ hφ
  have hId := hI.differentiableAt.hasDerivAt
  have hCd := hC.differentiableAt.hasDerivAt
  have hJd := (HasDerivAt.differentiableAt hJ).hasDerivAt
  have hsum := (hId.add (hCd.const_mul ε)).add (hJd.const_mul (ε ^ 2))
  have he : (fun t : ℝ =>
      (scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ t)).toReal) =
      fun t : ℝ => (ordinaryFisher h (absoluteRootVariation ρ hφ t)).toReal +
        ε * elementaryC h 0 (absoluteRootVariation ρ hφ t) +
        ε ^ 2 * elementaryJ h (absoluteRootVariation ρ hφ t) := by
    funext t
    exact (elementaryModel_scalarDissipation_real h ε b (absoluteRootVariation ρ hφ t)).2
  rw [he]
  exact hsum

end DGPS.Examples.ThreeSpeciesCircle
