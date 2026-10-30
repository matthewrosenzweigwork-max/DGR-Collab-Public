import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceUpper
import DGPS.Structural.AmplitudeComparison

/-! Finiteness of the original native Gaussian and two-sector rates, directly
from the existing general upper comparison and the actual reference test. -/

noncomputable section

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Any actual coercivity proof gives a finite native Gaussian rate. -/
theorem elementaryModel_gaussianRate_ne_top {h ε : ℝ} (hh : 0 < h)
    (hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh)) :
    gaussianRate (modelData h ε) (refProb hh) hH ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (threefold_reference_poincare_ne_top hh))
    (Structural.gaussianRate_le_hessianUpper_poincare (refProb hh) (modelData h ε) hH)

/-- The native two-sector minimum is finite at the same canonical reference. -/
theorem elementaryModel_twoSectorRate_ne_top {h ε : ℝ} (hh : 0 < h)
    (hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh)) :
    twoSectorRate (modelData h ε) (ordinaryReference h) hH ≠ ⊤ :=
  ne_top_of_le_ne_top (threefold_reference_poincare_ne_top hh)
    (twoSectorRate_le_poincareRate (modelData h ε) (ordinaryReference h) hH)

end DGPS.Examples.ThreeSpeciesCircle
