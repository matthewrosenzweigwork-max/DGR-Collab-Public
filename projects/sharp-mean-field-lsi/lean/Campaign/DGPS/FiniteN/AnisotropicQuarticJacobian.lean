import DGPS.FiniteN.AnisotropicQuarticChangeOfVariables
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant

/-!
# The triangular Jacobian of the FIN068 inverse chart

The inverse chart is `q -> (X q,q.2)`. Its determinant equals the retained derivative `X_v`;
this identifies the actual density factor in the change-of-variables formula, rather than
adding its identification as an assumption.
-/

open MeasureTheory

namespace DGPS.FiniteN

/-- The determinant of the triangular chart derivative is its first diagonal entry. -/
theorem quartic_triangular_det (L : ℝ × ℝ →L[ℝ] ℝ) :
    (L.prod (ContinuousLinearMap.snd ℝ ℝ ℝ)).det = L (1, 0) := by
  change LinearMap.det ((L.prod (ContinuousLinearMap.snd ℝ ℝ ℝ)).toLinearMap) = _
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]

/-- For the actual inverse-map form used in FIN068, the Jacobian is `X_v`. -/
theorem quartic_inverse_chart_det (X : ℝ × ℝ → ℝ) (q : ℝ × ℝ)
    (hX : DifferentiableAt ℝ X q) :
    (fderiv ℝ (fun p : ℝ × ℝ => (X p, p.2)) q).det = fderiv ℝ X q (1, 0) := by
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  have h := hX.hasFDerivAt.prodMk hsnd
  rw [h.fderiv]
  exact quartic_triangular_det (fderiv ℝ X q)

end DGPS.FiniteN
