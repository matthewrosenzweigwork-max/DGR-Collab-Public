import DGPS.FiniteN.AnisotropicQuarticScale
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The exact Euclidean normalization of the quartic chart

FIN068 writes its chart on the product plane, whereas its potential and FIN069 energy use
`EuclideanSpace ℝ (Fin 2)`. These maps preserve volume exactly, and the Euclidean derivative
norm equals the sum of the two squared coordinate derivatives. No norm or volume equivalence
is left as a hypothesis.
-/

open MeasureTheory

namespace DGPS.FiniteN

/-- The actual coordinate map from the Euclidean plane to the product plane preserves volume. -/
theorem quartic_euclidean_volume_preserving :
    MeasurePreserving (fun w : EuclideanSpace ℝ (Fin 2) => (w 0, w 1)) := by
  convert (volume_preserving_finTwoArrow ℝ).comp
    (PiLp.volume_preserving_ofLp (Fin 2)) using 1 <;> rfl

/-- The actual inverse coordinate map also preserves volume. -/
theorem quartic_product_volume_preserving :
    MeasurePreserving (fun p : ℝ × ℝ => !₂[p.1, p.2]) := by
  convert (PiLp.volume_preserving_toLp (Fin 2)).comp
    (volume_preserving_finTwoArrow ℝ).symm using 1 <;> rfl

/-- Exact conversion of the product-coordinate derivative to the Euclidean energy. -/
theorem quartic_euclidean_energy (F : ℝ × ℝ → ℝ) (w : EuclideanSpace ℝ (Fin 2))
    (hF : DifferentiableAt ℝ F (w 0, w 1)) :
    ‖fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => F (z 0, z 1)) w‖ ^ 2 =
      (fderiv ℝ F (w 0, w 1) (1, 0)) ^ 2 +
        (fderiv ℝ F (w 0, w 1) (0, 1)) ^ 2 := by
  let S : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))
  have hS0 : S (EuclideanSpace.basisFun (Fin 2) ℝ 0) = (1, 0) := by
    change ((EuclideanSpace.basisFun (Fin 2) ℝ 0) 0,
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1) = (1, 0)
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hS1 : S (EuclideanSpace.basisFun (Fin 2) ℝ 1) = (0, 1) := by
    change ((EuclideanSpace.basisFun (Fin 2) ℝ 1) 0,
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) 1) = (0, 1)
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hcomp := hF.hasFDerivAt.comp w S.hasFDerivAt
  change ‖fderiv ℝ (F ∘ S) w‖ ^ 2 = _
  rw [hcomp.fderiv, groundState_norm_sq_eq_sum_basis]
  simp only [Fin.sum_univ_two, ContinuousLinearMap.comp_apply, hS0, hS1] <;> rfl

end DGPS.FiniteN
