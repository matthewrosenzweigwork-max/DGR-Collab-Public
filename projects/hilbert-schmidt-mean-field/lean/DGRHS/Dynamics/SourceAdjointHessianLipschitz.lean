/- Source backward-adjoint Cb2 Hessian control implies the ACTUAL gradient
is globally Lipschitz with the same verified operator-norm Hessian bound.
Native Riesz dual isometry and global mean-value theorem are reused. -/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
noncomputable section
namespace DGRHS.Dynamics
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem sourceAdjoint_gradient_lipschitz_of_hessian_bound
    (q : E→ℝ) (hq : ContDiff ℝ 2 q) (K : NNReal)
    (hK : ∀ z,‖iteratedFDeriv ℝ 2 q z‖≤(K:ℝ)) :
    LipschitzWith K (gradient q) := by
  have hq' : ContDiff ℝ 1 (fderiv ℝ q) := (contDiff_succ_iff_fderiv.mp hq).2.2
  have hdf : Differentiable ℝ (fderiv ℝ q) := hq'.differentiable (by norm_num)
  have hn (z : E) : ‖fderiv ℝ (fderiv ℝ q) z‖=‖iteratedFDeriv ℝ 2 q z‖ := by
    rw [←norm_iteratedFDeriv_one (fderiv ℝ q),norm_iteratedFDeriv_fderiv]
  have hL : LipschitzWith K (fderiv ℝ q) := lipschitzWith_of_nnnorm_fderiv_le hdf (fun z=>by
    exact_mod_cast (show ‖fderiv ℝ (fderiv ℝ q) z‖≤(K:ℝ) from by
      rw [hn z]
      exact hK z))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [gradient,gradient,(InnerProductSpace.toDual ℝ E).symm.isometry.dist_eq]
  exact hL.dist_le_mul x y

end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceAdjoint_gradient_lipschitz_of_hessian_bound
#print axioms DGRHS.Dynamics.sourceAdjoint_gradient_lipschitz_of_hessian_bound
