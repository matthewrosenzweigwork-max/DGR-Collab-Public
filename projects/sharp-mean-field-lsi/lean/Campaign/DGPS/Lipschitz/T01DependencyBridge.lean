import DGPS.Lipschitz.KernelApproximation
import FullLabeledLSI.Paper.Lindeberg1

/-!
# Direct-Lipschitz inputs to the existing labeled replacement machinery

The continuous representatives in campaign spectral data already form the measurable bounded
orthonormal system required by the full-labeled Lindeberg argument. No semiconvexity hypothesis
or particle lower bound is used in this adapter.
-/

namespace DGPS.Lipschitz

open KernelApproximation

/-- Campaign spectral representatives satisfy the exact bounded-basis interface of the
full-labeled replacement theorem. -/
theorem goodBasis_of_spec_aux {d : ℕ} (S : Spec d) (A : Aux S) :
    SharpLSI.FL.GoodBasis S.mu S.v where
  zero := funext A.v0
  meas := fun j => (S.vc j).measurable
  bdd := fun j => ⟨A.Kc * (1 + S.lam j) ^ d, fun x =>
    (le_add_of_nonneg_right (norm_nonneg (A.g j x))).trans (A.c1 j x)⟩
  orth := S.orth

end DGPS.Lipschitz
