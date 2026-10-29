import FullLabeledLSI.Examples.E01h8_NonlinearEq
import FullLabeledLSI.Examples.E01h7_Trial
import FullLabeledLSI.Examples.E01h6_Zero

/-!
# Lane D, Task D: Proposition 9.10 (final theorem, frozen statement)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem nonlinear_equality :
    0 < rMs zeroV (attrW poissonKernel) ∧ rMs zeroV (attrW poissonKernel) = rStar zeroV (attrW poissonKernel) ∧
      rStar zeroV (attrW poissonKernel) < ENNReal.ofReal aCos ∧
      LamGValue (attrW poissonKernel) (ENNReal.ofReal aCos) ∧
      (∃ ρ : Torus 1 → ℝ, IsSmoothT ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
        ¬ (ρ =ᵐ[haar 1] fun _ => 1) ∧ 0 < gap zeroV (attrW poissonKernel) (densMeasure ρ) ∧
        dissipation zeroV (attrW poissonKernel) ρ =
          2 * rStar zeroV (attrW poissonKernel) *
            (gap zeroV (attrW poissonKernel) (densMeasure ρ)).toENNReal) ∧
      Tendsto (fun N => rAll zeroV (attrW poissonKernel) N) atTop (𝓝 (rStar zeroV (attrW poissonKernel))) ∧
      Tendsto (fun N => rSym zeroV (attrW poissonKernel) N) atTop (𝓝 (rStar zeroV (attrW poissonKernel))) := by
  exact nonlinear_equality_core
    (hzero_of_bound poisson_good abs_poisson_le (by norm_num)) trial_exists

end SharpLSI.FL.Ex.LaneD
