/- Actual zero quadratic labels vanish in the SAME product process. Zero-mode
linear coefficients are unaffected and must be retained in the isometry. -/
import DGRHS.Gaussian.CenteredChaos
namespace DGRHS.Gaussian
variable {ι : Type*}
lemma centeredGaussianChaos_restrict_nonzero (a : ι → ℝ) (f : ι → ℕ) :
    centeredGaussianChaos (fun i : {j // a j ≠ 0} => a i.val) (fun i => f i.val) =
      centeredGaussianChaos a f := by
  unfold centeredGaussianChaos
  change (∑' i : {j // a j ≠ 0}, centeredChaosTerm a f i.val) = _
  apply tsum_subtype_eq_of_support_subset (s := {i | a i ≠ 0})
  intro i hi
  intro hz
  exact hi (by simp [centeredChaosTerm,hz])
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.centeredGaussianChaos_restrict_nonzero
