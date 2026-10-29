/- Preparation: zero eigenvalues contribute exactly one to the regularized product.
This removes zero basis indices; it does not prove multiplicity cardinalities. -/
import DGRHS.Kernel.RegularizedDeterminant
namespace DGRHS.Kernel
variable {ι : Type*}
theorem regularizedDet_restrict_nonzero (eig : ι → ℝ) (β : ℝ) :
    regularizedDet (fun i ↦ β * eig i) =
      regularizedDet (fun i : {j // eig j ≠ 0} ↦ β * eig i.val) := by
  unfold regularizedDet
  symm
  apply tprod_subtype_eq_of_mulSupport_subset
    (f := fun i : ι ↦ (1 + β * eig i) * Real.exp (-(β * eig i)))
    (s := {i | eig i ≠ 0})
  intro i hi
  intro hz
  exact hi (by simp [hz])
end DGRHS.Kernel
#print axioms DGRHS.Kernel.regularizedDet_restrict_nonzero
