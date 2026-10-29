import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
namespace DGRHS.Gaussian

/-- An actual dyadic/geometric scale selector with its lower-index control.
The comparison window is constructed using the native Archimedean theorem. -/
theorem sharpness_geometric_scale_select (b v X : ℝ) (hb : 1 < b) (hv : 0 < v)
    (m0 : ℕ) (hX : v*b^m0 ≤ X) :
    ∃ m : ℕ,m0 ≤ m ∧ v*b^m ≤ X ∧ X < b*(v*b^m) := by
  have hratio : 1 ≤ X/(v*b^m0) := (le_div_iff₀ (by positivity : 0 < v*b^m0)).mpr (by simpa using hX)
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near hratio hb
  refine ⟨m0+j,by omega,?_,?_⟩
  · have hh := (le_div_iff₀ (by positivity : 0 < v*b^m0)).mp hj
    rw [pow_add]
    nlinarith
  · have hh := (div_lt_iff₀ (by positivity : 0 < v*b^m0)).mp hj'
    rw [pow_succ] at hh
    rw [pow_add]
    convert hh using 1 <;> ring

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_geometric_scale_select
#check @DGRHS.Gaussian.sharpness_geometric_scale_select
