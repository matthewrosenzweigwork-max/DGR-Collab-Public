/- Unchecked draft: no generalized eigenvectors beyond eigenspaces for real symmetric maps. -/
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic
open scoped InnerProductSpace
namespace DGRHS.Kernel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma symmetric_apply_apply_eq_zero (S : H →ₗ[ℝ] H) (hS : S.IsSymmetric)
    (x : H) (hx : S (S x) = 0) : S x = 0 := by
  have hi := hS x (S x)
  rw [hx, inner_zero_right] at hi
  exact inner_self_eq_zero.mp hi

lemma symmetric_pow_apply_eq_zero (S : H →ₗ[ℝ] H) (hS : S.IsSymmetric)
    (n : ℕ) (hn : n ≠ 0) (x : H) (hx : (S^n) x = 0) : S x = 0 := by
  induction n generalizing x with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    by_cases hzero : n = 0
    · subst hzero
      simpa using hx
    · have hi : (S^n) (S x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hx
      exact symmetric_apply_apply_eq_zero S hS x (ih hzero (S x) hi)

lemma symmetric_maxGenEigenspace_eq (T : H →ₗ[ℝ] H) (hT : T.IsSymmetric) (eig : ℝ) :
    Module.End.maxGenEigenspace T eig = Module.End.eigenspace T eig := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace T eig x).mp hx
    have hS : (T-eig • (1 : Module.End ℝ H)).IsSymmetric := hT.sub (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one)
    have he : (T-eig • (1 : Module.End ℝ H)) x = 0 := by
      by_cases hz : n = 0
      · subst hz
        have hx0 : x = 0 := by simpa using hn
        simp [hx0]
      · exact symmetric_pow_apply_eq_zero _ hS n hz x (by simpa only [LinearMap.mem_ker] using hn)
    exact Module.End.mem_eigenspace_iff.mpr (by simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] using he)
  · exact Module.End.eigenspace_le_maxGenEigenspace
end DGRHS.Kernel
#print axioms DGRHS.Kernel.symmetric_maxGenEigenspace_eq
