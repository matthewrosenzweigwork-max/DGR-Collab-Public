/- Actual logarithmic force and source dynamicSymmetrization.
The same derivative contraction is used; all collision terms vanish. -/
import DGRHS.Commutator.SourceLogTransportKernel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace DGRHS.Dynamics
open DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def sourceLogForce (z : E) : E := -(‖z‖^2)⁻¹ • z

lemma sourceLogForce_neg (z : E) : sourceLogForce (-z)=-sourceLogForce z := by
  simp only [sourceLogForce,norm_neg,smul_neg]

lemma sourceLogForce_fderiv {z : E} (hz : z≠0) (w : E) :
    ⟪sourceLogForce z,w⟫=fderiv ℝ sourceLogPotential z w := by
  rw [sourceLogPotential_fderiv_apply hz]
  simp only [sourceLogForce,real_inner_smul_left,neg_mul,div_eq_mul_inv]
  ring

lemma sourceLogTransportKernel_force (v : E→E) (x y : E) :
    sourceLogTransportKernel 1 v (x,y)=⟪sourceLogForce (x-y),v x-v y⟫ := by
  rw [sourceLogTransportKernel_one]
  simp only [sourceLogForce,real_inner_smul_left,neg_mul,div_eq_mul_inv]
  ring

theorem sourceLog_dynamic_force_symmetrization (N : ℕ) (x : Fin N→E) (v : E→E) :
    ∑ i : Fin N,∑ j : Fin N,sourceLogTransportKernel 1 v (x i,x j) =
      2*∑ i : Fin N,∑ j : Fin N,⟪sourceLogForce (x i-x j),v (x i)⟫ := by
  classical
  have hs : (∑ i : Fin N,∑ j : Fin N,⟪sourceLogForce (x i-x j),v (x j)⟫) =
      -(∑ i : Fin N,∑ j : Fin N,⟪sourceLogForce (x i-x j),v (x i)⟫) := by
    calc
      _ = ∑ j : Fin N,∑ i : Fin N,⟪sourceLogForce (x i-x j),v (x j)⟫ := Finset.sum_comm
      _ = ∑ i : Fin N,∑ j : Fin N,-⟪sourceLogForce (x i-x j),v (x i)⟫ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [show x j-x i=-(x i-x j) by abel,sourceLogForce_neg,inner_neg_left]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  simp_rw [sourceLogTransportKernel_force,inner_sub_right,Finset.sum_sub_distrib]
  rw [hs]
  ring
end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLogForce
#check @DGRHS.Dynamics.sourceLogForce_neg
#check @DGRHS.Dynamics.sourceLogForce_fderiv
#check @DGRHS.Dynamics.sourceLogTransportKernel_force
#check @DGRHS.Dynamics.sourceLog_dynamic_force_symmetrization
#print axioms DGRHS.Dynamics.sourceLogForce
#print axioms DGRHS.Dynamics.sourceLogForce_neg
#print axioms DGRHS.Dynamics.sourceLogForce_fderiv
#print axioms DGRHS.Dynamics.sourceLogTransportKernel_force
#print axioms DGRHS.Dynamics.sourceLog_dynamic_force_symmetrization
