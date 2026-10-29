import DGRHS.Commutator.SourceRieszTransportKernel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual positive-Riesz source force: spatial derivative of norm^(-s)/s.
Native squared-norm derivative and rpow chain rule (pinned Mathlib, Apache2)
prove its formula. Collision force is zero. Finite particle antisymmetric
symmetrization is an adaptation of root SourceLogForceSymmetry, read-only;
no logarithmic proof import or favorable force premise. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceRieszForce (s : ℝ) (z : E) : E := -(‖z‖^(-s-2)) • z

lemma sourceRieszForce_zero (s : ℝ) : sourceRieszForce (E:=E) s 0=0 := by
  simp [sourceRieszForce]

lemma sourceRieszForce_neg (s : ℝ) (z : E) : sourceRieszForce s (-z)=-sourceRieszForce s z := by
  simp only [sourceRieszForce,norm_neg,smul_neg]

lemma sourceRieszPotential_fderiv_apply (s : ℝ) (hs : 0<s) {z : E} (hz : z≠0) (w : E) :
    fderiv ℝ (sourceRieszPotential s) z w=-‖z‖^(-s-2)*⟪z,w⟫ := by
  have hsq : ‖z‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hd := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.rpow_const
    (p := -s/2) (Or.inl hsq)).const_mul s⁻¹
  have heq : sourceRieszPotential (E:=E) s=(fun t : E=>s⁻¹*(‖t‖^2)^(-s/2)) := by
    funext t
    unfold sourceRieszPotential
    rw [←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg t)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-s/2)=-s by ring]
    simp only [div_eq_mul_inv,mul_comm]
  have hrpow : (‖z‖^2)^(-s/2-1)=‖z‖^(-s-2) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg z)]
    congr 1
    ring
  rw [heq,hd.fderiv]
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply]
  rw [hrpow]
  field_simp [hs.ne']
  <;> ring

lemma sourceRieszForce_fderiv (s : ℝ) (hs : 0<s) {z : E} (hz : z≠0) (w : E) :
    ⟪sourceRieszForce s z,w⟫=fderiv ℝ (sourceRieszPotential s) z w := by
  rw [sourceRieszPotential_fderiv_apply s hs hz]
  simp [sourceRieszForce,real_inner_smul_left]

lemma sourceRieszTransportKernel_force (s : ℝ) (hs : 0<s) (v : E→E) (x y : E) :
    sourceRieszTransportKernel 1 s v (x,y)=⟪sourceRieszForce s (x-y),v x-v y⟫ := by
  by_cases hp : x=y
  · simp [sourceRieszTransportKernel,hp,sourceRieszForce_zero]
  · rw [sourceRieszTransportKernel,ite_eq_right hp,iteratedFDeriv_one_apply]
    exact (sourceRieszForce_fderiv s hs (sub_ne_zero.mpr hp) _).symm

/-- All terms include the zero collision representative, including repeated
spatial coordinates. The actual excluded-index force sum is identified below. -/
theorem sourceRiesz_dynamic_force_symmetrization (s : ℝ) (hs : 0<s)
    (N : ℕ) (x : Fin N→E) (v : E→E) :
    ∑ i : Fin N,∑ j : Fin N,sourceRieszTransportKernel 1 s v (x i,x j)=
      2*∑ i : Fin N,∑ j : Fin N,⟪sourceRieszForce s (x i-x j),v (x i)⟫ := by
  classical
  have ht : (∑ i : Fin N,∑ j : Fin N,⟪sourceRieszForce s (x i-x j),v (x j)⟫)=
      -(∑ i : Fin N,∑ j : Fin N,⟪sourceRieszForce s (x i-x j),v (x i)⟫) := by
    calc
      _ = ∑ j : Fin N,∑ i : Fin N,⟪sourceRieszForce s (x i-x j),v (x j)⟫ := Finset.sum_comm
      _ = ∑ i : Fin N,∑ j : Fin N,-⟪sourceRieszForce s (x i-x j),v (x i)⟫ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [show x j-x i=-(x i-x j) by abel,sourceRieszForce_neg,inner_neg_left]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  simp_rw [sourceRieszTransportKernel_force s hs,inner_sub_right,Finset.sum_sub_distrib]
  rw [ht]
  ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszForce
#print axioms DGRHS.Commutator.sourceRieszForce
#check @DGRHS.Commutator.sourceRieszForce_zero
#print axioms DGRHS.Commutator.sourceRieszForce_zero
#check @DGRHS.Commutator.sourceRieszForce_neg
#print axioms DGRHS.Commutator.sourceRieszForce_neg
#check @DGRHS.Commutator.sourceRieszPotential_fderiv_apply
#print axioms DGRHS.Commutator.sourceRieszPotential_fderiv_apply
#check @DGRHS.Commutator.sourceRieszForce_fderiv
#print axioms DGRHS.Commutator.sourceRieszForce_fderiv
#check @DGRHS.Commutator.sourceRieszTransportKernel_force
#print axioms DGRHS.Commutator.sourceRieszTransportKernel_force
#check @DGRHS.Commutator.sourceRiesz_dynamic_force_symmetrization
#print axioms DGRHS.Commutator.sourceRiesz_dynamic_force_symmetrization
