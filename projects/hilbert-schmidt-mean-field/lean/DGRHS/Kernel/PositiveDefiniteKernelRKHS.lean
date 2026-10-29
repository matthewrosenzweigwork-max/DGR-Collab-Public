/- Native Moore construction reused from pinned Apache2 Mathlib Reproducing.
This bridge retains the arbitrary real finite-Gram source definition.
Scalar RKHS measurability and weak-mean centering are subsequent obligations. -/
import DGRHS.Kernel.PositiveDefiniteKernelCap
import Mathlib.Analysis.InnerProductSpace.Reproducing
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Kernel

lemma IsPositiveDefiniteKernel.gram_nonneg_fintype {Ω J : Type*} [Fintype J]
    {q : Ω→Ω→ℝ} (hq : IsPositiveDefiniteKernel q) (x : J→Ω) (c : J→ℝ) :
    0 ≤ ∑ i,∑ j,c i*c j*q (x i) (x j) := by
  classical
  let e := Fintype.equivFin J
  have he : (∑ i,∑ j,c i*c j*q (x i) (x j))=
      ∑ i : Fin (Fintype.card J),∑ j : Fin (Fintype.card J),
        c (e.symm i)*c (e.symm j)*q (x (e.symm i)) (x (e.symm j)) := by
    apply Fintype.sum_equiv e
    intro i
    apply Fintype.sum_equiv e
    intro j
    simp
  rw [he]
  exact hq.gram_nonneg _ (fun i=>x (e.symm i)) (fun i=>c (e.symm i))

 def scalarKernelMatrix {Ω : Type*} (q : Ω→Ω→ℝ) : Matrix Ω Ω (ℝ→L[ℝ]ℝ) :=
  fun x y=>q x y • ContinuousLinearMap.id ℝ ℝ

lemma IsPositiveDefiniteKernel.scalarKernel_posSemidef {Ω : Type*}
    {q : Ω→Ω→ℝ} (hq : IsPositiveDefiniteKernel q) :
    (scalarKernelMatrix q).PosSemidef := by
  classical
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_,?_⟩
  · ext x y z
    simp [scalarKernelMatrix,Matrix.IsHermitian,Matrix.conjTranspose_apply,hq.symmetric,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_id]
  · intro vv
    have h := hq.gram_nonneg_fintype (fun x : vv.support=>x.1) (fun x=>vv x.1)
    have he : (∑ i : vv.support,∑ j : vv.support,
        vv i.1*vv j.1*q i.1 j.1)=∑ i ∈ vv.support,∑ j ∈ vv.support,vv i*vv j*q i j := by
      calc
        _ = ∑ i : vv.support,∑ j ∈ vv.support,vv i.1*vv j*q i.1 j := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_coe_sort vv.support (fun j : Ω=>vv i.1*vv j*q i.1 j)
        _ = _ := Finset.sum_coe_sort vv.support (fun i : Ω=>∑ j ∈ vv.support,vv i*vv j*q i j)
    rw [he] at h
    simpa [scalarKernelMatrix,Finsupp.sum,hq.symmetric,
      real_inner_comm,mul_assoc,mul_comm,mul_left_comm] using h
end DGRHS.Kernel
#check @DGRHS.Kernel.IsPositiveDefiniteKernel.gram_nonneg_fintype
#print axioms DGRHS.Kernel.IsPositiveDefiniteKernel.gram_nonneg_fintype
#check @DGRHS.Kernel.IsPositiveDefiniteKernel.scalarKernel_posSemidef
#print axioms DGRHS.Kernel.IsPositiveDefiniteKernel.scalarKernel_posSemidef
