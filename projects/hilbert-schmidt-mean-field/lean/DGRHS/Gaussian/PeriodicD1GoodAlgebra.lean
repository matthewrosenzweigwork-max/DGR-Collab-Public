import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! Draft, not yet compiler-checked. Algebraic step of I. J. Good's 1970
Dyson recurrence (J. Math. Phys. 11, 1884). We apply the actual native
Lagrange.sum_basis identity; no Dyson coefficient/integral identity is a premise.
Exact native source and Apache license are retained in the D1 moment-route records.
The finite vertex subset keeps the ambient particle coordinate type fixed. -/
noncomputable section
open scoped BigOperators Classical
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [DecidableEq ι]

def periodicD1GoodRow (s : Finset ι) (z : ι → ℂ) (i : ι) : ℂ :=
  ∏ j ∈ s.erase i, (1-z i/z j)

def periodicD1GoodWeight (s : Finset ι) (a : ι → ℕ) (z : ι → ℂ) : ℂ :=
  ∏ i ∈ s, periodicD1GoodRow s z i ^ a i

lemma periodicD1GoodWeight_empty (a : ι → ℕ) (z : ι → ℂ) :
    periodicD1GoodWeight ∅ a z=1 := by simp [periodicD1GoodWeight]

lemma periodicD1GoodWeight_zero (s : Finset ι) (z : ι → ℂ) :
    periodicD1GoodWeight s (fun _ => 0) z=1 := by simp [periodicD1GoodWeight]

lemma periodicD1GoodRow_ne_zero (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ j∈s,z j≠0) (hinj : Set.InjOn z s) {i : ι} (hi : i∈s) :
    periodicD1GoodRow s z i≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hj' := Finset.mem_erase.mp hj
  apply sub_ne_zero.mpr
  intro h
  have he : z i=z j := (div_eq_one_iff_eq (hz j hj'.2)).mp h.symm
  exact hj'.1 (hinj hi hj'.2 he).symm

/-- Lagrange interpolation of one, evaluated at zero: Good's exact multiplier. -/
lemma periodicD1GoodRow_inv_sum (s : Finset ι) (hs : s.Nonempty) (z : ι → ℂ)
    (hz : ∀ j∈s,z j≠0) (hinj : Set.InjOn z s) :
    (∑ i∈s,(periodicD1GoodRow s z i)⁻¹)=1 := by
  have h := congrArg (Polynomial.eval (0:ℂ)) (Lagrange.sum_basis hinj hs)
  rw [Polynomial.eval_finsetSum,Polynomial.eval_one] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [periodicD1GoodRow,←Finset.prod_inv_distrib,Lagrange.basis,
    Polynomial.eval_prod,Lagrange.basisDivisor,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X,zero_sub]
  apply Finset.prod_congr rfl
  intro j hj
  have hzj := hz j (Finset.mem_erase.mp hj).2
  have he : 1-z i/z j=(z j-z i)/z j := by field_simp [hzj]
  rw [he,inv_div,show z j-z i=-(z i-z j) by ring,div_neg,div_eq_mul_inv]
  ring

lemma periodicD1GoodWeight_lower_mul (s : Finset ι) (a : ι → ℕ) (z : ι → ℂ)
    {i : ι} (hi : i∈s) (ha : 0<a i) :
    periodicD1GoodRow s z i * periodicD1GoodWeight s (Function.update a i (a i-1)) z=
      periodicD1GoodWeight s a z := by
  have hl : periodicD1GoodWeight s (Function.update a i (a i-1)) z=
      periodicD1GoodRow s z i^(a i-1)*∏ j∈s.erase i,periodicD1GoodRow s z j^a j := by
    rw [periodicD1GoodWeight,←Finset.mul_prod_erase _ _ hi]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hl,periodicD1GoodWeight,←Finset.mul_prod_erase _ _ hi,←mul_assoc,←pow_succ']
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ha))]

lemma periodicD1GoodWeight_lower_eq_div (s : Finset ι) (a : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ j∈s,z j≠0) (hinj : Set.InjOn z s) {i : ι} (hi : i∈s) (ha : 0<a i) :
    periodicD1GoodWeight s (Function.update a i (a i-1)) z=
      periodicD1GoodWeight s a z/periodicD1GoodRow s z i := by
  apply (eq_div_iff (periodicD1GoodRow_ne_zero s z hz hinj hi)).mpr
  simpa only [mul_comm] using periodicD1GoodWeight_lower_mul s a z hi ha

/-- The recurrence has only unit/distinct-node and positive-exponent assumptions. -/
theorem periodicD1GoodWeight_recurrence (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℕ) (ha : ∀ i∈s,0<a i) (z : ι → ℂ)
    (hz : ∀ j∈s,z j≠0) (hinj : Set.InjOn z s) :
    periodicD1GoodWeight s a z=
      ∑ i∈s,periodicD1GoodWeight s (Function.update a i (a i-1)) z := by
  calc
    _ = periodicD1GoodWeight s a z * ∑ i∈s,(periodicD1GoodRow s z i)⁻¹ := by
      rw [periodicD1GoodRow_inv_sum s hs z hz hinj,mul_one]
    _ = ∑ i∈s,periodicD1GoodWeight s a z*(periodicD1GoodRow s z i)⁻¹ := by
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [periodicD1GoodWeight_lower_eq_div s a z hz hinj hi (ha i hi),div_eq_mul_inv]

lemma periodicD1GoodRow_erase (s : Finset ι) (z : ι → ℂ)
    {k i : ι} (hk : k∈s) (hki : k≠i) :
    periodicD1GoodRow s z i=(1-z i/z k)*periodicD1GoodRow (s.erase k) z i := by
  unfold periodicD1GoodRow
  have he : (s.erase i).erase k=(s.erase k).erase i := by
    ext j
    simp only [Finset.mem_erase]
    tauto
  rw [←Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hki,hk⟩),he]

/-- A zero exponent leaves only nonpositive powers of its circle coordinate. -/
lemma periodicD1GoodWeight_zero_exponent (s : Finset ι) (a : ι → ℕ) (z : ι → ℂ)
    {k : ι} (hk : k∈s) (ha : a k=0) :
    periodicD1GoodWeight s a z=periodicD1GoodWeight (s.erase k) a z *
      ∏ i∈s.erase k,(1-z i/z k)^a i := by
  rw [periodicD1GoodWeight,←Finset.mul_prod_erase _ _ hk,ha,pow_zero,one_mul]
  calc
    _ = ∏ i∈s.erase k,periodicD1GoodRow (s.erase k) z i^a i*(1-z i/z k)^a i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [periodicD1GoodRow_erase s z hk (Finset.mem_erase.mp hi).1.symm,mul_pow,mul_comm]
    _ = _ := by rw [Finset.prod_mul_distrib]; rfl

lemma periodicD1GoodWeight_congr_nodes (s : Finset ι) (a : ι → ℕ)
    {z w : ι → ℂ} (h : ∀ i∈s,z i=w i) :
    periodicD1GoodWeight s a z=periodicD1GoodWeight s a w := by
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [h i hi,h j (Finset.mem_erase.mp hj).2]

end DGRHS.Periodic
