/- Development counting candidate.
Pinned native multivariate coefficient/multinomial expansion is reused.
No surviving-array moment or exponential bound is assumed or concluded here. -/
import Mathlib.Algebra.MvPolynomial.Coeff
import DGRHS.Concentration.Coefficients
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
noncomputable section
open scoped BigOperators
namespace DGRHS.Attractive
variable {α : Type*} [Fintype α] [DecidableEq α]

def wordMultiplicity {m : ℕ} (w : Fin m → α) : α →₀ ℕ :=
  ∑ j : Fin m,Finsupp.single (w j) 1

lemma wordMultiplicity_apply {m : ℕ} (w : Fin m → α) (i : α) :
    wordMultiplicity w i = (Finset.univ.filter (fun j : Fin m => w j=i)).card := by
  classical
  simp only [wordMultiplicity,Finsupp.finsetSum_apply,Finsupp.single_apply]
  simp [eq_comm,Finset.sum_boole]

lemma wordMultiplicity_degree {m : ℕ} (w : Fin m → α) :
    (wordMultiplicity w).sum (fun _ n => n) = m := by
  classical
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
  simp only [wordMultiplicity,Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

lemma wordMultiplicity_mem_antidiag {m : ℕ} (w : Fin m → α) :
    wordMultiplicity w ∈ Finset.finsuppAntidiag (Finset.univ : Finset α) m := by
  classical
  apply Finset.mem_finsuppAntidiag.mpr
  refine ⟨?_,Finset.subset_univ _⟩
  have heq := Finsupp.sum_of_support_subset (wordMultiplicity w)
    (Finset.subset_univ _) (fun _ n => n) (by simp)
  exact heq.symm.trans (wordMultiplicity_degree w)

lemma word_product_X {m : ℕ} (w : Fin m → α) :
    (∏ j : Fin m,MvPolynomial.X (w j) : MvPolynomial α ℕ) =
      MvPolynomial.monomial (wordMultiplicity w) 1 := by
  symm
  simpa only [wordMultiplicity,MvPolynomial.X] using
    (MvPolynomial.monomial_sum_one (R := ℕ) (Finset.univ : Finset (Fin m))
      (fun j => Finsupp.single (w j) 1))

theorem card_wordMultiplicity_fiber (m : ℕ) (d : α →₀ ℕ) :
    (Finset.univ.filter (fun w : Fin m → α => wordMultiplicity w=d)).card =
      if d.sum (fun _ n => n)=m then d.multinomial else 0 := by
  classical
  have hp := Fintype.sum_pow (fun i : α => (MvPolynomial.X i : MvPolynomial α ℕ)) m
  have hc := congrArg (fun P : MvPolynomial α ℕ => P.coeff d) hp
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype] at hc
  simp_rw [MvPolynomial.coeff_sum,word_product_X,MvPolynomial.coeff_monomial] at hc
  simpa [Finset.sum_boole] using hc.symm

lemma card_wordMultiplicity_fiber_mul_factorials (m : ℕ) (d : α →₀ ℕ)
    (hd : d.sum (fun _ n => n)=m) :
    (Finset.univ.filter (fun w : Fin m → α => wordMultiplicity w=d)).card*
      (∏ i : α,(d i).factorial) = m.factorial := by
  rw [card_wordMultiplicity_fiber,if_pos hd]
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ d.support)]
  have hsum : (∑ i : α,d i)=m := by
    have heq := Finsupp.sum_of_support_subset d
      (Finset.subset_univ _) (fun _ n => n) (by simp)
    exact heq.symm.trans hd
  simpa only [hsum,mul_comm] using Nat.multinomial_spec (Finset.univ : Finset α) d
end DGRHS.Attractive
#print axioms DGRHS.Attractive.wordMultiplicity_apply
#print axioms DGRHS.Attractive.wordMultiplicity_degree
#print axioms DGRHS.Attractive.card_wordMultiplicity_fiber
#print axioms DGRHS.Attractive.card_wordMultiplicity_fiber_mul_factorials
#check @DGRHS.Attractive.card_wordMultiplicity_fiber_mul_factorials
