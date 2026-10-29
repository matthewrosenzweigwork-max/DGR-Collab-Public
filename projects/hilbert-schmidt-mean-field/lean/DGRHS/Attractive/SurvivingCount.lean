/- Development candidate. Exact no-singleton vector count through
native power-series coefficient expansion. No array moment premise. -/
import DGRHS.Attractive.WordMultiplicity
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
noncomputable section
open scoped BigOperators
namespace DGRHS.Attractive
variable {α : Type*} [Fintype α] [DecidableEq α]

def noSingletonVectors (m : ℕ) : Finset (α →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ m).filter (fun d => ∀ i, d i ≠ 1)

def noSingletonWords (m : ℕ) : Finset (Fin m → α) :=
  Finset.univ.filter (fun w => ∀ i, wordMultiplicity w i ≠ 1)

def vectorCountPolynomial (m : ℕ) : Polynomial ℝ :=
  PowerSeries.trunc (m+1) (PowerSeries.mk (fun r => if r=1 then 0 else 1))

def wordCountPolynomial (m : ℕ) : Polynomial ℝ :=
  PowerSeries.trunc (m+1) (PowerSeries.mk
    (fun r => if r=1 then 0 else 1/(r.factorial:ℝ)))

lemma vectorCountPolynomial_coeff (m r : ℕ) (hr : r≤m) :
    (vectorCountPolynomial m).coeff r = if r=1 then 0 else 1 := by
  simp only [vectorCountPolynomial,PowerSeries.coeff_trunc,PowerSeries.coeff_mk,
    if_pos (by omega : r<m+1)]

lemma vectorCountPolynomial_coeff_nonneg (m r : ℕ) :
    0≤(vectorCountPolynomial m).coeff r := by
  simp only [vectorCountPolynomial,PowerSeries.coeff_trunc,PowerSeries.coeff_mk]
  split_ifs <;> norm_num

lemma wordCountPolynomial_coeff (m r : ℕ) (hr : r≤m) :
    (wordCountPolynomial m).coeff r = if r=1 then 0 else 1/(r.factorial:ℝ) := by
  simp only [wordCountPolynomial,PowerSeries.coeff_trunc,PowerSeries.coeff_mk,
    if_pos (by omega : r<m+1)]

lemma wordCountPolynomial_coeff_nonneg (m r : ℕ) :
    0≤(wordCountPolynomial m).coeff r := by
  simp only [wordCountPolynomial,PowerSeries.coeff_trunc,PowerSeries.coeff_mk]
  split_ifs <;> positivity

lemma card_noSingletonVectors_eq_coefficient (m : ℕ) :
    ((noSingletonVectors (α:=α) m).card:ℝ) =
      ((vectorCountPolynomial m)^(Fintype.card α)).coeff m := by
  classical
  have hprod : (vectorCountPolynomial m)^(Fintype.card α)=
      ∏ _ : α,vectorCountPolynomial m := by simp
  rw [hprod,DGRHS.Concentration.polynomial_coeff_prod]
  have ht (d : α →₀ ℕ) (hd : d∈Finset.finsuppAntidiag Finset.univ m) :
      (∏ i : α,(vectorCountPolynomial m).coeff (d i))=
        if ∀ i,d i≠1 then 1 else 0 := by
    have hcoeff (i : α) : (vectorCountPolynomial m).coeff (d i)=
        if d i≠1 then 1 else 0 := by
      rw [vectorCountPolynomial_coeff m (d i)
        (DGRHS.Concentration.antidiagonal_degree_le Finset.univ m d hd i (Finset.mem_univ i))]
      split_ifs <;> simp_all
    simp_rw [hcoeff]
    exact Fintype.prod_boole
  rw [Finset.sum_congr rfl ht]
  simp [noSingletonVectors,Finset.sum_boole]

lemma wordMultiplicity_mem_noSingletonVectors_iff (m : ℕ) (w : Fin m→α) :
    wordMultiplicity w ∈ noSingletonVectors m ↔ ∀ i,wordMultiplicity w i≠1 := by
  simp only [noSingletonVectors,Finset.mem_filter]
  exact and_iff_right (wordMultiplicity_mem_antidiag w)

lemma card_noSingletonWords_eq_sum_fibers (m : ℕ) :
    (noSingletonWords (α:=α) m).card =
      ∑ d∈noSingletonVectors m,
        (Finset.univ.filter (fun w : Fin m→α => wordMultiplicity w=d)).card := by
  classical
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext w
  simp [noSingletonWords,wordMultiplicity_mem_noSingletonVectors_iff]

lemma card_noSingletonWords_eq_coefficient (m : ℕ) :
    ((noSingletonWords (α:=α) m).card:ℝ) =
      (m.factorial:ℝ)*((wordCountPolynomial m)^(Fintype.card α)).coeff m := by
  classical
  have hprod : (wordCountPolynomial m)^(Fintype.card α)=
      ∏ _ : α,wordCountPolynomial m := by simp
  rw [hprod,DGRHS.Concentration.polynomial_coeff_prod]
  have ht (d : α →₀ ℕ) (hd : d∈Finset.finsuppAntidiag Finset.univ m) :
      (∏ i : α,(wordCountPolynomial m).coeff (d i))=
        if ∀ i,d i≠1 then 1/(∏ i : α,(d i).factorial:ℝ) else 0 := by
    have hcoeff (i : α) : (wordCountPolynomial m).coeff (d i)=
        if d i≠1 then 1/((d i).factorial:ℝ) else 0 := by
      rw [wordCountPolynomial_coeff m (d i)
        (DGRHS.Concentration.antidiagonal_degree_le Finset.univ m d hd i (Finset.mem_univ i))]
      split_ifs <;> simp_all
    simp_rw [hcoeff]
    rw [Fintype.prod_ite_zero,Finset.prod_div_distrib]
    simp
  rw [Finset.sum_congr rfl ht,←Finset.sum_filter]
  change _=(m.factorial:ℝ)*∑ d∈noSingletonVectors m,1/(∏ i : α,(d i).factorial:ℝ)
  rw [card_noSingletonWords_eq_sum_fibers,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have ha := (Finset.mem_filter.mp hd).1
  have hdeg : d.sum (fun _ n => n)=m := by
    have heq := Finsupp.sum_of_support_subset d (Finset.subset_univ _) (fun _ n=>n) (by simp)
    exact heq.trans (Finset.mem_finsuppAntidiag.mp ha).1
  have hc : ((Finset.univ.filter (fun w : Fin m→α => wordMultiplicity w=d)).card:ℝ)*
      (∏ i : α,(d i).factorial:ℝ)=(m.factorial:ℝ) := by
    exact_mod_cast card_wordMultiplicity_fiber_mul_factorials m d hdeg
  have hp : (∏ i : α,(d i).factorial:ℝ)≠0 := by
    apply ne_of_gt
    exact Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (d i))
  rw [mul_one_div]
  exact (eq_div_iff hp).2 hc

lemma sum_noSingletonWords_factorials (m : ℕ) :
    (∑ w∈noSingletonWords (α:=α) m,∏ i : α,(wordMultiplicity w i).factorial)=
      m.factorial*(noSingletonVectors (α:=α) m).card := by
  classical
  have hm (w : Fin m→α) (hw : w∈noSingletonWords m) :
      wordMultiplicity w∈noSingletonVectors m := by
    apply (wordMultiplicity_mem_noSingletonVectors_iff m w).2
    exact (Finset.mem_filter.mp hw).2
  rw [←Finset.sum_fiberwise_of_maps_to hm
    (fun w => ∏ i : α,(wordMultiplicity w i).factorial)]
  have hterm (d : α →₀ ℕ) (hd : d∈noSingletonVectors m) :
      (∑ w∈(noSingletonWords m).filter (fun w => wordMultiplicity w=d),
        ∏ i : α,(wordMultiplicity w i).factorial)=m.factorial := by
    have hf : (noSingletonWords m).filter (fun w => wordMultiplicity w=d)=
        Finset.univ.filter (fun w : Fin m→α => wordMultiplicity w=d) := by
      ext w
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · exact fun h => h.2
      · intro he
        refine ⟨?_,he⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        simpa only [he] using (Finset.mem_filter.mp hd).2
    rw [hf]
    have he : (∑ w∈Finset.univ.filter (fun w : Fin m→α => wordMultiplicity w=d),
        ∏ i : α,(wordMultiplicity w i).factorial)=
        (Finset.univ.filter (fun w : Fin m→α => wordMultiplicity w=d)).card*
          ∏ i : α,(d i).factorial := by
      rw [←Finset.sum_const_nat (m:=∏ i : α,(d i).factorial)]
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    rw [he]
    have ha := (Finset.mem_filter.mp hd).1
    have hdeg : d.sum (fun _ n=>n)=m := by
      have hs := Finsupp.sum_of_support_subset d (Finset.subset_univ _) (fun _ n=>n) (by simp)
      exact hs.trans (Finset.mem_finsuppAntidiag.mp ha).1
    exact card_wordMultiplicity_fiber_mul_factorials m d hdeg
  rw [Finset.sum_congr rfl hterm]
  simp [mul_comm]

lemma surviving_pair_factorial_count (m : ℕ) :
    (∑ i∈noSingletonWords (α:=α) m,∑ _j∈noSingletonWords (α:=α) m,
      ∏ a : α,(wordMultiplicity i a).factorial)=
      m.factorial*(noSingletonVectors (α:=α) m).card*(noSingletonWords (α:=α) m).card := by
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [←Finset.mul_sum,sum_noSingletonWords_factorials]
  simp only [Nat.cast_id]
  ring

lemma polynomial_coeff_mul_pow_le_eval (P : Polynomial ℝ)
    (hP : ∀ n,0≤P.coeff n) (t : ℝ) (ht : 0≤t) (m : ℕ) :
    P.coeff m*t^m≤P.eval t := by
  classical
  have he : P.eval t=∑ n∈P.support,P.coeff n*t^n := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  rw [he]
  by_cases hm : m∈P.support
  · exact Finset.single_le_sum (fun n _ => mul_nonneg (hP n) (pow_nonneg ht n)) hm
  · rw [Polynomial.notMem_support_iff.mp hm,zero_mul]
    exact Finset.sum_nonneg (fun n _ => mul_nonneg (hP n) (pow_nonneg ht n))

end DGRHS.Attractive
#print axioms DGRHS.Attractive.card_noSingletonVectors_eq_coefficient
#print axioms DGRHS.Attractive.card_noSingletonWords_eq_sum_fibers
#print axioms DGRHS.Attractive.card_noSingletonWords_eq_coefficient
#print axioms DGRHS.Attractive.polynomial_coeff_mul_pow_le_eval
#print axioms DGRHS.Attractive.sum_noSingletonWords_factorials
#print axioms DGRHS.Attractive.surviving_pair_factorial_count
