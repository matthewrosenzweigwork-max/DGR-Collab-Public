import DGRHS.Gaussian.PeriodicD1GoodHaar

/-! Uncompiled draft: Good's full multinomial normalization for the actual
Haar integral. Both recurrence and boundary are proved upstream for the actual
weight. No constant-term evaluation, Dyson integral or desired normalization
is supplied as a hypothesis. -/
noncomputable section
open scoped BigOperators Classical
namespace DGRHS.Periodic
variable {N : ℕ}

def periodicD1GoodMultinomial (s : Finset (Fin N)) (a : Fin N → ℕ) : ℂ :=
  ((∑ i∈s,a i).factorial:ℂ)/(∏ i∈s,((a i).factorial:ℂ))

lemma periodicD1Good_factorial_prod_ne_zero (s : Finset (Fin N)) (a : Fin N → ℕ) :
    (∏ i∈s,((a i).factorial:ℂ))≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

lemma periodicD1Good_factorial_pred (m : ℕ) (hm : 0<m) :
    m.factorial=m*(m-1).factorial := by
  have h : m-1+1=m := Nat.sub_add_cancel hm
  conv_lhs => rw [←h,Nat.factorial_succ]
  rw [h]

lemma periodicD1Good_sum_lower (s : Finset (Fin N)) (a : Fin N → ℕ)
    {i : Fin N} (hi : i∈s) (ha : 0<a i) :
    (∑ j∈s,Function.update a i (a i-1) j)=(∑ j∈s,a j)-1 := by
  have he : (∑ j∈s.erase i,Function.update a i (a i-1) j)=∑ j∈s.erase i,a j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [←Finset.add_sum_erase _ _ hi,Function.update_self,he,
    ←Finset.add_sum_erase s a hi]
  omega

lemma periodicD1Good_factorial_prod_lower (s : Finset (Fin N)) (a : Fin N → ℕ)
    {i : Fin N} (hi : i∈s) (ha : 0<a i) :
    (a i:ℂ)*(∏ j∈s,((Function.update a i (a i-1) j).factorial:ℂ))=
      ∏ j∈s,((a j).factorial:ℂ) := by
  have he : (∏ j∈s.erase i,((Function.update a i (a i-1) j).factorial:ℂ))=
      ∏ j∈s.erase i,((a j).factorial:ℂ) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [←Finset.mul_prod_erase _ _ hi,Function.update_self,he,
    ←Finset.mul_prod_erase s (fun j => ((a j).factorial:ℂ)) hi,←mul_assoc]
  congr 1
  exact_mod_cast (periodicD1Good_factorial_pred (a i) ha).symm

lemma periodicD1GoodMultinomial_empty (a : Fin N → ℕ) :
    periodicD1GoodMultinomial ∅ a=1 := by simp [periodicD1GoodMultinomial]

lemma periodicD1GoodMultinomial_boundary (s : Finset (Fin N)) (a : Fin N → ℕ)
    {k : Fin N} (hk : k∈s) (ha : a k=0) :
    periodicD1GoodMultinomial s a=periodicD1GoodMultinomial (s.erase k) a := by
  unfold periodicD1GoodMultinomial
  rw [←Finset.add_sum_erase s a hk,ha,zero_add,
    ←Finset.mul_prod_erase s (fun j => ((a j).factorial:ℂ)) hk,ha]
  simp

lemma periodicD1GoodMultinomial_lower (s : Finset (Fin N)) (a : Fin N → ℕ)
    {i : Fin N} (hi : i∈s) (ha : 0<a i) :
    periodicD1GoodMultinomial s (Function.update a i (a i-1))=
      (a i:ℂ)*(((∑ j∈s,a j)-1).factorial:ℂ)/(∏ j∈s,((a j).factorial:ℂ)) := by
  unfold periodicD1GoodMultinomial
  rw [periodicD1Good_sum_lower s a hi ha,
    ←periodicD1Good_factorial_prod_lower s a hi ha]
  have hi0 : (a i:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  field_simp [hi0,periodicD1Good_factorial_prod_ne_zero s (Function.update a i (a i-1))]

lemma periodicD1GoodMultinomial_recurrence (s : Finset (Fin N)) (hs : s.Nonempty)
    (a : Fin N → ℕ) (ha : ∀ i∈s,0<a i) :
    periodicD1GoodMultinomial s a=
      ∑ i∈s,periodicD1GoodMultinomial s (Function.update a i (a i-1)) := by
  have hsum : 0<∑ i∈s,a i := by
    obtain ⟨i,hi⟩ := hs
    exact lt_of_lt_of_le (ha i hi) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
  symm
  calc
    _ = ∑ i∈s,(a i:ℂ)*(((∑ j∈s,a j)-1).factorial:ℂ)/
        (∏ j∈s,((a j).factorial:ℂ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact periodicD1GoodMultinomial_lower s a hi (ha i hi)
    _ = ((∑ i∈s,a i:ℕ):ℂ)*(((∑ j∈s,a j)-1).factorial:ℂ)/
        (∏ j∈s,((a j).factorial:ℂ)) := by
      rw [←Finset.sum_div,←Finset.sum_mul,Nat.cast_sum]
    _ = _ := by
      unfold periodicD1GoodMultinomial
      congr 1
      exact_mod_cast (periodicD1Good_factorial_pred (∑ i∈s,a i) hsum).symm

/-- The multinomial normalization of the literal Haar integral, for every
finite particle subset and every vector of nonnegative integer exponents. -/
theorem periodicD1GoodIntegral_eq_multinomial (s : Finset (Fin N)) (a : Fin N → ℕ) :
    periodicD1GoodIntegral s a=periodicD1GoodMultinomial s a := by
  induction hn : s.card+∑ i∈s,a i using Nat.strong_induction_on generalizing s a with
  | h n ih =>
    by_cases hs0 : s=∅
    · subst s
      rw [periodicD1GoodIntegral_empty,periodicD1GoodMultinomial_empty]
    · have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
      by_cases hz : ∃ k∈s,a k=0
      · obtain ⟨k,hk,hak⟩ := hz
        rw [periodicD1GoodIntegral_boundary s a hk hak,
          periodicD1GoodMultinomial_boundary s a hk hak]
        have he : (∑ i∈s.erase k,a i)=∑ i∈s,a i := by
          have hh := Finset.add_sum_erase s a hk
          simpa only [hak,zero_add] using hh
        apply ih ((s.erase k).card+∑ i∈s.erase k,a i) ?_ (s.erase k) a rfl
        rw [he,Finset.card_erase_of_mem hk]
        have hc : 0<s.card := Finset.card_pos.mpr hs
        omega
      · have ha : ∀ i∈s,0<a i := by
          intro i hi
          exact Nat.pos_of_ne_zero (fun he => hz ⟨i,hi,he⟩)
        rw [periodicD1GoodIntegral_recurrence s hs a ha,
          periodicD1GoodMultinomial_recurrence s hs a ha]
        apply Finset.sum_congr rfl
        intro i hi
        apply ih (s.card+∑ j∈s,Function.update a i (a i-1) j) ?_
          s (Function.update a i (a i-1)) rfl
        rw [periodicD1Good_sum_lower s a hi (ha i hi)]
        have hb : a i≤∑ j∈s,a j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        have hp := ha i hi
        omega

/-- Exact all-particle integer Dyson normalization, still written as the
actual complex polynomial Haar weight. Pairing directed factors into the
nonnegative squared Vandermonde is a separate algebraic identification. -/
theorem periodicD1GoodIntegral_constant (N m : ℕ) :
    periodicD1GoodIntegral (Finset.univ : Finset (Fin N)) (fun _ => m)=
      (((N*m).factorial:ℕ):ℂ)/((m.factorial:ℂ)^N) := by
  rw [periodicD1GoodIntegral_eq_multinomial]
  simp [periodicD1GoodMultinomial,Nat.mul_comm]

end DGRHS.Periodic
