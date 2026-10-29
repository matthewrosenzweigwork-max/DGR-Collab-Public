import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Defs.D17_Occupation

/-!
# Counting labellings with prescribed fibre sizes (Phase 3, lane D; R28)

`#{c : Fin N → L | #c⁻¹(ℓ) = k ℓ ∀ ℓ} · ∏ k_ℓ! = N!` when `∑ k_ℓ = N` (the multinomial count).
-/

noncomputable section
open Finset

namespace SharpLSI

section count
variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Labellings of `Fin N` with fibre sizes `k`. -/
def fibreLab (N : ℕ) (k : L → ℕ) : Finset (Fin N → L) :=
  univ.filter fun c => ∀ ℓ, #{i | c i = ℓ} = k ℓ

theorem card_fibre_cons {N : ℕ} (ℓ : L) (t : Fin N → L) (m : L) :
    #{i | (Fin.cons ℓ t : Fin (N + 1) → L) i = m} = (if ℓ = m then 1 else 0) + #{i | t i = m} := by
  rw [Fin.card_filter_univ_succ']
  simp

theorem card_fibreLab_succ (N : ℕ) (k : L → ℕ) :
    #(fibreLab (N + 1) k) = ∑ ℓ, if 1 ≤ k ℓ then #(fibreLab N (Function.update k ℓ (k ℓ - 1)))
      else 0 := by
  rw [card_eq_sum_card_fiberwise (f := fun c : Fin (N + 1) → L => c 0) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun ℓ _ => ?_
  split_ifs with hk
  · refine card_bij (fun c _ => Fin.tail c) ?_ ?_ ?_
    · intro c hc
      simp only [fibreLab, mem_filter, mem_univ, true_and] at hc ⊢
      intro m
      have h := hc.1 m
      rw [← Fin.cons_self_tail c, card_fibre_cons, hc.2] at h
      by_cases hm : m = ℓ
      · subst hm; simp only [ite_true] at h; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hm]; simp only [Ne.symm hm, ite_false] at h; omega
    · intro c₁ h₁ c₂ h₂ he
      simp only [mem_filter] at h₁ h₂
      rw [← Fin.cons_self_tail c₁, ← Fin.cons_self_tail c₂, he, h₁.2, h₂.2]
    · intro t ht
      refine ⟨Fin.cons ℓ t, ?_, Fin.tail_cons _ _⟩
      simp only [fibreLab, mem_filter, mem_univ, true_and, Fin.cons_zero, and_true] at ht ⊢
      intro m
      rw [card_fibre_cons, ht m]
      by_cases hm : ℓ = m
      · subst hm; rw [Function.update_self]; simp; omega
      · rw [Function.update_of_ne (Ne.symm hm)]; simp [hm]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro c hc
    simp only [fibreLab, mem_filter, mem_univ, true_and] at hc
    intro h0
    have h := hc ℓ
    rw [← Fin.cons_self_tail c, card_fibre_cons, h0] at h
    simp at h; omega

/-- **The multinomial count.** -/
theorem card_fibreLab_mul (N : ℕ) (k : L → ℕ) (hk : ∑ ℓ, k ℓ = N) :
    #(fibreLab N k) * ∏ ℓ, (k ℓ).factorial = N.factorial := by
  induction N generalizing k with
  | zero =>
    have hk0 : ∀ ℓ, k ℓ = 0 := fun ℓ => by
      have := single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (mem_univ ℓ); omega
    have : fibreLab 0 k = univ := by
      ext c; simp [fibreLab, hk0]
    simp [this, hk0]
  | succ N ih =>
    rw [card_fibreLab_succ, sum_mul]
    have hterm : ∀ ℓ, (if 1 ≤ k ℓ then #(fibreLab N (Function.update k ℓ (k ℓ - 1))) else 0) *
        ∏ m, (k m).factorial = k ℓ * N.factorial := by
      intro ℓ
      split_ifs with h
      · have hs : ∑ m, Function.update k ℓ (k ℓ - 1) m = N := by
          have := sum_update_of_mem (mem_univ ℓ) k (k ℓ - 1)
          rw [this]
          have h2 := add_sum_erase univ k (mem_univ ℓ)
          rw [sdiff_singleton_eq_erase]; omega
        have hi := ih _ hs
        have hp : ∏ m, (k m).factorial =
            k ℓ * ∏ m, (Function.update k ℓ (k ℓ - 1) m).factorial := by
          rw [← mul_prod_erase univ _ (mem_univ ℓ), ← mul_prod_erase univ
            (fun m => (Function.update k ℓ (k ℓ - 1) m).factorial) (mem_univ ℓ)]
          rw [Function.update_self]
          have he : ∏ m ∈ univ.erase ℓ, (Function.update k ℓ (k ℓ - 1) m).factorial =
              ∏ m ∈ univ.erase ℓ, (k m).factorial :=
            prod_congr rfl fun m hm => by rw [Function.update_of_ne (ne_of_mem_erase hm)]
          rw [he, ← mul_assoc]
          congr 1
          obtain ⟨j, hj⟩ : ∃ j, k ℓ = j + 1 := ⟨k ℓ - 1, by omega⟩
          rw [hj, Nat.factorial_succ]; simp
        rw [hp, mul_left_comm, hi]
      · have : k ℓ = 0 := by omega
        simp [this]
    rw [sum_congr rfl fun ℓ _ => hterm ℓ, ← sum_mul, hk, Nat.factorial_succ]

end count


section occ

theorem support_lt (α : ℕ →₀ ℕ) {n : ℕ} (hn : n ∈ α.support) : n < α.support.sup id + 1 :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)

theorem eq_zero_of_gt (α : ℕ →₀ ℕ) {n : ℕ} (hn : α.support.sup id < n) : α n = 0 := by
  by_contra h
  have := support_lt α (Finsupp.mem_support_iff.mpr h)
  omega

theorem occSize_eq_sum_range (α : ℕ →₀ ℕ) :
    occSize α = ∑ n ∈ Finset.range (α.support.sup id + 1), α n := by
  unfold occSize Finsupp.sum
  refine Finset.sum_subset (fun n hn => Finset.mem_range.mpr (support_lt α hn)) fun n _ hn => ?_
  simpa using hn

theorem occFactorial_eq_prod_range (α : ℕ →₀ ℕ) :
    occFactorial α = ∏ n ∈ Finset.range (α.support.sup id + 1), (α n).factorial := by
  unfold occFactorial Finsupp.prod
  refine Finset.prod_subset (fun n hn => Finset.mem_range.mpr (support_lt α hn)) fun n _ hn => ?_
  have : α n = 0 := by simpa using hn
  simp [this]

/-- The fibre sizes of the labellings of (7.1). -/
def occFibre (α : ℕ →₀ ℕ) (N : ℕ) (ℓ : Fin (α.support.sup id + 2)) : ℕ :=
  if (ℓ : ℕ) = 0 then N - occSize α else α ((ℓ : ℕ) - 1)

theorem sum_occFibre (α : ℕ →₀ ℕ) {N : ℕ} (hq : occSize α ≤ N) :
    ∑ ℓ, occFibre α N ℓ = N := by
  rw [Fin.sum_univ_succ]
  simp only [occFibre, Fin.val_zero, ite_true, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
    Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun n => α n), ← occSize_eq_sum_range]
  omega

theorem occLabellings_eq (α : ℕ →₀ ℕ) {N : ℕ} (hq : occSize α ≤ N) :
    occLabellings α N = fibreLab N (occFibre α N) := by
  ext c
  simp only [occLabellings, fibreLab, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h ℓ
    by_cases hℓ : (ℓ : ℕ) = 0
    · -- the label `0` carries the remaining `N - q` points
      have htot : ∑ m, #{i | c i = m} = N := by
        rw [← Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)]
        simp
      rw [Fin.sum_univ_succ] at htot
      have hrest : ∑ m : Fin (α.support.sup id + 1), #{i | c i = m.succ} = occSize α := by
        rw [occSize_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun n => α n)]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← h m]
        exact congrArg Finset.card (Finset.filter_congr fun i _ => by
          rw [Fin.ext_iff, Fin.val_succ])
      have h0 : ℓ = 0 := Fin.ext hℓ
      subst h0
      simp only [occFibre, Fin.val_zero, ite_true]
      omega
    · obtain ⟨n, hn⟩ : ∃ n, (ℓ : ℕ) = n + 1 := ⟨(ℓ : ℕ) - 1, by omega⟩
      simp only [occFibre, hℓ, ite_false, hn, Nat.add_sub_cancel]
      rw [← h n]
      exact congrArg Finset.card (Finset.filter_congr fun i _ => by rw [Fin.ext_iff, hn])
  · intro h n
    by_cases hn : n + 1 < α.support.sup id + 2
    · have := h ⟨n + 1, hn⟩
      simp only [occFibre, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at this
      rw [← this]
      exact congrArg Finset.card (Finset.filter_congr fun i _ => by rw [Fin.ext_iff])
    · rw [eq_zero_of_gt α (by omega)]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      have := (c i).2
      omega

/-- **`#labellings · α! = (N)_q`.** -/
theorem card_occLabellings (α : ℕ →₀ ℕ) {N : ℕ} (hq : occSize α ≤ N) :
    #(occLabellings α N) * occFactorial α = N.descFactorial (occSize α) := by
  have h := card_fibreLab_mul N (occFibre α N) (sum_occFibre α hq)
  rw [← occLabellings_eq α hq, Fin.prod_univ_succ] at h
  simp only [occFibre, Fin.val_zero, ite_true, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
    Nat.add_sub_cancel] at h
  rw [Fin.prod_univ_eq_prod_range (fun n => (α n).factorial), ← occFactorial_eq_prod_range] at h
  have h2 := Nat.factorial_mul_descFactorial hq
  have hpos : 0 < (N - occSize α).factorial := Nat.factorial_pos _
  have : #(occLabellings α N) * occFactorial α * (N - occSize α).factorial =
      N.descFactorial (occSize α) * (N - occSize α).factorial := by
    rw [mul_comm (N.descFactorial _), h2, ← h]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end occ

end SharpLSI
