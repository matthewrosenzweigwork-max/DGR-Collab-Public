import Mathlib

/-!
# Proposition 3.2: counting lemmas for sums over the labels other than `i`
-/

open scoped BigOperators

namespace SharpLSI.FL

theorem sum_fiber_finset {N q : ℕ} (E : Finset (Fin N)) (a : Fin N → Fin q) (g : Fin q → ℝ) :
    ∑ j ∈ E, g (a j) = ∑ t, ((E.filter fun j => a j = t).card : ℝ) * g t := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := E) (t := Finset.univ) (g := a)
    (fun j _ => Finset.mem_univ _) (fun j => g (a j))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g t) (fun j hj => by
    rw [(Finset.mem_filter.1 hj).2]), Finset.sum_const, nsmul_eq_mul]

theorem card_erase_fiber {N q : ℕ} (a : Fin N → Fin q) (n : Fin q → ℕ)
    (hfib : ∀ s, (Finset.univ.filter fun i => a i = s).card = n s) (i : Fin N) (t : Fin q) :
    (((Finset.univ.erase i).filter fun j => a j = t).card : ℝ) =
      (n t : ℝ) - (if a i = t then 1 else 0) := by
  have h : (Finset.univ.erase i).filter (fun j => a j = t) =
      (Finset.univ.filter fun j => a j = t).erase i := by
    ext j; simp [and_comm]
  rw [h]
  by_cases hit : a i = t
  · rw [Finset.card_erase_of_mem (by simp [hit]), hfib t, if_pos hit]
    have : 1 ≤ n t := by
      rw [← hfib t]; exact Finset.card_pos.2 ⟨i, by simp [hit]⟩
    push_cast [Nat.cast_sub this]; ring
  · rw [Finset.erase_eq_of_notMem (by simp [hit]), hfib t, if_neg hit]; ring


theorem sum_erase_pairs {N q : ℕ} (E : Finset (Fin N)) (a : Fin N → Fin q)
    (H : Fin q → Fin q → ℝ) :
    ∑ j ∈ E, ∑ l ∈ E.erase j, H (a j) (a l) =
      ∑ t, ∑ u, ((E.filter fun j => a j = t).card : ℝ) * ((E.filter fun j => a j = u).card : ℝ) *
        H t u - ∑ t, ((E.filter fun j => a j = t).card : ℝ) * H t t := by
  have h1 : ∀ j ∈ E, ∑ l ∈ E.erase j, H (a j) (a l) = ∑ l ∈ E, H (a j) (a l) - H (a j) (a j) :=
    fun j hj => by
      rw [← Finset.add_sum_erase _ _ hj]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  have h2 : ∀ j, ∑ l ∈ E, H (a j) (a l) =
      ∑ u, ((E.filter fun l => a l = u).card : ℝ) * H (a j) u := fun j =>
    sum_fiber_finset E a (fun u => H (a j) u)
  simp_rw [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ u, ∑ j ∈ E, ((E.filter fun l => a l = u).card : ℝ) * H (a j) u =
      ∑ t, ((E.filter fun j => a j = t).card : ℝ) *
        (((E.filter fun l => a l = u).card : ℝ) * H t u) := fun u =>
    sum_fiber_finset E a (fun t => ((E.filter fun l => a l = u).card : ℝ) * H t u)
  simp_rw [h3]
  rw [sum_fiber_finset E a (fun t => H t t), Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring

end SharpLSI.FL
