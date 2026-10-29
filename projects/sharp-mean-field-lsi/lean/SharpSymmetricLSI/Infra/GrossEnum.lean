import Mathlib

/-!
# Enumerating an infinite type increasingly along a function with finite sublevel sets

If `α` is infinite and every sublevel set `{x | f x ≤ L}` of `f : α → ℝ` is finite, there is a
bijection `e : ℕ ≃ α` with `f ∘ e` monotone (`exists_equiv_monotone`). Ties are broken by an
injection into `ℕ`; the enumeration is the rank `#{y | key y < key x}`.
-/

open Set

namespace SharpLSI

section enum
variable {α : Type*} (f : α → ℝ) (hfin : ∀ L, {x | f x ≤ L}.Finite)
include hfin

theorem countable_of_finite_sublevel : Countable α := by
  have : (univ : Set α) = ⋃ n : ℕ, {x | f x ≤ n} := by
    ext x; simp only [mem_univ, mem_iUnion, mem_setOf_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge (f x); exact ⟨n, hn⟩
  have hc : (univ : Set α).Countable := by
    rw [this]; exact countable_iUnion fun n => (hfin n).countable
  exact countable_univ_iff.1 hc

variable [Infinite α]

theorem exists_equiv_monotone : ∃ e : ℕ ≃ α, Monotone (f ∘ e) := by
  have := countable_of_finite_sublevel f hfin
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat α
  -- the strict total order by `(f, g)`
  let lt : α → α → Prop := fun x y => f x < f y ∨ (f x = f y ∧ g x < g y)
  have lt_trans : ∀ {x y z}, lt x y → lt y z → lt x z := by
    intro x y z h1 h2
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (h2 ▸ h1)
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩
  have lt_irrefl : ∀ x, ¬ lt x x := fun x h => by
    rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
  have lt_total : ∀ x y, x ≠ y → lt x y ∨ lt y x := by
    intro x y hxy
    rcases lt_trichotomy (f x) (f y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy (g x) (g y) with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact absurd (hg h') hxy
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)
  have lt_le : ∀ {x y}, lt x y → f x ≤ f y := fun {x y} h => by
    rcases h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  -- the rank
  let below : α → Set α := fun x => {y | lt y x}
  have below_fin : ∀ x, (below x).Finite := fun x =>
    (hfin (f x)).subset fun y hy => lt_le hy
  let r : α → ℕ := fun x => (below x).ncard
  have r_lt : ∀ {x y}, lt x y → r x < r y := by
    intro x y hxy
    refine ncard_lt_ncard ?_ (below_fin y)
    refine ssubset_iff_subset_ne.2 ⟨fun z hz => lt_trans hz hxy, fun h => ?_⟩
    have : x ∈ below y := hxy
    rw [← h] at this
    exact lt_irrefl x this
  have r_inj : Function.Injective r := by
    intro x y h
    by_contra hxy
    rcases lt_total x y hxy with h' | h'
    · exact absurd h (r_lt h').ne
    · exact absurd h (r_lt h').ne'
  -- downward closed image
  have r_down : ∀ x m, r x = m + 1 → ∃ z, r z = m := by
    intro x m hx
    have hne : (below x).Nonempty := by
      rw [← ncard_pos (below_fin x)]; simp only [r] at hx; omega
    obtain ⟨z, hz, hmax⟩ := Set.exists_max_image (below x) r (below_fin x) hne
    refine ⟨z, ?_⟩
    have hset : below z = below x \ {z} := by
      ext y
      simp only [below, mem_setOf_eq, mem_diff, mem_singleton_iff]
      constructor
      · intro hy
        exact ⟨lt_trans hy hz, fun h => lt_irrefl z (h ▸ hy)⟩
      · rintro ⟨hy, hyz⟩
        rcases lt_total y z hyz with h | h
        · exact h
        · exact absurd (hmax y hy) (not_le.2 (r_lt h))
    show (below z).ncard = m
    rw [hset, ncard_sdiff_singleton_of_mem hz]
    simp only [r] at hx; omega
  have r_surj : Function.Surjective r := by
    intro n
    obtain ⟨m, ⟨x, rfl⟩, hm⟩ := (Set.infinite_range_of_injective r_inj).exists_gt n
    have key : ∀ k x, r x = n + k → ∃ y, r y = n := by
      intro k
      induction k with
      | zero => exact fun x hx => ⟨x, hx⟩
      | succ k ih =>
        intro x hx
        obtain ⟨z, hz⟩ := r_down x (n + k) (by rw [hx]; ring)
        exact ih z hz
    exact key (r x - n) x (by omega)
  let e : ℕ ≃ α := (Equiv.ofBijective r ⟨r_inj, r_surj⟩).symm
  have he : ∀ n, r (e n) = n := fun n => (Equiv.ofBijective r ⟨r_inj, r_surj⟩).apply_symm_apply n
  refine ⟨e, fun n m hnm => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have := r_lt (Or.inl hlt : lt (e m) (e n))
  rw [he, he] at this
  omega

end enum

end SharpLSI
