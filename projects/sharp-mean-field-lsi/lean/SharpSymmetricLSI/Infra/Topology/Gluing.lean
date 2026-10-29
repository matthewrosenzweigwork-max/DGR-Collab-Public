import SharpSymmetricLSI.Infra.Topology.Pairs

/-!
# Gluing local homology classes along closed sets

For a subset `A` of a space `X` write `locH i A = Hᵢ(X, X ∖ A; 𝔽₂)`, and `restr` for the
restriction maps `Hᵢ(X, X ∖ B) ⟶ Hᵢ(X, X ∖ A)`, `A ⊆ B`.  The predicate `Good n A` collects the
three properties of Hatcher, *Algebraic Topology*, Lemma 3.27 (with `𝔽₂` coefficients):

* `Hᵢ(X, X ∖ A) = 0` for `i > n`;
* a class in `Hₙ(X, X ∖ A)` vanishing at every point of `A` is zero;
* some class in `Hₙ(X, X ∖ A)` is nonzero at every point of `A`.

The main result `Good.union` is the Mayer–Vietoris step of that lemma: for closed `A`, `B`,
`Good n A`, `Good n B` and `Good n (A ∩ B)` imply `Good n (A ∪ B)`.  Instead of a relative
Mayer–Vietoris sequence we chase the long exact sequences of the two triples
`(X, X ∖ A, X ∖ (A ∪ B))` and `(X, X ∖ (A ∩ B), X ∖ B)`, linked by the excision isomorphism
`Hᵢ(X ∖ A, X ∖ (A ∪ B)) ≅ Hᵢ(X ∖ (A ∩ B), X ∖ B)`.
-/

universe u

open CategoryTheory Set

namespace SharpLSI.Topology

variable {X : TopCat.{u}}

/-- The local homology `Hᵢ(X, X ∖ A; 𝔽₂)`. -/
noncomputable abbrev locH (i : ℕ) (A : Set X) : ModuleCat.{u} F2.{u} :=
  relH i (subset_univ Aᶜ)

/-- Restriction `Hᵢ(X, X ∖ B) ⟶ Hᵢ(X, X ∖ A)` for `A ⊆ B`. -/
noncomputable abbrev restr (i : ℕ) {A B : Set X} (h : A ⊆ B) : locH i B ⟶ locH i A :=
  relMap i (subset_univ Bᶜ) (subset_univ Aᶜ) (compl_subset_compl.mpr h) subset_rfl

lemma restr_restr (i : ℕ) {A B C : Set X} (hAB : A ⊆ B) (hBC : B ⊆ C) (α : locH i C) :
    restr i hAB (restr i hBC α) = restr i (hAB.trans hBC) α :=
  relMap_comp_apply i _ _ _ _ _ _ _ α

/-- The three properties of Hatcher's Lemma 3.27 for a set `A` in dimension `n`. -/
structure Good (n : ℕ) (A : Set X) : Prop where
  vanish : ∀ i, n < i → ∀ α : locH i A, α = 0
  inj : ∀ α : locH n A, (∀ x (hx : x ∈ A), restr n (singleton_subset_iff.2 hx) α = 0) → α = 0
  fund : ∃ α : locH n A, ∀ x (hx : x ∈ A), restr n (singleton_subset_iff.2 hx) α ≠ 0

section Chase

variable {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)

private lemma h₁ : (A ∪ B)ᶜ ⊆ Aᶜ := compl_subset_compl.mpr subset_union_left
private lemma h₂ : Bᶜ ⊆ (A ∩ B)ᶜ := compl_subset_compl.mpr inter_subset_right

include hA hB in
/-- The excision map `Hᵢ(X ∖ A, X ∖ (A ∪ B)) ⟶ Hᵢ(X ∖ (A ∩ B), X ∖ B)` is bijective. -/
private lemma bijective_exc (i : ℕ) :
    Function.Bijective (relMap i (h₁ (A := A) (B := B)) (h₂ (A := A) (B := B))
      (compl_subset_compl.mpr subset_union_right) (compl_subset_compl.mpr inter_subset_left)) := by
  refine bijective_relMap_excision i _ _ _ _ ?_ ?_ hA.isOpen_compl hB.isOpen_compl
  · rw [← compl_union]
  · rw [compl_inter]

include hA hB in
/-- A class of `Hᵢ(X, X ∖ (A ∪ B))` restricting to zero on `A` and on `B` is zero, provided
`Hᵢ₊₁(X, X ∖ (A ∩ B)) = 0`. -/
lemma eq_zero_of_restr_eq_zero (i : ℕ) (hAB : ∀ γ : locH (i + 1) (A ∩ B), γ = 0)
    (α : locH i (A ∪ B)) (hαA : restr i subset_union_left α = 0)
    (hαB : restr i subset_union_right α = 0) : α = 0 := by
  obtain ⟨β, hβ⟩ := triple_exact_total (h₁ (A := A) (B := B)) (subset_univ _) i α hαA
  have he := bijective_exc hA hB i
  have hj : relMap i (h₂ (A := A) (B := B)) ((h₂ (A := A) (B := B)).trans (subset_univ _))
      subset_rfl (subset_univ _)
      (relMap i (h₁ (A := A) (B := B)) (h₂ (A := A) (B := B))
        (compl_subset_compl.mpr subset_union_right)
        (compl_subset_compl.mpr inter_subset_left) β) = 0 := by
    rw [relMap_comp_apply, ← hαB, ← hβ, relMap_comp_apply]
  obtain ⟨γ, hγ⟩ := triple_exact_inner (h₂ (A := A) (B := B)) (subset_univ _) i _ hj
  rw [hAB γ, map_zero] at hγ
  have hβ0 : β = 0 := he.1 (hγ.symm.trans (map_zero _).symm)
  rw [← hβ, hβ0, map_zero]

include hA hB in
/-- Two classes on `A` and `B` agreeing on `A ∩ B` glue to a class on `A ∪ B`. -/
lemma exists_glue (n : ℕ) (αA : locH (n + 1) A) (αB : locH (n + 1) B)
    (h : restr (n + 1) inter_subset_left αA = restr (n + 1) inter_subset_right αB) :
    ∃ α : locH (n + 1) (A ∪ B),
      restr (n + 1) subset_union_left α = αA ∧ restr (n + 1) subset_union_right α = αB := by
  have he := bijective_exc hA hB
  -- The boundary of `αA` in `Hₙ(X ∖ A, X ∖ (A ∪ B))` vanishes.
  have hδ : tripleδ (h₁ (A := A) (B := B)) (subset_univ _) n αA = 0 := by
    apply (he n).1
    rw [map_zero, tripleδ_naturality (h₁ (A := A) (B := B)) (subset_univ _)
      (h₂ (A := A) (B := B)) (subset_univ _) n (compl_subset_compl.mpr subset_union_right)
      (compl_subset_compl.mpr inter_subset_left) subset_rfl]
    have : relMap (n + 1) (subset_univ Aᶜ) (subset_univ (A ∩ B)ᶜ)
        (compl_subset_compl.mpr inter_subset_left) subset_rfl αA =
        relMap (n + 1) ((h₂ (A := A) (B := B)).trans (subset_univ _)) (subset_univ _)
          (h₂ (A := A) (B := B)) subset_rfl αB := h
    rw [this, tripleδ_comp_zero]
  obtain ⟨α₀, hα₀⟩ := triple_exact_outer (h₁ (A := A) (B := B)) (subset_univ _) n αA hδ
  -- Correct `α₀` so that it also restricts to `αB`.
  set d : locH (n + 1) B := restr (n + 1) subset_union_right α₀ - αB with hd
  have hd0 : relMap (n + 1) ((h₂ (A := A) (B := B)).trans (subset_univ _)) (subset_univ _)
      (h₂ (A := A) (B := B)) subset_rfl d = 0 := by
    rw [hd, map_sub, sub_eq_zero]
    refine (relMap_comp_apply (n + 1) _ _ _ _ _ _ _ α₀).trans ?_
    refine Eq.trans ?_ h
    rw [← hα₀]
    exact (relMap_comp_apply (n + 1) _ _ _ _ _ _ _ α₀).symm
  obtain ⟨β', hβ'⟩ := triple_exact_total (h₂ (A := A) (B := B)) (subset_univ _) (n + 1) d hd0
  obtain ⟨β, rfl⟩ := (he (n + 1)).2 β'
  refine ⟨α₀ - relMap (n + 1) (h₁ (A := A) (B := B))
    ((h₁ (A := A) (B := B)).trans (subset_univ _)) subset_rfl (subset_univ _) β, ?_, ?_⟩
  · rw [map_sub, ← hα₀]
    have := triple_comp_zero (h₁ (A := A) (B := B)) (subset_univ _) (n + 1) β
    rw [sub_eq_self]
    exact this
  · rw [map_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', ← hd, ← hβ', relMap_comp_apply,
      relMap_comp_apply]

end Chase

/-- **Mayer–Vietoris step of Hatcher's Lemma 3.27.** -/
theorem Good.union {n : ℕ} (hn : 1 ≤ n)
    (hloc : ∀ x : X, ∀ α β : locH n ({x} : Set X), α ≠ 0 → β ≠ 0 → α = β)
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (gA : Good n A) (gB : Good n B) (gAB : Good n (A ∩ B)) : Good n (A ∪ B) where
  vanish i hi α :=
    eq_zero_of_restr_eq_zero hA hB i (gAB.vanish (i + 1) (by omega)) α
      (gA.vanish i hi _) (gB.vanish i hi _)
  inj α hα := by
    refine eq_zero_of_restr_eq_zero hA hB n (gAB.vanish (n + 1) (by omega)) α ?_ ?_
    · refine gA.inj _ fun x hx ↦ ?_
      rw [restr_restr]
      exact hα x (subset_union_left hx)
    · refine gB.inj _ fun x hx ↦ ?_
      rw [restr_restr]
      exact hα x (subset_union_right hx)
  fund := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨αA, hαA⟩ := gA.fund
    obtain ⟨αB, hαB⟩ := gB.fund
    have hagree : restr (m + 1) inter_subset_left αA = restr (m + 1) inter_subset_right αB := by
      rw [← sub_eq_zero]
      refine gAB.inj _ fun x hx ↦ ?_
      rw [map_sub, restr_restr, restr_restr, sub_eq_zero]
      exact hloc x _ _ (hαA x hx.1) (hαB x hx.2)
    obtain ⟨α, hα₁, hα₂⟩ := exists_glue hA hB m αA αB hagree
    refine ⟨α, fun x hx ↦ ?_⟩
    rcases hx with hx | hx
    · have := hαA x hx
      rwa [← hα₁, restr_restr] at this
    · have := hαB x hx
      rwa [← hα₂, restr_restr] at this

end SharpLSI.Topology

namespace SharpLSI.Topology

variable {X : TopCat.{u}}

/-- The relative homology of a pair `(t, t)` vanishes. -/
lemma relH_eq_zero_of_eq (i : ℕ) {s t : Set X} (h : s ⊆ t) (hst : s = t) (α : relH i h) :
    α = 0 := by
  subst hst
  have := triple_comp_zero h (subset_refl s) i α
  rwa [relMap_id_apply, relMap_id_apply] at this

/-- The empty set is `Good`. -/
lemma good_empty (n : ℕ) : Good n (∅ : Set X) where
  vanish i _ α := relH_eq_zero_of_eq i _ compl_empty α
  inj α _ := relH_eq_zero_of_eq n _ compl_empty α
  fund := ⟨0, fun _ hx ↦ hx.elim⟩

end SharpLSI.Topology
