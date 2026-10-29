import SharpSymmetricLSI.Infra.Topology.Gluing

/-!
# Transporting `Good` along a homeomorphism of open sets

Let `h : U ≃ₜ V` be a homeomorphism between open subsets of spaces `X` and `Y`, and let `A ⊆ U`,
`B ⊆ Y` be closed sets which correspond under `h` (`u ∈ A ↔ h u ∈ B`, with `B ⊆ V`).  By excision
`Hᵢ(X, X ∖ A) ≅ Hᵢ(U, U ∖ A)`, `h` induces `Hᵢ(U, U ∖ A) ≅ Hᵢ(V, V ∖ B)`, and by excision again
`Hᵢ(V, V ∖ B) ≅ Hᵢ(Y, Y ∖ B)`.  These isomorphisms commute with restriction to points, so
`Good n B` implies `Good n A` (`Good.of_homeomorph`), and the local homology groups at
corresponding points have the same "any two nonzero elements agree" property
(`locH_point_eq_of_homeomorph`).  This is step (3) of Hatcher's proof of Lemma 3.27: reduction
to a chart.
-/

universe u

open CategoryTheory Set

namespace SharpLSI.Topology

section Excision

variable {X : TopCat.{u}} {W : Set X}

/-- The excision map `Hᵢ(W, W ∖ C) ⟶ Hᵢ(X, X ∖ C)`. -/
noncomputable abbrev excMap (i : ℕ) (W C : Set X) : relH i (inter_subset_left : W ∩ Cᶜ ⊆ W) ⟶ locH i C :=
  relMap i inter_subset_left (subset_univ Cᶜ) inter_subset_right (subset_univ W)

lemma bijective_excMap (i : ℕ) (hW : IsOpen W) {C : Set X} (hC : IsClosed C) (hCW : C ⊆ W) :
    Function.Bijective (excMap i W C) :=
  bijective_relMap_excision i _ _ _ _ subset_rfl
    (fun x _ ↦ (em (x ∈ W)).elim Or.inl fun h ↦ Or.inr fun hx ↦ h (hCW hx)) hW hC.isOpen_compl

/-- The restriction `Hᵢ(W, W ∖ C) ⟶ Hᵢ(W, W ∖ C')` for `C' ⊆ C`. -/
noncomputable abbrev wRestr (i : ℕ) (W : Set X) {C C' : Set X} (h : C' ⊆ C) :
    relH i (inter_subset_left : W ∩ Cᶜ ⊆ W) ⟶ relH i (inter_subset_left : W ∩ C'ᶜ ⊆ W) :=
  relMap i inter_subset_left inter_subset_left
    (inter_subset_inter_right _ (compl_subset_compl.2 h)) subset_rfl

lemma restr_excMap (i : ℕ) {C C' : Set X} (h : C' ⊆ C) (α : relH i (inter_subset_left : W ∩ Cᶜ ⊆ W)) :
    restr i h (excMap i W C α) = excMap i W C' (wRestr i W h α) := by
  rw [relMap_comp_apply, relMap_comp_apply]

end Excision

section Homeomorph

variable {X Y : TopCat.{u}} {U : Set X} {V : Set Y} (h : U ≃ₜ V)

lemma homeo_mem_iff {A : Set X} {B : Set Y} (hAB : ∀ u : U, (u : X) ∈ A ↔ (h u : Y) ∈ B)
    (v : V) : (h.symm v : X) ∈ A ↔ (v : Y) ∈ B := by
  rw [hAB, h.apply_symm_apply]

/-- The map of pairs `(U, U ∖ A) ⟶ (V, V ∖ B)` induced by `h`. -/
noncomputable def homeoPairMap {A : Set X} {B : Set Y}
    (hAB : ∀ u : U, (u : X) ∈ A ↔ (h u : Y) ∈ B) :
    TopPair.ofInclusion (inter_subset_left : U ∩ Aᶜ ⊆ U) ⟶
      TopPair.ofInclusion (inter_subset_left : V ∩ Bᶜ ⊆ V) :=
  TopPair.ofHom (TopCat.ofHom ⟨h, h.continuous⟩)
    (TopCat.ofHom ⟨fun y ↦ ⟨(h ⟨y.1, y.2.1⟩ : Y), (h ⟨y.1, y.2.1⟩).2,
        fun hy ↦ y.2.2 ((hAB _).2 hy)⟩,
      Continuous.subtype_mk (continuous_subtype_val.comp (h.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val fun y ↦ y.2.1))) fun y ↦
          ⟨(h ⟨y.1, y.2.1⟩).2, fun hy ↦ y.2.2 ((hAB _).2 hy)⟩⟩)
    (by ext; rfl)

lemma bijective_homeoPairMap (i : ℕ) {A : Set X} {B : Set Y}
    (hAB : ∀ u : U, (u : X) ∈ A ↔ (h u : Y) ∈ B) :
    Function.Bijective (TopPair.singularHomologyMap (homeoPairMap h hAB) R2 i) := by
  let g := homeoPairMap h.symm (A := B) (B := A) fun v ↦ (homeo_mem_iff h hAB v).symm
  have h₁ : homeoPairMap h hAB ≫ g = 𝟙 _ := by
    ext y : 2
    · apply Subtype.ext
      show ((h.symm (h ⟨y.1, y.2.1⟩) : U) : X) = y.1
      rw [h.symm_apply_apply]
    · show h.symm (h y) = y
      exact h.symm_apply_apply y
  have h₂ : g ≫ homeoPairMap h hAB = 𝟙 _ := by
    ext y : 2
    · apply Subtype.ext
      show ((h (h.symm ⟨y.1, y.2.1⟩) : V) : Y) = y.1
      rw [h.apply_symm_apply]
    · show h (h.symm y) = y
      exact h.apply_symm_apply y
  have e₁ := congrArg (fun f ↦ TopPair.singularHomologyMap f R2 i) h₁
  have e₂ := congrArg (fun f ↦ TopPair.singularHomologyMap f R2 i) h₂
  simp only [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_id] at e₁ e₂
  constructor
  · intro a b hab
    have := congrArg (TopPair.singularHomologyMap g R2 i) hab
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, e₁] at this
  · intro b
    refine ⟨TopPair.singularHomologyMap g R2 i b, ?_⟩
    rw [← ConcreteCategory.comp_apply, e₂]
    rfl

/-- Naturality of `homeoPairMap` with respect to restriction. -/
lemma homeoPairMap_wRestr (i : ℕ) {A A' : Set X} {B B' : Set Y}
    (hAB : ∀ u : U, (u : X) ∈ A ↔ (h u : Y) ∈ B) (hAB' : ∀ u : U, (u : X) ∈ A' ↔ (h u : Y) ∈ B')
    (hA : A' ⊆ A) (hB : B' ⊆ B) (α : relH i (inter_subset_left : U ∩ Aᶜ ⊆ U)) :
    wRestr i V hB (TopPair.singularHomologyMap (homeoPairMap h hAB) R2 i α) =
      TopPair.singularHomologyMap (homeoPairMap h hAB') R2 i (wRestr i U hA α) := by
  have : homeoPairMap h hAB ≫ pairMap inter_subset_left inter_subset_left
      (inter_subset_inter_right _ (compl_subset_compl.2 hB)) subset_rfl =
      pairMap inter_subset_left inter_subset_left
        (inter_subset_inter_right _ (compl_subset_compl.2 hA)) subset_rfl ≫
        homeoPairMap h hAB' := by
    ext : 2 <;> rfl
  have e := congrArg (fun f ↦ TopPair.singularHomologyMap f R2 i) this
  simp only [TopPair.singularHomologyMap_comp] at e
  exact ConcreteCategory.congr_hom e α

variable (hU : IsOpen U) (hV : IsOpen V)
include hU hV

/-- **Transport of `Good` to a chart.** -/
theorem Good.of_homeomorph {n : ℕ} {A : Set X} {B : Set Y} (hAU : A ⊆ U) (hBV : B ⊆ V)
    (hA : IsClosed A) (hB : IsClosed B) (hX1 : ∀ x : X, IsClosed ({x} : Set X))
    (hAB : ∀ u : U, (u : X) ∈ A ↔ (h u : Y) ∈ B) (g : Good n B) : Good n A := by
  -- Points of `A` correspond to points of `B`.
  have hpt (x : X) (hx : x ∈ U) : ∀ u : U, (u : X) ∈ ({x} : Set X) ↔
      (h u : Y) ∈ ({(h ⟨x, hx⟩ : Y)} : Set Y) := by
    intro u
    simp only [mem_singleton_iff]
    constructor
    · rintro rfl; rfl
    · intro hu
      exact congrArg Subtype.val (h.injective (Subtype.ext hu))
  have hhB (x : X) (hxA : x ∈ A) : (h ⟨x, hAU hxA⟩ : Y) ∈ B := (hAB _).1 hxA
  refine ⟨fun i hi α ↦ ?_, fun α hα ↦ ?_, ?_⟩
  · obtain ⟨α', rfl⟩ := (bijective_excMap i hU hA hAU).2 α
    suffices α' = 0 by rw [this, map_zero]
    refine (bijective_homeoPairMap h i hAB).1 ((bijective_excMap i hV hB hBV).1 ?_)
    rw [map_zero, map_zero]
    exact g.vanish i hi _
  · obtain ⟨α', rfl⟩ := (bijective_excMap n hU hA hAU).2 α
    suffices α' = 0 by rw [this, map_zero]
    refine (bijective_homeoPairMap h n hAB).1 ((bijective_excMap n hV hB hBV).1 ?_)
    rw [map_zero, map_zero]
    refine g.inj _ fun y hy ↦ ?_
    obtain ⟨⟨x, hxU⟩, hxy⟩ := h.surjective ⟨y, hBV hy⟩
    have hyx : y = (h ⟨x, hxU⟩ : Y) := (congrArg Subtype.val hxy).symm
    subst hyx
    have hxA : x ∈ A := (hAB _).2 hy
    have hx := hα x hxA
    rw [restr_excMap] at hx ⊢
    have h0 : wRestr n U (singleton_subset_iff.2 hxA) α' = 0 :=
      (bijective_excMap n hU (hX1 x) (singleton_subset_iff.2 (hAU hxA))).1
        (hx.trans (map_zero _).symm)
    rw [homeoPairMap_wRestr h n hAB (hpt x hxU) (singleton_subset_iff.2 hxA)
      (singleton_subset_iff.2 hy), h0, map_zero, map_zero]
  · obtain ⟨β, hβ⟩ := g.fund
    obtain ⟨β', rfl⟩ := (bijective_excMap n hV hB hBV).2 β
    obtain ⟨α', rfl⟩ := (bijective_homeoPairMap h n hAB).2 β'
    refine ⟨excMap n U A α', fun x hxA hx ↦ hβ _ (hhB x hxA) ?_⟩
    rw [restr_excMap] at hx ⊢
    have h0 : wRestr n U (singleton_subset_iff.2 hxA) α' = 0 :=
      (bijective_excMap n hU (hX1 x) (singleton_subset_iff.2 (hAU hxA))).1
        (hx.trans (map_zero _).symm)
    rw [homeoPairMap_wRestr h n hAB (hpt x (hAU hxA)) (singleton_subset_iff.2 hxA)
      (singleton_subset_iff.2 (hhB x hxA)), h0, map_zero, map_zero]

/-- Transport of the "two nonzero local classes agree" property to a chart. -/
theorem locH_point_eq_of_homeomorph {n : ℕ} (hX1 : ∀ x : X, IsClosed ({x} : Set X))
    (hY1 : ∀ y : Y, IsClosed ({y} : Set Y)) {x : X} (hx : x ∈ U)
    (hloc : ∀ α β : locH n ({(h ⟨x, hx⟩ : Y)} : Set Y), α ≠ 0 → β ≠ 0 → α = β)
    (α β : locH n ({x} : Set X)) (hα : α ≠ 0) (hβ : β ≠ 0) : α = β := by
  have hpt : ∀ u : U, (u : X) ∈ ({x} : Set X) ↔ (h u : Y) ∈ ({(h ⟨x, hx⟩ : Y)} : Set Y) := by
    intro u
    simp only [mem_singleton_iff]
    constructor
    · rintro rfl; rfl
    · intro hu
      exact congrArg Subtype.val (h.injective (Subtype.ext hu))
  have hxU : ({x} : Set X) ⊆ U := singleton_subset_iff.2 hx
  have hyV : ({(h ⟨x, hx⟩ : Y)} : Set Y) ⊆ V := singleton_subset_iff.2 (h ⟨x, hx⟩).2
  let T := fun γ ↦ excMap n V _ (TopPair.singularHomologyMap (homeoPairMap h hpt) R2 n γ)
  have hT : Function.Bijective T :=
    (bijective_excMap n hV (hY1 _) hyV).comp (bijective_homeoPairMap h n hpt)
  have hT0 : T 0 = 0 := by simp only [T, map_zero]
  obtain ⟨α', rfl⟩ := (bijective_excMap n hU (hX1 x) hxU).2 α
  obtain ⟨β', rfl⟩ := (bijective_excMap n hU (hX1 x) hxU).2 β
  have hα' : T α' ≠ 0 := fun h0 ↦ hα (by
    rw [hT.1 (h0.trans hT0.symm), map_zero])
  have hβ' : T β' ≠ 0 := fun h0 ↦ hβ (by
    rw [hT.1 (h0.trans hT0.symm), map_zero])
  rw [hT.1 (hloc _ _ hα' hβ')]

end Homeomorph

end SharpLSI.Topology
