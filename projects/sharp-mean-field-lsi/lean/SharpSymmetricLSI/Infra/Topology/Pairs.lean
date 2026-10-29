import SharpSymmetricLSI.Vendor.TauCeti.AlgebraicTopology.Singular.Excision
import SharpSymmetricLSI.Vendor.TauCeti.AlgebraicTopology.Singular.Triple
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Data.ZMod.Basic

/-!
# Relative singular homology of nested subsets, with `𝔽₂` coefficients

For subsets `s ⊆ t` of a topological space `X` we write `relH i h` (with `h : s ⊆ t`) for the
relative singular homology `Hᵢ(t, s; 𝔽₂)`, and `relMap` for the map induced by an inclusion of
pairs `(t, s) ⟶ (t', s')`.  We record functoriality, the long exact sequence of a triple
`s ⊆ t ⊆ u` in element form, naturality of its connecting morphism, and excision in the form
`(t, t ∩ s') ⟶ (t ∪ s', s')` for open `t` and `s'`.

All of this is a thin layer over the vendored Tau Ceti library
(`SharpSymmetricLSI.Vendor.TauCeti`).
-/

universe u

open CategoryTheory Limits Topology

namespace SharpLSI.Topology

/-- The field `𝔽₂`, lifted to universe `u`. -/
abbrev F2 : Type u := ULift.{u} (ZMod 2)

/-- `𝔽₂` as a module over itself: the coefficients of all homology groups below. -/
noncomputable abbrev R2 : ModuleCat.{u} F2.{u} := ModuleCat.of F2 F2

/-- Cached so that later files with more instances in scope find it immediately. -/
instance hasCoproducts_R2 : HasCoproducts.{u} (ModuleCat.{u} F2.{u}) := inferInstance

section Pairs

variable {X : TopCat.{u}}

/-- Relative singular homology `Hᵢ(t, s; 𝔽₂)` of nested subsets `s ⊆ t` of `X`. -/
noncomputable abbrev relH (i : ℕ) {s t : Set X} (h : s ⊆ t) : ModuleCat.{u} F2.{u} :=
  (TopPair.ofInclusion h).singularHomology R2 i

/-- The map of pairs `(t, s) ⟶ (t', s')` given by inclusions. -/
abbrev pairMap {s t s' t' : Set X} (h : s ⊆ t) (h' : s' ⊆ t') (hs : s ⊆ s') (ht : t ⊆ t') :
    TopPair.ofInclusion h ⟶ TopPair.ofInclusion h' :=
  TopPair.ofInclusionMap h h' (ContinuousMap.inclusion ht) (fun _ hx ↦ hs hx)

lemma pairMap_comp {s t s' t' s'' t'' : Set X} (h : s ⊆ t) (h' : s' ⊆ t') (h'' : s'' ⊆ t'')
    (hs : s ⊆ s') (ht : t ⊆ t') (hs' : s' ⊆ s'') (ht' : t' ⊆ t'') :
    pairMap h h' hs ht ≫ pairMap h' h'' hs' ht' =
      pairMap h h'' (hs.trans hs') (ht.trans ht') := by
  ext : 2 <;> rfl

lemma pairMap_id {s t : Set X} (h : s ⊆ t) :
    pairMap h h subset_rfl subset_rfl = 𝟙 _ := by
  ext : 2 <;> rfl

/-- The map on relative homology induced by an inclusion of pairs. -/
noncomputable abbrev relMap (i : ℕ) {s t s' t' : Set X} (h : s ⊆ t) (h' : s' ⊆ t')
    (hs : s ⊆ s') (ht : t ⊆ t') : relH i h ⟶ relH i h' :=
  TopPair.singularHomologyMap (pairMap h h' hs ht) R2 i

lemma relMap_comp_apply (i : ℕ) {s t s' t' s'' t'' : Set X} (h : s ⊆ t) (h' : s' ⊆ t')
    (h'' : s'' ⊆ t'') (hs : s ⊆ s') (ht : t ⊆ t') (hs' : s' ⊆ s'') (ht' : t' ⊆ t'')
    (x : relH i h) :
    relMap i h' h'' hs' ht' (relMap i h h' hs ht x) =
      relMap i h h'' (hs.trans hs') (ht.trans ht') x := by
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp, pairMap_comp]

lemma relMap_id_apply (i : ℕ) {s t : Set X} (h : s ⊆ t) (hs : s ⊆ s) (ht : t ⊆ t)
    (x : relH i h) : relMap i h h hs ht x = x := by
  rw [relMap, pairMap_id, TopPair.singularHomologyMap_id]
  rfl

end Pairs

section Triples

variable {X : TopCat.{u}} {s t v : Set X} (hst : s ⊆ t) (htv : t ⊆ v)

/-- The triple `(v, t, s)` of nested subsets. -/
abbrev triple : TauCeti.TopTriple.{u} := TauCeti.TopTriple.ofInclusions hst htv

lemma innerToTotal_triple :
    TauCeti.TopTriple.innerToTotal.app (triple hst htv) =
      pairMap hst (hst.trans htv) subset_rfl htv := by
  ext : 2 <;> rfl

lemma totalToOuter_triple :
    TauCeti.TopTriple.totalToOuter.app (triple hst htv) =
      pairMap (hst.trans htv) htv hst subset_rfl := by
  ext : 2 <;> rfl

lemma map_innerToTotal_triple (n : ℕ) :
    TopPair.singularHomologyMap (TauCeti.TopTriple.innerToTotal.app (triple hst htv)) R2 n =
      relMap n hst (hst.trans htv) subset_rfl htv := by
  rw [innerToTotal_triple]; rfl

lemma map_totalToOuter_triple (n : ℕ) :
    TopPair.singularHomologyMap (TauCeti.TopTriple.totalToOuter.app (triple hst htv)) R2 n =
      relMap n (hst.trans htv) htv hst subset_rfl := by
  rw [totalToOuter_triple]; rfl

/-- The connecting morphism `Hₙ₊₁(v, t) ⟶ Hₙ(t, s)` of the triple `(v, t, s)`. -/
noncomputable def tripleδ (n : ℕ) : relH (n + 1) htv ⟶ relH n hst :=
  TauCeti.TopTriple.singularHomologyδ (triple hst htv) R2 (n + 1) n

/-- Exactness at `Hₙ(t, s)`. -/
lemma triple_exact_inner (n : ℕ) (x : relH n hst)
    (hx : relMap n hst (hst.trans htv) subset_rfl htv x = 0) :
    ∃ z : relH (n + 1) htv, tripleδ hst htv n z = x := by
  have hE := TauCeti.TopTriple.singularHomology_exact_inner (triple hst htv) R2 (n + 1) n
  rw [ShortComplex.moduleCat_exact_iff] at hE
  exact hE x ((ConcreteCategory.congr_hom (map_innerToTotal_triple hst htv n) x).trans hx)

/-- Exactness at `Hₙ(v, s)`. -/
lemma triple_exact_total (n : ℕ) (y : relH n (hst.trans htv))
    (hy : relMap n (hst.trans htv) htv hst subset_rfl y = 0) :
    ∃ x : relH n hst, relMap n hst (hst.trans htv) subset_rfl htv x = y := by
  have hE := TauCeti.TopTriple.singularHomology_exact_total (triple hst htv) R2 n
  rw [ShortComplex.moduleCat_exact_iff] at hE
  obtain ⟨x, hx⟩ := hE y ((ConcreteCategory.congr_hom (map_totalToOuter_triple hst htv n) y).trans hy)
  exact ⟨x, (ConcreteCategory.congr_hom (map_innerToTotal_triple hst htv n) x).symm.trans hx⟩

/-- Exactness at `Hₙ₊₁(v, t)`. -/
lemma triple_exact_outer (n : ℕ) (y : relH (n + 1) htv) (hy : tripleδ hst htv n y = 0) :
    ∃ x : relH (n + 1) (hst.trans htv),
      relMap (n + 1) (hst.trans htv) htv hst subset_rfl x = y := by
  have hE := TauCeti.TopTriple.singularHomology_exact_outer (triple hst htv) R2 (n + 1) n
  rw [ShortComplex.moduleCat_exact_iff] at hE
  obtain ⟨x, hx⟩ := hE y hy
  exact ⟨x, (ConcreteCategory.congr_hom (map_totalToOuter_triple hst htv (n + 1)) x).symm.trans hx⟩

/-- The two maps `Hₙ(t, s) ⟶ Hₙ(v, s) ⟶ Hₙ(v, t)` compose to zero. -/
lemma triple_comp_zero (n : ℕ) (x : relH n hst) :
    relMap n (hst.trans htv) htv hst subset_rfl
      (relMap n hst (hst.trans htv) subset_rfl htv x) = 0 := by
  have h0 :=
    TauCeti.TopTriple.singularHomologyMap_innerToTotal_comp_totalToOuter (triple hst htv) R2 n
  rw [map_innerToTotal_triple, map_totalToOuter_triple] at h0
  exact ConcreteCategory.congr_hom h0 x

/-- The composite `Hₙ₊₁(v, s) ⟶ Hₙ₊₁(v, t) ⟶ Hₙ(t, s)` is zero. -/
lemma tripleδ_comp_zero (n : ℕ) (y : relH (n + 1) (hst.trans htv)) :
    tripleδ hst htv n (relMap (n + 1) (hst.trans htv) htv hst subset_rfl y) = 0 := by
  have h0 := TauCeti.TopTriple.comp_singularHomologyδ (triple hst htv) R2 (n + 1) n
  rw [map_totalToOuter_triple] at h0
  exact ConcreteCategory.congr_hom h0 y

variable {s' t' v' : Set X} (hst' : s' ⊆ t') (htv' : t' ⊆ v')

/-- A map of triples given by inclusions. -/
def tripleMap (hs : s ⊆ s') (ht : t ⊆ t') (hv : v ⊆ v') :
    triple hst htv ⟶ triple hst' htv' :=
  ⟨ComposableArrows.homMk₂ (TopCat.ofHom (ContinuousMap.inclusion hs))
    (TopCat.ofHom (ContinuousMap.inclusion ht)) (TopCat.ofHom (ContinuousMap.inclusion hv))
    (by ext; rfl) (by ext; rfl)⟩

/-- Naturality of the connecting morphism of a triple, in element form. -/
lemma tripleδ_naturality (n : ℕ) (hs : s ⊆ s') (ht : t ⊆ t') (hv : v ⊆ v')
    (y : relH (n + 1) htv) :
    relMap n hst hst' hs ht (tripleδ hst htv n y) =
      tripleδ hst' htv' n (relMap (n + 1) htv htv' ht hv y) := by
  have h := TauCeti.TopTriple.singularHomologyδ_naturality
    (tripleMap hst htv hst' htv' hs ht hv) R2 (n + 1) n
  have h₁ : TauCeti.TopTriple.innerPair.map (tripleMap hst htv hst' htv' hs ht hv) =
      pairMap hst hst' hs ht := by
    ext : 2 <;> rfl
  have h₂ : TauCeti.TopTriple.outerPair.map (tripleMap hst htv hst' htv' hs ht hv) =
      pairMap htv htv' ht hv := by
    ext : 2 <;> rfl
  have h₁' : TopPair.singularHomologyMap
      (TauCeti.TopTriple.innerPair.map (tripleMap hst htv hst' htv' hs ht hv)) R2 n =
      relMap n hst hst' hs ht := by rw [h₁]; rfl
  have h₂' : TopPair.singularHomologyMap
      (TauCeti.TopTriple.outerPair.map (tripleMap hst htv hst' htv' hs ht hv)) R2 (n + 1) =
      relMap (n + 1) htv htv' ht hv := by rw [h₂]; rfl
  rw [h₁', h₂'] at h
  exact ConcreteCategory.congr_hom h y

end Triples

section Excision

variable {X : TopCat.{u}}

/-- **Excision.** For open `t` and `s'`, the inclusion `(t, s) ⟶ (t', s')` induces an isomorphism
on relative homology provided `t ∩ s' ⊆ s` and `t' ⊆ t ∪ s'`. -/
lemma isIso_relMap_excision (i : ℕ) {s t s' t' : Set X} (h : s ⊆ t) (h' : s' ⊆ t')
    (hs : s ⊆ s') (ht : t ⊆ t') (hts : t ∩ s' ⊆ s) (hcov : t' ⊆ t ∪ s')
    (hto : IsOpen t) (hso : IsOpen s') :
    IsIso (relMap i h h' hs ht) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover R2 (pairMap h h' hs ht)
    (IsEmbedding.inclusion ht) ?_
    (fun b : Bool ↦ bif b then (Subtype.val ⁻¹' t : Set t') else Subtype.val ⁻¹' s')
    (fun b ↦ by cases b
                · exact hso.preimage continuous_subtype_val
                · exact hto.preimage continuous_subtype_val) ?_ ?_ i
  · rintro (x : t) ⟨(y : s'), hy⟩
    have hy' : (y : X) = x := congrArg Subtype.val hy
    exact ⟨⟨(x : X), hts ⟨x.2, hy' ▸ y.2⟩⟩, rfl⟩
  · refine Set.eq_univ_of_forall fun (x : t') ↦ ?_
    rcases hcov x.2 with hx | hx
    · exact Set.mem_iUnion.2 ⟨true, hx⟩
    · exact Set.mem_iUnion.2 ⟨false, hx⟩
  · intro b
    cases b
    · exact Or.inl fun (x : t') hx ↦ ⟨⟨(x : X), hx⟩, rfl⟩
    · exact Or.inr fun (x : t') hx ↦ ⟨⟨(x : X), hx⟩, rfl⟩

lemma bijective_relMap_excision (i : ℕ) {s t s' t' : Set X} (h : s ⊆ t) (h' : s' ⊆ t')
    (hs : s ⊆ s') (ht : t ⊆ t') (hts : t ∩ s' ⊆ s) (hcov : t' ⊆ t ∪ s')
    (hto : IsOpen t) (hso : IsOpen s') :
    Function.Bijective (relMap i h h' hs ht) := by
  have := isIso_relMap_excision i h h' hs ht hts hcov hto hso
  exact ConcreteCategory.bijective_of_isIso _

end Excision

end SharpLSI.Topology
