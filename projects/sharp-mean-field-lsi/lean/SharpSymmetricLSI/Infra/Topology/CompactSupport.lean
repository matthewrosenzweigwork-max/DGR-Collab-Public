import SharpSymmetricLSI.Infra.Topology.Gluing
import SharpSymmetricLSI.Vendor.TauCeti.AlgebraicTopology.Singular.DirectedUnion

/-!
# Compact supports for local homology

If a closed set `A` is the intersection of a decreasing sequence of closed sets `K j`, and the
ambient space has vanishing homology in positive degrees, then every class of
`Hᵢ₊₁(X, X ∖ A)` is the restriction of a class of some `Hᵢ₊₁(X, X ∖ K j)`
(`exists_restr_eq_of_iInter`).  This is the compactness argument in Hatcher's proof of
Lemma 3.27: singular homology of `X ∖ A = ⋃ⱼ X ∖ K j` is the colimit of the homology of the
`X ∖ K j` (vendored Tau Ceti `isColimitMapCoconeSingularHomology`), combined with the long exact
sequences of the pairs.
-/

universe u

open CategoryTheory Limits Set TopCat

namespace SharpLSI.Topology

/-- **Every class of a directed union comes from a member.** -/
lemma exists_homologyMap_inclusion_eq {Y : TopCat.{u}} {U : ℕ → Set Y} (hU : Monotone U)
    {V : Set Y} (hUV : ∀ j, U j ⊆ V) (hopen : ∀ j, IsOpen (Subtype.val ⁻¹' U j : Set V))
    (hcover : V ⊆ ⋃ j, U j) (k : ℕ) (x : ((toSSet.obj (TopCat.of V)).homology R2 k : ModuleCat.{u} F2.{u})) :
    ∃ j, ∃ y : ((toSSet.obj (TopCat.of (U j))).homology R2 k : ModuleCat.{u} F2.{u}),
      SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion (hUV j)))) R2 k y = x := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} F2.{u})) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let c : Cocone ({ obj j := of (U j)
                    map f := ofHom (ContinuousMap.inclusion (hU f.le)) } : ℕ ⥤ TopCat.{u}) :=
    { pt := of V, ι := { app j := ofHom (ContinuousMap.inclusion (hUV j)) } }
  have hK (K : Set c.pt) (hK : IsCompact K) : ∃ j, K ⊆ Set.range (c.ι.app j) := by
    obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j ↦ (Subtype.val ⁻¹' U j : Set V)) hopen
      (fun x _ ↦ Set.mem_iUnion.2 (Set.mem_iUnion.1 (hcover x.2) : ∃ j, x.1 ∈ U j))
      (Monotone.directed_le fun _ _ h ↦ Set.preimage_mono (hU h))
    exact ⟨j, fun x hx ↦ ⟨⟨x.1, hj hx⟩, rfl⟩⟩
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _
    (TauCeti.isColimitMapCoconeSingularHomology R2 k c
      (fun j ↦ Topology.IsEmbedding.inclusion (hUV j)) hK) x
  exact ⟨j, y, hy⟩

variable {X : TopCat.{u}}

/-- The pair `(X, X ∖ A)`, presented as `(univ, Aᶜ)`. -/
abbrev compPair (A : Set X) : TopPair.{u} := TopPair.ofInclusion (subset_univ (Aᶜ : Set X))

/-- **Compact supports.** Let `A = ⋂ⱼ K j` with `K` decreasing and closed, and suppose `X` has
vanishing homology in positive degrees.  Then every class of `Hᵢ₊₁(X, X ∖ A)` is the restriction
of a class of some `Hᵢ₊₁(X, X ∖ K j)`. -/
theorem exists_restr_eq_of_iInter
    (hX : ∀ i, ∀ a : ((toSSet.obj (TopCat.of (univ : Set X))).homology R2 (i + 1) :
      ModuleCat.{u} F2.{u}), a = 0)
    {A : Set X} {K : ℕ → Set X} (hK : Antitone K) (hAK : ∀ j, A ⊆ K j)
    (hKc : ∀ j, IsClosed (K j)) (hinter : ⋂ j, K j ⊆ A) (i : ℕ) (z : locH (i + 1) A) :
    ∃ j, ∃ z' : locH (i + 1) (K j), restr (i + 1) (hAK j) z' = z := by
  have hUV (j : ℕ) : (K j)ᶜ ⊆ Aᶜ := compl_subset_compl.2 (hAK j)
  obtain ⟨j, c, hc⟩ := exists_homologyMap_inclusion_eq (U := fun j ↦ (K j)ᶜ)
    (fun _ _ h ↦ compl_subset_compl.2 (hK h)) hUV
    (fun j ↦ (hKc j).isOpen_compl.preimage continuous_subtype_val)
    (fun x hx ↦ by
      by_contra h
      simp only [mem_iUnion, mem_compl_iff, not_exists, not_not] at h
      exact hx (hinter (mem_iInter.2 h)))
    i (((compPair A).singularHomologyδ R2 (i + 1) i) z)
  -- `c` dies in the homology of `X`.
  let ι : (compPair (K j)).snd ⟶ (compPair A).snd := ofHom (ContinuousMap.inclusion (hUV j))
  have key : SSet.homologyMap (toSSet.map (compPair (K j)).map) R2 i =
      SSet.homologyMap (toSSet.map ι) R2 i ≫
        SSet.homologyMap (toSSet.map (compPair A).map) R2 i := by
    have := SSet.homologyMap_comp (f := toSSet.map ι) (g := toSSet.map (compPair A).map) (R := R2) (n := i)
    rw [← Functor.map_comp] at this
    exact this
  have hc0 : SSet.homologyMap (toSSet.map (compPair (K j)).map) R2 i c = 0 :=
    (ConcreteCategory.congr_hom key c).trans
      ((congrArg (SSet.homologyMap (toSSet.map (compPair A).map) R2 i) hc).trans
        (ConcreteCategory.congr_hom ((compPair A).singularHomologyδ_comp R2 (i + 1) i) z))
  have hE := (compPair (K j)).singularHomology_exact_subspace R2 (i + 1) i
  rw [ShortComplex.moduleCat_exact_iff] at hE
  obtain ⟨y, hy⟩ := hE c hc0
  have hy' : ((compPair (K j)).singularHomologyδ R2 (i + 1) i) y = c := hy
  let f := pairMap (subset_univ ((K j)ᶜ : Set X)) (subset_univ (Aᶜ : Set X)) (hUV j) subset_rfl
  have hsnd : TopPair.Hom.snd f = ofHom (ContinuousMap.inclusion (hUV j)) := by ext; rfl
  have nat : ((compPair A).singularHomologyδ R2 (i + 1) i) (restr (i + 1) (hAK j) y) =
      ((compPair A).singularHomologyδ R2 (i + 1) i) z := by
    refine (ConcreteCategory.congr_hom
      (TopPair.singularHomologyδ_naturality R2 f (i + 1) i) y).symm.trans ?_
    refine Eq.trans ?_ hc
    refine (congrArg (SSet.homologyMap (toSSet.map (TopPair.Hom.snd f)) R2 i) hy').trans ?_
    rw [hsnd]
    rfl
  -- The difference lies in the image of the homology of `X`, which vanishes.
  have hR := (compPair A).singularHomology_exact_relative R2 (i + 1) i
  rw [ShortComplex.moduleCat_exact_iff] at hR
  obtain ⟨w, hw⟩ := hR (restr (i + 1) (hAK j) y - z) (by
    change ((compPair A).singularHomologyδ R2 (i + 1) i) _ = 0
    rw [map_sub, nat, sub_self])
  have hw' : (compPair A).singularHomologyπ R2 (i + 1) w = restr (i + 1) (hAK j) y - z := hw
  have h0 : (compPair A).singularHomologyπ R2 (i + 1) w = 0 := by rw [hX i w]; exact map_zero _
  exact ⟨j, y, (sub_eq_zero.1 (hw'.symm.trans h0))⟩

end SharpLSI.Topology
