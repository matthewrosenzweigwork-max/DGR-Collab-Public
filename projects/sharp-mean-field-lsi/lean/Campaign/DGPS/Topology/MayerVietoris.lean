import DGPS.Topology.Excision
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace DGPS.Topology.MayerVietoris

abbrev CC : Type 1 := ChainComplex F2Mod ℕ

lemma add_self_zero {M : Type*} [AddCommGroup M] [Module F2 M] (a : M) : a + a = 0 := by
  calc a + a = a + -a := by rw [Excision.neg_eq_self'' a]
    _ = 0 := add_neg_cancel a

/-- Elementwise hypotheses for a Mayer-Vietoris short exact sequence. -/
structure MVHyp {M K L N : CC} (f1 : M ⟶ K) (f2 : M ⟶ L) (g1 : K ⟶ N) (g2 : L ⟶ N) : Prop where
  comm : ∀ n c, (g1.f n).hom ((f1.f n).hom c) = (g2.f n).hom ((f2.f n).hom c)
  inj : ∀ n c, (f1.f n).hom c = 0 → (f2.f n).hom c = 0 → c = 0
  mid : ∀ n a b, (g1.f n).hom a = (g2.f n).hom b →
    ∃ c, (f1.f n).hom c = a ∧ (f2.f n).hom c = b
  surj : ∀ n s, ∃ a b, (g1.f n).hom a + (g2.f n).hom b = s

section
variable {M K L N : CC} {f1 : M ⟶ K} {f2 : M ⟶ L} {g1 : K ⟶ N} {g2 : L ⟶ N}

lemma lift_desc_zero (h : MVHyp f1 f2 g1 g2) : biprod.lift f1 f2 ≫ biprod.desc g1 g2 = 0 := by
  rw [biprod.lift_desc]
  ext n c
  have := h.comm n c
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, ModuleCat.hom_add,
    ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply, HomologicalComplex.zero_f_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply]
  rw [this]; exact add_self_zero _

/-- the short complex -/
noncomputable def mvShortComplex (h : MVHyp f1 f2 g1 g2) : ShortComplex CC :=
  ShortComplex.mk (biprod.lift f1 f2) (biprod.desc g1 g2) (lift_desc_zero h)

lemma biprod_decomp (i : ℕ) (x : (K ⊞ L).X i) :
    x = ((biprod.inl : K ⟶ K ⊞ L).f i).hom (((biprod.fst : K ⊞ L ⟶ K).f i).hom x) +
      ((biprod.inr : L ⟶ K ⊞ L).f i).hom (((biprod.snd : K ⊞ L ⟶ L).f i).hom x) := by
  have := congr($(biprod_total_f K L i) x)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at this
  exact this.symm


section elem
variable (K L : CC) (i : ℕ)

lemma fst_inl (a : K.X i) : ((biprod.fst : K ⊞ L ⟶ K).f i).hom (((biprod.inl : K ⟶ K ⊞ L).f i).hom a) = a := by
  have := congr($(biprod_inl_fst_f (K := K) (L := L) i) a)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, ModuleCat.hom_zero,
    LinearMap.id_apply, LinearMap.zero_apply] using this

lemma snd_inl (a : K.X i) : ((biprod.snd : K ⊞ L ⟶ L).f i).hom (((biprod.inl : K ⟶ K ⊞ L).f i).hom a) = 0 := by
  have := congr($(biprod_inl_snd_f (K := K) (L := L) i) a)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, ModuleCat.hom_zero,
    LinearMap.id_apply, LinearMap.zero_apply] using this

lemma fst_inr (b : L.X i) : ((biprod.fst : K ⊞ L ⟶ K).f i).hom (((biprod.inr : L ⟶ K ⊞ L).f i).hom b) = 0 := by
  have := congr($(biprod_inr_fst_f (K := K) (L := L) i) b)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, ModuleCat.hom_zero,
    LinearMap.id_apply, LinearMap.zero_apply] using this

lemma snd_inr (b : L.X i) : ((biprod.snd : K ⊞ L ⟶ L).f i).hom (((biprod.inr : L ⟶ K ⊞ L).f i).hom b) = b := by
  have := congr($(biprod_inr_snd_f (K := K) (L := L) i) b)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, ModuleCat.hom_zero,
    LinearMap.id_apply, LinearMap.zero_apply] using this

lemma biprod_ext {x y : (K ⊞ L).X i}
    (h1 : ((biprod.fst : K ⊞ L ⟶ K).f i).hom x = ((biprod.fst : K ⊞ L ⟶ K).f i).hom y)
    (h2 : ((biprod.snd : K ⊞ L ⟶ L).f i).hom x = ((biprod.snd : K ⊞ L ⟶ L).f i).hom y) : x = y := by
  rw [biprod_decomp i x, biprod_decomp i y, h1, h2]

end elem

variable (f1 f2 g1 g2) in
lemma fst_lift (i : ℕ) (c : M.X i) :
    ((biprod.fst : K ⊞ L ⟶ K).f i).hom (((biprod.lift f1 f2).f i).hom c) = (f1.f i).hom c := by
  have e : (biprod.lift f1 f2 ≫ biprod.fst).f i = f1.f i := by rw [biprod.lift_fst]
  have := congr($(e) c)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using this

variable (f1 f2 g1 g2) in
lemma snd_lift (i : ℕ) (c : M.X i) :
    ((biprod.snd : K ⊞ L ⟶ L).f i).hom (((biprod.lift f1 f2).f i).hom c) = (f2.f i).hom c := by
  have e : (biprod.lift f1 f2 ≫ biprod.snd).f i = f2.f i := by rw [biprod.lift_snd]
  have := congr($(e) c)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] using this

variable (f1 f2 g1 g2) in
lemma desc_apply (i : ℕ) (x : (K ⊞ L).X i) :
    ((biprod.desc g1 g2).f i).hom x =
      (g1.f i).hom (((biprod.fst : K ⊞ L ⟶ K).f i).hom x) +
        (g2.f i).hom (((biprod.snd : K ⊞ L ⟶ L).f i).hom x) := by
  conv_lhs => rw [biprod_decomp i x]
  rw [map_add]
  have e1 : ((biprod.inl : K ⟶ K ⊞ L) ≫ biprod.desc g1 g2).f i = g1.f i := by rw [biprod.inl_desc]
  have e2 : ((biprod.inr : L ⟶ K ⊞ L) ≫ biprod.desc g1 g2).f i = g2.f i := by rw [biprod.inr_desc]
  have h1 := congr($(e1) (((biprod.fst : K ⊞ L ⟶ K).f i).hom x))
  have h2 := congr($(e2) (((biprod.snd : K ⊞ L ⟶ L).f i).hom x))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1, h2]

lemma mvShortExact (h : MVHyp f1 f2 g1 g2) : (mvShortComplex h).ShortExact := by
  rw [shortExact_iff_degreewise_shortExact]
  intro i
  have hm : Mono (((mvShortComplex h).map (eval _ _ i)).f) := by
    show Mono ((biprod.lift f1 f2).f i)
    rw [ModuleCat.mono_iff_injective]
    intro a b hab
    rw [← sub_eq_zero]
    refine h.inj i _ ?_ ?_
    · rw [map_sub, ← fst_lift f1 f2, ← fst_lift f1 f2, hab, sub_self]
    · rw [map_sub, ← snd_lift f1 f2, ← snd_lift f1 f2, hab, sub_self]
  have he : Epi (((mvShortComplex h).map (eval _ _ i)).g) := by
    show Epi ((biprod.desc g1 g2).f i)
    rw [ModuleCat.epi_iff_surjective]
    intro s
    obtain ⟨a, b, hs⟩ := h.surj i s
    refine ⟨((biprod.inl : K ⟶ K ⊞ L).f i).hom a + ((biprod.inr : L ⟶ K ⊞ L).f i).hom b, ?_⟩
    rw [desc_apply g1 g2]
    simp only [map_add, fst_inl, fst_inr, snd_inl, snd_inr, add_zero, zero_add]
    exact hs
  have hex : ((mvShortComplex h).map (eval _ _ i)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x : (K ⊞ L).X i) hx
    have hx' : ((biprod.desc g1 g2).f i).hom x = 0 := hx
    rw [desc_apply g1 g2] at hx'
    obtain ⟨c, hc1, hc2⟩ := h.mid i ((((biprod.fst : K ⊞ L ⟶ K).f i).hom x))
      ((((biprod.snd : K ⊞ L ⟶ L).f i).hom x)) (by
        rw [← sub_eq_zero, Excision.sub_eq_add'']; exact hx')
    show ∃ c : M.X i, ((biprod.lift f1 f2).f i).hom c = x
    refine ⟨c, ?_⟩
    apply biprod_ext
    · exact (fst_lift f1 f2 i c).trans hc1
    · exact (snd_lift f1 f2 i c).trans hc2
  exact ShortComplex.ShortExact.mk' hex hm he


instance homologyFunctorPreservesBinaryBiproducts (n : ℕ) :
    PreservesBinaryBiproducts (homologyFunctor F2Mod (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

variable (f1 f2 g1 g2) in
/-- The map `H_n(M) ⟶ H_n(K) ⊞ H_n(L)`. -/
noncomputable abbrev mvF (n : ℕ) : M.homology n ⟶ K.homology n ⊞ L.homology n :=
  biprod.lift (homologyMap f1 n) (homologyMap f2 n)

variable (f1 f2 g1 g2) in
/-- The map `H_n(K) ⊞ H_n(L) ⟶ H_n(N)`. -/
noncomputable abbrev mvG (n : ℕ) : K.homology n ⊞ L.homology n ⟶ N.homology n :=
  biprod.desc (homologyMap g1 n) (homologyMap g2 n)

theorem mv_exact_aux (h : MVHyp f1 f2 g1 g2) {N' : CC} (φ : N ⟶ N') [QuasiIso φ] :
    ∃ δ : ∀ n : ℕ, N'.homology (n + 1) ⟶ M.homology n,
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (mvF f1 f2 n).hom) ∧
      (∀ n, LinearMap.range (mvF f1 f2 n).hom = LinearMap.ker (mvG (g1 ≫ φ) (g2 ≫ φ) n).hom) ∧
      (∀ n, LinearMap.range (mvG (g1 ≫ φ) (g2 ≫ φ) (n + 1)).hom = LinearMap.ker (δ n).hom) := by
  have hS := mvShortExact h
  have hφ : ∀ i, IsIso (homologyMap φ i) := fun i => inferInstance
  let e : ∀ n, (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n := fun n =>
    (homologyFunctor F2Mod (ComplexShape.down ℕ) n).mapBiprod K L
  have he1 : ∀ n, homologyMap (biprod.lift f1 f2) n ≫ (e n).hom = mvF f1 f2 n := fun n =>
    biprod.map_lift_mapBiprod (homologyFunctor F2Mod (ComplexShape.down ℕ) n) K L f1 f2
  have he2 : ∀ n, (e n).hom ≫ mvG g1 g2 n = homologyMap (biprod.desc g1 g2) n := fun n =>
    biprod.mapBiprod_hom_desc (homologyFunctor F2Mod (ComplexShape.down ℕ) n) K L g1 g2
  let eφ : ∀ i, N.homology i ≅ N'.homology i := fun i => @asIso _ _ _ _ _ (hφ i)
  obtain ⟨d, hd1, hd3, hx1, hx2, hx3⟩ : ∃ d : ∀ n : ℕ, N.homology (n + 1) ⟶ M.homology n,
      ∃ (hd1 : ∀ n, d n ≫ homologyMap (biprod.lift f1 f2) n = 0)
        (hd3 : ∀ n, homologyMap (biprod.desc g1 g2) (n + 1) ≫ d n = 0),
      (∀ n, (ShortComplex.mk (d n) (homologyMap (biprod.lift f1 f2) n) (hd1 n)).Exact) ∧
      (∀ n, (ShortComplex.mk (homologyMap (biprod.lift f1 f2) n)
        (homologyMap (biprod.desc g1 g2) n) (by
          rw [← homologyMap_comp, lift_desc_zero h, homologyMap_zero])).Exact) ∧
      (∀ n, (ShortComplex.mk (homologyMap (biprod.desc g1 g2) (n + 1)) (d n) (hd3 n)).Exact) :=
    ⟨fun n => hS.δ (n + 1) n rfl, fun n => hS.δ_comp (n + 1) n rfl,
      fun n => hS.comp_δ (n + 1) n rfl, fun n => hS.homology_exact₁ (n + 1) n rfl,
      fun n => hS.homology_exact₂ n, fun n => hS.homology_exact₃ (n + 1) n rfl⟩
  let δ : ∀ n : ℕ, N'.homology (n + 1) ⟶ M.homology n := fun n => (eφ (n + 1)).inv ≫ d n
  refine ⟨δ, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have hz : δ n ≫ mvF f1 f2 n = 0 := by
      rw [← he1 n, Category.assoc, reassoc_of% (hd1 n), zero_comp, comp_zero]
    let iso : ShortComplex.mk (d n) (homologyMap (biprod.lift f1 f2) n) (hd1 n) ≅
        ShortComplex.mk (δ n) (mvF f1 f2 n) hz :=
      ShortComplex.isoMk (eφ (n + 1)) (Iso.refl _) (e n) (by simp [δ]) (by simpa using (he1 n).symm)
    exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (ShortComplex.exact_of_iso iso (hx1 n))
  · have hG : ∀ m, mvG (g1 ≫ φ) (g2 ≫ φ) m = mvG g1 g2 m ≫ homologyMap φ m := by
      intro m
      apply biprod.hom_ext'
      · simp [mvG, homologyMap_comp]
      · simp [mvG, homologyMap_comp]
    have hz0 : mvF f1 f2 n ≫ mvG g1 g2 n = 0 := by
      rw [← he1 n, Category.assoc, he2 n, ← homologyMap_comp, lift_desc_zero h, homologyMap_zero]
    have hz : mvF f1 f2 n ≫ mvG (g1 ≫ φ) (g2 ≫ φ) n = 0 := by
      rw [hG, ← Category.assoc, hz0, zero_comp]
    let iso : ShortComplex.mk (homologyMap (biprod.lift f1 f2) n)
        (homologyMap (biprod.desc g1 g2) n) (by
          rw [← homologyMap_comp, lift_desc_zero h, homologyMap_zero]) ≅
        ShortComplex.mk (mvF f1 f2 n) (mvG (g1 ≫ φ) (g2 ≫ φ) n) hz :=
      ShortComplex.isoMk (Iso.refl _) (e n) (eφ n) (by simpa using (he1 n).symm)
        (by
          show (e n).hom ≫ mvG (g1 ≫ φ) (g2 ≫ φ) n = _ ≫ (eφ n).hom
          rw [hG, ← Category.assoc, he2 n]; rfl)
    exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (ShortComplex.exact_of_iso iso (hx2 n))
  · have hG : ∀ m, mvG (g1 ≫ φ) (g2 ≫ φ) m = mvG g1 g2 m ≫ homologyMap φ m := by
      intro m
      apply biprod.hom_ext'
      · simp [mvG, homologyMap_comp]
      · simp [mvG, homologyMap_comp]
    have hz : mvG (g1 ≫ φ) (g2 ≫ φ) (n + 1) ≫ δ n = 0 := by
      show _ ≫ (eφ (n + 1)).inv ≫ d n = 0
      rw [hG, Category.assoc]
      have h1 : homologyMap φ (n + 1) ≫ (eφ (n + 1)).inv = 𝟙 _ := (eφ (n + 1)).hom_inv_id
      have h2 : mvG g1 g2 (n + 1) = (e (n + 1)).inv ≫ homologyMap (biprod.desc g1 g2) (n + 1) := by
        rw [← he2 (n + 1), Iso.inv_hom_id_assoc]
      rw [reassoc_of% h1, h2, Category.assoc, hd3, comp_zero]
    let iso : ShortComplex.mk (homologyMap (biprod.desc g1 g2) (n + 1)) (d n) (hd3 n) ≅
        ShortComplex.mk (mvG (g1 ≫ φ) (g2 ≫ φ) (n + 1)) (δ n) hz :=
      ShortComplex.isoMk (e (n + 1)) (eφ (n + 1)) (Iso.refl _)
        (by
          show (e (n + 1)).hom ≫ mvG (g1 ≫ φ) (g2 ≫ φ) (n + 1) = _ ≫ (eφ (n + 1)).hom
          rw [hG, ← Category.assoc, he2 (n + 1)]; rfl)
        (by simp [δ])
    exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (ShortComplex.exact_of_iso iso (hx3 n))

theorem mv_epi0 (h : MVHyp f1 f2 g1 g2) {N' : CC} (φ : N ⟶ N') [QuasiIso φ] :
    Epi (mvG (g1 ≫ φ) (g2 ≫ φ) 0) := by
  have hS := mvShortExact h
  have hg : Epi (mvShortComplex h).g := hS.epi_g
  have : Epi ((biprod.desc g1 g2).f 0) := inferInstanceAs (Epi ((mvShortComplex h).g.f 0))
  have hepi : Epi (homologyMap (biprod.desc g1 g2) 0) :=
    epi_homologyMap_of_epi_of_not_rel (biprod.desc g1 g2) 0 (by simp)
  have he2 : ((homologyFunctor F2Mod (ComplexShape.down ℕ) 0).mapBiprod K L).hom ≫
      mvG g1 g2 0 = homologyMap (biprod.desc g1 g2) 0 :=
    biprod.mapBiprod_hom_desc (homologyFunctor F2Mod (ComplexShape.down ℕ) 0) K L g1 g2
  have hG : mvG (g1 ≫ φ) (g2 ≫ φ) 0 = mvG g1 g2 0 ≫ homologyMap φ 0 := by
    apply biprod.hom_ext'
    · simp [mvG, homologyMap_comp]
    · simp [mvG, homologyMap_comp]
  have h3 : Epi (mvG g1 g2 0) := @epi_of_epi_fac _ _ _ _ _ _ _ _ hepi he2
  rw [hG]
  infer_instance

end


section Topological

open DGPS.Topology

/-- The inclusion of a subset as a continuous map. -/
def incl {X : TopCat.{0}} (S : Set X) : TopCat.of ↥S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of a subset in a larger subset. -/
def inclSub {X : TopCat.{0}} {S T : Set X} (h : S ⊆ T) : TopCat.of ↥S ⟶ TopCat.of ↥T :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

lemma incl_emb {X : TopCat.{0}} (S : Set X) : Topology.IsEmbedding (incl S).hom :=
  Topology.IsEmbedding.subtypeVal

lemma inclSub_emb {X : TopCat.{0}} {S T : Set X} (h : S ⊆ T) :
    Topology.IsEmbedding (inclSub h).hom :=
  Topology.IsEmbedding.inclusion h

lemma incl_range {X : TopCat.{0}} (S : Set X) : Set.range (incl S).hom = S :=
  Subtype.range_val

lemma inclSub_range {X : TopCat.{0}} {S T : Set X} (h : S ⊆ T) :
    Set.range (inclSub h).hom = {y : TopCat.of ↥T | y.1 ∈ S} :=
  Set.range_inclusion h

lemma inclSub_comp_incl {X : TopCat.{0}} {S T : Set X} (h : S ⊆ T) :
    inclSub h ≫ incl T = incl S := by
  ext x; rfl

lemma chain_inj {A X : TopCat.{0}} (i : A ⟶ X) (hi : Function.Injective i.hom) (n : ℕ) :
    Function.Injective ((singularChains.map i).f n).hom := by
  have : Mono i := (TopCat.mono_iff_injective _).2 hi
  have h := relative_chain_quotient.1 (TopPair.of i) n
  exact (ModuleCat.mono_iff_injective _).1 h

lemma comp_incl_apply {X : TopCat.{0}} {S T : Set X} (h : S ⊆ T) (n : ℕ)
    (z : (singularChains.obj (TopCat.of ↥S)).X n) :
    ((singularChains.map (incl T)).f n).hom (((singularChains.map (inclSub h)).f n).hom z) =
      ((singularChains.map (incl S)).f n).hom z := by
  rw [← Excision.sc_map_comp_apply, inclSub_comp_incl]

lemma range_incl_eq {X : TopCat.{0}} (S : Set X) (n : ℕ) :
    LinearMap.range ((singularChains.map (incl S)).f n).hom = SmallChains.smallSub X {S} n := by
  have := Excision.range_map_eq (incl S) (incl_emb S) n
  rwa [incl_range] at this

lemma range_inclSub_eq {X : TopCat.{0}} {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    LinearMap.range ((singularChains.map (inclSub h)).f n).hom =
      SmallChains.smallSub (TopCat.of ↥T) {{y : TopCat.of ↥T | y.1 ∈ S}} n := by
  have := Excision.range_map_eq (inclSub h) (inclSub_emb h) n
  rwa [inclSub_range] at this

lemma smallSub_union {X : TopCat.{0}} (S T : Set (Set X)) (n : ℕ) :
    SmallChains.smallSub X (S ∪ T) n =
      SmallChains.smallSub X S n ⊔ SmallChains.smallSub X T n := by
  unfold SmallChains.smallSub
  rw [← Submodule.span_union, ← Set.image_union]
  congr 2
  ext σ
  simp only [SmallChains.IsSmall, Set.mem_union, Set.mem_ofPred_eq, or_and_right, exists_or]

lemma smallSub_pair {X : TopCat.{0}} (U V : Set X) (n : ℕ) :
    SmallChains.smallSub X {U, V} n =
      SmallChains.smallSub X {U} n ⊔ SmallChains.smallSub X {V} n := by
  rw [Set.insert_eq]; exact smallSub_union _ _ n

lemma smallSub_single_le {X : TopCat.{0}} {W : Set (Set X)} {S : Set X} (hS : S ∈ W) (n : ℕ) :
    SmallChains.smallSub X {S} n ≤ SmallChains.smallSub X W n := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro σ ⟨B', hB', hs⟩
  rw [Set.mem_singleton_iff] at hB'
  subst hB'
  exact ⟨_, hS, hs⟩

/-- Corestriction of a chain map into a subcomplex. -/
noncomputable def subLift {C D : CC} (P : ∀ i, Submodule F2 (D.X i))
    (hP : ∀ i j (x : D.X i), x ∈ P i → (D.d i j).hom x ∈ P j) (f : C ⟶ D)
    (hf : ∀ i x, (f.f i).hom x ∈ P i) : C ⟶ SmallChains.subcomplex D P hP where
  f i := ModuleCat.ofHom (LinearMap.codRestrict (P i) (f.f i).hom (hf i))
  comm' i j _ := by
    ext x
    apply Subtype.ext
    exact congr($(f.comm i j) x)

lemma subLift_ι {C D : CC} (P : ∀ i, Submodule F2 (D.X i))
    (hP : ∀ i j (x : D.X i), x ∈ P i → (D.d i j).hom x ∈ P j) (f : C ⟶ D)
    (hf : ∀ i x, (f.f i).hom x ∈ P i) : subLift P hP f hf ≫ SmallChains.subcomplexι D P hP = f := by
  ext i x
  rfl

/-- The map `C(S) ⟶ C^W(X)` for `S ∈ W`. -/
noncomputable def toSmall {X : TopCat.{0}} (W : Set (Set X)) (S : Set X) (hS : S ∈ W) :
    singularChains.obj (TopCat.of ↥S) ⟶ SmallChains.smallChains W :=
  subLift _ _ (singularChains.map (incl S)) (fun i x => by
    apply smallSub_single_le hS
    rw [← range_incl_eq]
    exact ⟨x, rfl⟩)

lemma toSmall_ι {X : TopCat.{0}} (W : Set (Set X)) (S : Set X) (hS : S ∈ W) :
    toSmall W S hS ≫ SmallChains.smallChains_inclusion W = singularChains.map (incl S) :=
  subLift_ι _ _ _ _

lemma toSmall_val {X : TopCat.{0}} (W : Set (Set X)) (S : Set X) (hS : S ∈ W) (n : ℕ)
    (a : (singularChains.obj (TopCat.of ↥S)).X n) :
    (((toSmall W S hS).f n).hom a).1 = ((singularChains.map (incl S)).f n).hom a := rfl

end Topological


lemma bp_gluing {M K L N : F2Mod} (g1 : M ⟶ K) (g2 : M ⟶ L) (u : K ⟶ N) (v : L ⟶ N)
    (h : LinearMap.range (biprod.lift g1 g2).hom = LinearMap.ker (biprod.desc u v).hom)
    (a : K) (b : L) :
    (∃ c : M, g1.hom c = a ∧ g2.hom c = b) ↔ u.hom a = v.hom b := by
  have dec : ∀ y : (K ⊞ L : F2Mod), y = (biprod.inl : K ⟶ K ⊞ L).hom ((biprod.fst : K ⊞ L ⟶ K).hom y) +
      (biprod.inr : L ⟶ K ⊞ L).hom ((biprod.snd : K ⊞ L ⟶ L).hom y) := by
    intro y
    have := congr($(biprod.total (X := K) (Y := L)) y)
    simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] using this.symm
  have hd1 : (biprod.desc u v).hom ((biprod.inl : K ⟶ K ⊞ L).hom a) = u.hom a := by
    have := congr($(biprod.inl_desc u v) a)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hd2 : (biprod.desc u v).hom ((biprod.inr : L ⟶ K ⊞ L).hom b) = v.hom b := by
    have := congr($(biprod.inr_desc u v) b)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have f1 : ∀ c, (biprod.fst : K ⊞ L ⟶ K).hom ((biprod.lift g1 g2).hom c) = g1.hom c := by
    intro c
    have := congr($(biprod.lift_fst g1 g2) c)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have f2 : ∀ c, (biprod.snd : K ⊞ L ⟶ L).hom ((biprod.lift g1 g2).hom c) = g2.hom c := by
    intro c
    have := congr($(biprod.lift_snd g1 g2) c)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have i1 : (biprod.fst : K ⊞ L ⟶ K).hom ((biprod.inl : K ⟶ K ⊞ L).hom a) = a := by
    have := congr($(biprod.inl_fst (X := K) (Y := L)) a)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
      using this
  have i2 : (biprod.snd : K ⊞ L ⟶ L).hom ((biprod.inl : K ⟶ K ⊞ L).hom a) = 0 := by
    have := congr($(biprod.inl_snd (X := K) (Y := L)) a)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using this
  have i3 : (biprod.fst : K ⊞ L ⟶ K).hom ((biprod.inr : L ⟶ K ⊞ L).hom b) = 0 := by
    have := congr($(biprod.inr_fst (X := K) (Y := L)) b)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using this
  have i4 : (biprod.snd : K ⊞ L ⟶ L).hom ((biprod.inr : L ⟶ K ⊞ L).hom b) = b := by
    have := congr($(biprod.inr_snd (X := K) (Y := L)) b)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
      using this
  set x : (K ⊞ L : F2Mod) := (biprod.inl : K ⟶ K ⊞ L).hom a + (biprod.inr : L ⟶ K ⊞ L).hom b
    with hx
  have hdx : (biprod.desc u v).hom x = u.hom a + v.hom b := by
    rw [hx, map_add, hd1, hd2]
  have hfx : (biprod.fst : K ⊞ L ⟶ K).hom x = a := by
    rw [hx, map_add, i1, i3, add_zero]
  have hsx : (biprod.snd : K ⊞ L ⟶ L).hom x = b := by
    rw [hx, map_add, i2, i4, zero_add]
  constructor
  · rintro ⟨c, hc1, hc2⟩
    have hlx : (biprod.lift g1 g2).hom c = x := by
      rw [dec ((biprod.lift g1 g2).hom c), dec x, f1, f2, hfx, hsx, hc1, hc2]
    have hmem : x ∈ LinearMap.range (biprod.lift g1 g2).hom := ⟨c, hlx⟩
    rw [h] at hmem
    have h0 : u.hom a + v.hom b = 0 := by rw [← hdx]; exact hmem
    rw [← Excision.sub_eq_add''] at h0
    exact sub_eq_zero.1 h0
  · intro huv
    have hmem : x ∈ LinearMap.ker (biprod.desc u v).hom := by
      rw [LinearMap.mem_ker, hdx, huv]; exact add_self_zero _
    rw [← h] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_, ?_⟩
    · rw [← f1, hc, hfx]
    · rw [← f2, hc, hsx]


section Absolute

open DGPS.Topology

variable {X : TopCat.{0}}

theorem abs_hyp (U V : Set X) :
    MVHyp (singularChains.map (inclSub (Set.inter_subset_left : U ∩ V ⊆ U)))
      (singularChains.map (inclSub (Set.inter_subset_right : U ∩ V ⊆ V)))
      (toSmall ({U, V} : Set (Set X)) U (by simp))
      (toSmall ({U, V} : Set (Set X)) V (by simp)) where
  comm n c := by
    apply Subtype.ext
    rw [toSmall_val, toSmall_val, comp_incl_apply, comp_incl_apply]
  inj n c h1 _ := by
    apply chain_inj _ (inclSub_emb (Set.inter_subset_left : U ∩ V ⊆ U)).injective n
    rw [h1, map_zero]
  mid n a b h := by
    have h' := congrArg Subtype.val h
    rw [toSmall_val, toSmall_val] at h'
    have hU : ((singularChains.map (incl U)).f n).hom a ∈ SmallChains.smallSub X {U} n := by
      rw [← range_incl_eq]; exact ⟨a, rfl⟩
    have hV : ((singularChains.map (incl U)).f n).hom a ∈ SmallChains.smallSub X {V} n := by
      rw [h', ← range_incl_eq]; exact ⟨b, rfl⟩
    have hz := Excision.inter_smallSub U V n _ hU hV
    rw [← range_incl_eq] at hz
    obtain ⟨c, hc⟩ := hz
    refine ⟨c, ?_, ?_⟩
    · apply chain_inj _ (incl_emb U).injective n
      rw [comp_incl_apply, hc]
    · apply chain_inj _ (incl_emb V).injective n
      rw [comp_incl_apply, hc, h']
  surj n s := by
    have hs := s.2
    have hs' : s.1 ∈ SmallChains.smallSub X {U} n ⊔ SmallChains.smallSub X {V} n := by
      rw [← smallSub_pair]; exact hs
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hs'
    rw [← range_incl_eq] at hp hq
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a, b, Subtype.ext hpq⟩


theorem absolute_mv (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ δ : ∀ n : ℕ, (singularHomology (n + 1)).obj X ⟶
        (singularHomology n).obj (TopCat.of ↥(U ∩ V)),
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (biprod.lift
        ((singularHomology n).map (inclSub (Set.inter_subset_left : U ∩ V ⊆ U)))
        ((singularHomology n).map (inclSub (Set.inter_subset_right : U ∩ V ⊆ V)))).hom) ∧
      (∀ n, LinearMap.range (biprod.lift
        ((singularHomology n).map (inclSub (Set.inter_subset_left : U ∩ V ⊆ U)))
        ((singularHomology n).map (inclSub (Set.inter_subset_right : U ∩ V ⊆ V)))).hom =
        LinearMap.ker (biprod.desc ((singularHomology n).map (incl U))
          ((singularHomology n).map (incl V))).hom) ∧
      (∀ n, LinearMap.range (biprod.desc ((singularHomology (n + 1)).map (incl U))
          ((singularHomology (n + 1)).map (incl V))).hom = LinearMap.ker (δ n).hom) := by
  have hq : QuasiIso (SmallChains.smallChains_inclusion ({U, V} : Set (Set X))) := by
    have hopen : ∀ A ∈ ({U, V} : Set (Set X)), IsOpen A := by
      intro A hA
      rcases hA with rfl | hA
      · exact hU
      · rw [Set.mem_singleton_iff] at hA; subst hA; exact hV
    have hc : ⋃₀ ({U, V} : Set (Set X)) = Set.univ := by
      rw [Set.sUnion_pair]; exact hcov
    exact inferInstanceAs (QuasiIso (Excision.smallChainsHomotopyEquiv _ hopen hc).hom)
  obtain ⟨δ, h1, h2, h3⟩ := mv_exact_aux (abs_hyp U V) (SmallChains.smallChains_inclusion _)
  rw [toSmall_ι, toSmall_ι] at h2 h3
  exact ⟨δ, h1, h2, h3⟩

/-- The one-point space. -/
abbrev pt : TopCat.{0} := TopCat.of PUnit.{1}

/-- The collapse map to a point. -/
def toPt (S : TopCat.{0}) : S ⟶ pt := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The inclusion of a point. -/
def ptTo {S : TopCat.{0}} (p : S) : pt ⟶ S := TopCat.ofHom ⟨fun _ => p, continuous_const⟩

/-- The augmentation `H_0(S) ⟶ H_0(pt)`. -/
noncomputable abbrev eps (S : TopCat.{0}) : (singularHomology 0).obj S ⟶ (singularHomology 0).obj pt :=
  (singularHomology 0).map (toPt S)

lemma comp_toPt {S T : TopCat.{0}} (f : S ⟶ T) : f ≫ toPt T = toPt S := by
  ext

lemma ptTo_toPt {S : TopCat.{0}} (p : S) : ptTo p ≫ toPt S = 𝟙 pt := by
  ext

lemma eps_nat {S T : TopCat.{0}} (f : S ⟶ T) (x : (singularHomology 0).obj S) :
    (eps T).hom (((singularHomology 0).map f).hom x) = (eps S).hom x := by
  have h : (singularHomology 0).map f ≫ eps T = eps S := by
    rw [← Functor.map_comp, comp_toPt]
  have := congr($(h) x)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

lemma eps_ptTo {S : TopCat.{0}} (p : S) (t : (singularHomology 0).obj pt) :
    (eps S).hom (((singularHomology 0).map (ptTo p)).hom t) = t := by
  have h : (singularHomology 0).map (ptTo p) ≫ eps S = 𝟙 _ := by
    rw [← Functor.map_comp, ptTo_toPt, (singularHomology 0).map_id]
  have := congr($(h) t)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    using this

lemma bp_desc_apply {K L N : F2Mod} (u : K ⟶ N) (v : L ⟶ N) (x : (K ⊞ L : F2Mod)) :
    (biprod.desc u v).hom x =
      u.hom ((biprod.fst : K ⊞ L ⟶ K).hom x) + v.hom ((biprod.snd : K ⊞ L ⟶ L).hom x) := by
  have dec : x = (biprod.inl : K ⟶ K ⊞ L).hom ((biprod.fst : K ⊞ L ⟶ K).hom x) +
      (biprod.inr : L ⟶ K ⊞ L).hom ((biprod.snd : K ⊞ L ⟶ L).hom x) := by
    have := congr($(biprod.total (X := K) (Y := L)) x)
    simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] using this.symm
  have hd1 : ∀ a, (biprod.desc u v).hom ((biprod.inl : K ⟶ K ⊞ L).hom a) = u.hom a := by
    intro a
    have := congr($(biprod.inl_desc u v) a)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hd2 : ∀ b, (biprod.desc u v).hom ((biprod.inr : L ⟶ K ⊞ L).hom b) = v.hom b := by
    intro b
    have := congr($(biprod.inr_desc u v) b)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  conv_lhs => rw [dec]
  rw [map_add, hd1, hd2]

theorem absolute_epi0 (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    Function.Surjective (biprod.desc ((singularHomology 0).map (incl U))
      ((singularHomology 0).map (incl V))).hom := by
  have hq : QuasiIso (SmallChains.smallChains_inclusion ({U, V} : Set (Set X))) := by
    have hopen : ∀ A ∈ ({U, V} : Set (Set X)), IsOpen A := by
      intro A hA
      rcases hA with rfl | hA
      · exact hU
      · rw [Set.mem_singleton_iff] at hA; subst hA; exact hV
    have hc : ⋃₀ ({U, V} : Set (Set X)) = Set.univ := by
      rw [Set.sUnion_pair]; exact hcov
    exact inferInstanceAs (QuasiIso (Excision.smallChainsHomotopyEquiv _ hopen hc).hom)
  have h := mv_epi0 (abs_hyp U V) (SmallChains.smallChains_inclusion _)
  rw [toSmall_ι, toSmall_ι] at h
  exact (ModuleCat.epi_iff_surjective _).1 h

theorem reduced_deg0 (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hne : (U ∩ V).Nonempty) :
    (∀ z : (singularHomology 0).obj X, (eps X).hom z = 0 →
      ∃ (a : (singularHomology 0).obj (TopCat.of ↥U)) (b : (singularHomology 0).obj (TopCat.of ↥V)),
        (eps (TopCat.of ↥U)).hom a = 0 ∧ (eps (TopCat.of ↥V)).hom b = 0 ∧
        ((singularHomology 0).map (incl U)).hom a + ((singularHomology 0).map (incl V)).hom b = z) ∧
    (∀ (a : (singularHomology 0).obj (TopCat.of ↥U)) (b : (singularHomology 0).obj (TopCat.of ↥V)),
      (eps (TopCat.of ↥U)).hom a = 0 → (eps (TopCat.of ↥V)).hom b = 0 →
      ((singularHomology 0).map (incl U)).hom a + ((singularHomology 0).map (incl V)).hom b = 0 →
      ∃ c : (singularHomology 0).obj (TopCat.of ↥(U ∩ V)),
        (eps (TopCat.of ↥(U ∩ V))).hom c = 0 ∧
        ((singularHomology 0).map (inclSub (Set.inter_subset_left : U ∩ V ⊆ U))).hom c = a ∧
        ((singularHomology 0).map (inclSub (Set.inter_subset_right : U ∩ V ⊆ V))).hom c = b) := by
  obtain ⟨p, hpU, hpV⟩ := hne
  have key : ∀ (S : Set X) (hp : p ∈ S) (t : (singularHomology 0).obj pt),
      ((singularHomology 0).map (incl S)).hom
        (((singularHomology 0).map (ptTo (⟨p, hp⟩ : TopCat.of ↥S))).hom t) =
        ((singularHomology 0).map (ptTo p)).hom t := by
    intro S hp t
    have h : ptTo (⟨p, hp⟩ : TopCat.of ↥S) ≫ incl S = ptTo p := by ext; rfl
    have := congr($(congrArg (singularHomology 0).map h) t)
    rw [Functor.map_comp] at this
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hsurj : ∀ z : (singularHomology 0).obj X,
      ∃ (a : (singularHomology 0).obj (TopCat.of ↥U)) (b : (singularHomology 0).obj (TopCat.of ↥V)),
        ((singularHomology 0).map (incl U)).hom a + ((singularHomology 0).map (incl V)).hom b = z := by
    intro z
    obtain ⟨x, hx⟩ := absolute_epi0 U V hU hV hcov z
    exact ⟨_, _, by rw [← hx, bp_desc_apply]⟩
  obtain ⟨δ, -, h2, -⟩ := absolute_mv U V hU hV hcov
  refine ⟨fun z hz => ?_, fun a b ha hb hab => ?_⟩
  · obtain ⟨a0, b0, hz0⟩ := hsurj z
    have hε : (eps (TopCat.of ↥U)).hom a0 + (eps (TopCat.of ↥V)).hom b0 = 0 := by
      rw [← hz0, map_add, eps_nat, eps_nat] at hz
      exact hz
    have hb0 : (eps (TopCat.of ↥V)).hom b0 = (eps (TopCat.of ↥U)).hom a0 := by
      have h := eq_neg_of_add_eq_zero_right hε
      rw [Excision.neg_eq_self''] at h
      exact h
    refine ⟨a0 + ((singularHomology 0).map (ptTo (⟨p, hpU⟩ : TopCat.of ↥U))).hom
        ((eps (TopCat.of ↥U)).hom a0),
      b0 + ((singularHomology 0).map (ptTo (⟨p, hpV⟩ : TopCat.of ↥V))).hom
        ((eps (TopCat.of ↥U)).hom a0), ?_, ?_, ?_⟩
    · rw [map_add, eps_ptTo]; exact add_self_zero _
    · rw [map_add, eps_ptTo, hb0]; exact add_self_zero _
    · rw [map_add, map_add, key U hpU, key V hpV]
      have hw := add_self_zero
        (((singularHomology 0).map (ptTo p)).hom ((eps (TopCat.of ↥U)).hom a0))
      calc _ = (((singularHomology 0).map (incl U)).hom a0 +
            ((singularHomology 0).map (incl V)).hom b0) +
            (((singularHomology 0).map (ptTo p)).hom ((eps (TopCat.of ↥U)).hom a0) +
              ((singularHomology 0).map (ptTo p)).hom ((eps (TopCat.of ↥U)).hom a0)) := by abel
        _ = z := by rw [hw, add_zero, hz0]
  · have hab' : ((singularHomology 0).map (incl U)).hom a =
        ((singularHomology 0).map (incl V)).hom b := by
      rw [← Excision.sub_eq_add''] at hab
      exact sub_eq_zero.1 hab
    obtain ⟨c, hc1, hc2⟩ := (bp_gluing _ _ _ _ (h2 0) a b).2 hab'
    refine ⟨c, ?_, hc1, hc2⟩
    rw [← eps_nat (inclSub (Set.inter_subset_left : U ∩ V ⊆ U)) c, hc1]
    exact ha

end Absolute


section Relative

open DGPS.Topology

variable {X : TopCat.{0}}

lemma ses_surj {S : ShortComplex CC} (hS : S.ShortExact) (n : ℕ) :
    Function.Surjective (S.g.f n).hom := by
  have h := hS.epi_g
  have : Epi (S.g.f n) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

lemma ses_ker {S : ShortComplex CC} (hS : S.ShortExact) (n : ℕ) (z : S.X₂.X n)
    (hz : (S.g.f n).hom z = 0) : ∃ w : S.X₁.X n, (S.f.f n).hom w = z := by
  have h := (hS.map_of_exact (HomologicalComplex.eval _ _ n)).exact
  exact (ShortComplex.moduleCat_exact_iff _).1 h z hz

lemma mono_smallChains_inclusion {X : TopCat.{0}} (W : Set (Set X)) :
    Mono (SmallChains.smallChains_inclusion W) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ =>
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective)

lemma mono_map_incl (S : Set X) : Mono (singularChains.map (incl S)) :=
  HomologicalComplex.mono_of_mono_f _ (fun n =>
    (ModuleCat.mono_iff_injective _).2 (chain_inj _ (incl_emb S).injective n))

/-- The cover `{P, Q}` of `P ∪ Q`, as subsets of the subspace. -/
abbrev coverY (P Q : Set X) : Set (Set (TopCat.of ↥(P ∪ Q))) :=
  {{y | y.1 ∈ P}, {y | y.1 ∈ Q}}

/-- The inclusion of `P`-small and `Q`-small chains of `P ∪ Q` into the chains of `X`. -/
noncomputable def fSmall (P Q : Set X) :
    SmallChains.smallChains (coverY P Q) ⟶ singularChains.obj X :=
  SmallChains.smallChains_inclusion (coverY P Q) ≫ singularChains.map (incl (P ∪ Q))

instance (P Q : Set X) : Mono (fSmall P Q) := by
  have := mono_smallChains_inclusion (coverY P Q)
  have := mono_map_incl (P ∪ Q)
  unfold fSmall
  infer_instance

/-- The quotient `C(X) / (C(P) + C(Q))`. -/
noncomputable abbrev Fq (P Q : Set X) : CC := cokernel (fSmall P Q)

/-- The quotient map `C(X) ⟶ C(X) / (C(P) + C(Q))`. -/
noncomputable abbrev πF (P Q : Set X) : singularChains.obj X ⟶ Fq P Q := cokernel.π (fSmall P Q)

theorem fSmall_shortExact (P Q : Set X) :
    (ShortComplex.mk (fSmall P Q) (πF P Q) (cokernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

lemma map_smallSub_Y {S T : Set X} (h : S ⊆ T) (n : ℕ) :
    Submodule.map ((singularChains.map (incl T)).f n).hom
      (SmallChains.smallSub (TopCat.of ↥T) {{y : TopCat.of ↥T | y.1 ∈ S}} n) =
      SmallChains.smallSub X {S} n := by
  rw [← range_inclSub_eq h, ← LinearMap.range_comp, ← range_incl_eq]
  congr 1
  apply LinearMap.ext
  intro z
  exact comp_incl_apply h n z

lemma hF_ker (P Q : Set X) (n : ℕ) (z : (singularChains.obj X).X n) :
    ((πF P Q).f n).hom z = 0 ↔
      z ∈ SmallChains.smallSub X {P} n ⊔ SmallChains.smallSub X {Q} n := by
  have hsub : Submodule.map ((singularChains.map (incl (P ∪ Q))).f n).hom
      (SmallChains.smallSub (TopCat.of ↥(P ∪ Q)) (coverY P Q) n) =
      SmallChains.smallSub X {P} n ⊔ SmallChains.smallSub X {Q} n := by
    rw [smallSub_pair, Submodule.map_sup, map_smallSub_Y Set.subset_union_left,
      map_smallSub_Y Set.subset_union_right]
  rw [← hsub]
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := ses_ker (fSmall_shortExact P Q) n z hz
    exact ⟨w.1, w.2, hw⟩
  · rintro ⟨y, hy, rfl⟩
    have h := congr($(HomologicalComplex.congr_hom (cokernel.condition (fSmall P Q)) n) ⟨y, hy⟩)
    exact h


/-- The map of pairs `(X, S) ⟶ (X, T)` for `S ⊆ T`. -/
noncomputable def relPairMap {S T : Set X} (h : S ⊆ T) :
    TopPair.ofSet X S ⟶ TopPair.ofSet X T :=
  TopPair.homMk (inclSub h) (𝟙 X) (by ext x; rfl)

lemma rel_map_π {S T : Set X} (h : S ⊆ T) (n : ℕ) (z : (singularChains.obj X).X n) :
    ((relativeChains.map (relPairMap h)).f n).hom
      (((relativeChainsπ (TopPair.ofSet X S)).f n).hom z) =
      ((relativeChainsπ (TopPair.ofSet X T)).f n).hom z := by
  have h' := congr($(HomologicalComplex.congr_hom
    (relativeChainsπ_naturality (relPairMap h)) n) z)
  have h0 : ((singularChains.map (relPairMap h).right).f n).hom z = z :=
    congr($(HomologicalComplex.congr_hom (singularChains.map_id X) n) z)
  have h1 : ((relativeChainsπ (TopPair.ofSet X T)).f n).hom
      (((singularChains.map (relPairMap h).right).f n).hom z) =
      ((relativeChains.map (relPairMap h)).f n).hom
      (((relativeChainsπ (TopPair.ofSet X S)).f n).hom z) := h'
  rw [h0] at h1
  exact h1.symm

lemma epi_relπ (S : Set X) : Epi (relativeChainsπ (TopPair.ofSet X S)) :=
  (pairShortComplex_shortExact (TopPair.ofSet X S)).epi_g

/-- The map `C(X, S) ⟶ C(X) / (C(P) + C(Q))`. -/
noncomputable def relToF (P Q S : Set X)
    (hle : ∀ n, SmallChains.smallSub X {S} n ≤
      SmallChains.smallSub X {P} n ⊔ SmallChains.smallSub X {Q} n) :
    relativeChains.obj (TopPair.ofSet X S) ⟶ Fq P Q :=
  have : Epi (pairShortComplex (TopPair.ofSet X S)).g := epi_relπ S
  (pairShortComplex_shortExact (TopPair.ofSet X S)).exact.desc (πF P Q) (by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    ext x
    have hx : ((singularChains.map (incl S)).f n).hom x ∈ SmallChains.smallSub X {S} n := by
      rw [← range_incl_eq]; exact ⟨x, rfl⟩
    exact (hF_ker P Q n _).2 (hle n hx))

lemma relToF_π (P Q S : Set X)
    (hle : ∀ n, SmallChains.smallSub X {S} n ≤
      SmallChains.smallSub X {P} n ⊔ SmallChains.smallSub X {Q} n) (n : ℕ)
    (z : (singularChains.obj X).X n) :
    ((relToF P Q S hle).f n).hom (((relativeChainsπ (TopPair.ofSet X S)).f n).hom z) =
      ((πF P Q).f n).hom z := by
  have : Epi (pairShortComplex (TopPair.ofSet X S)).g := epi_relπ S
  have h : relativeChainsπ (TopPair.ofSet X S) ≫ relToF P Q S hle = πF P Q :=
    (pairShortComplex_shortExact (TopPair.ofSet X S)).exact.g_desc _ _
  exact congr($(HomologicalComplex.congr_hom h n) z)

lemma relπ_ker (S : Set X) (n : ℕ) (z : (singularChains.obj X).X n) :
    ((relativeChainsπ (TopPair.ofSet X S)).f n).hom z = 0 ↔
      z ∈ SmallChains.smallSub X {S} n := by
  have h := Excision.rel_ker_iff (TopPair.ofSet X S) (incl_emb S) n z
  have hr : Set.range (TopPair.ofSet X S).hom.hom = S := incl_range S
  rw [hr] at h
  exact h

lemma relπ_surj (S : Set X) (n : ℕ) (y : (relativeChains.obj (TopPair.ofSet X S)).X n) :
    ∃ z : (singularChains.obj X).X n,
      ((relativeChainsπ (TopPair.ofSet X S)).f n).hom z = y :=
  ses_surj (pairShortComplex_shortExact (TopPair.ofSet X S)) n y

lemma relπ_sub (S : Set X) (n : ℕ) (x p : (singularChains.obj X).X n) :
    ((relativeChainsπ (TopPair.ofSet X S)).f n).hom (x - p) =
      ((relativeChainsπ (TopPair.ofSet X S)).f n).hom x -
        ((relativeChainsπ (TopPair.ofSet X S)).f n).hom p :=
  map_sub ((relativeChainsπ (TopPair.ofSet X S)).f n).hom x p

lemma relπ_add (S : Set X) (n : ℕ) (x p : (singularChains.obj X).X n) :
    ((relativeChainsπ (TopPair.ofSet X S)).f n).hom (x + p) =
      ((relativeChainsπ (TopPair.ofSet X S)).f n).hom x +
        ((relativeChainsπ (TopPair.ofSet X S)).f n).hom p :=
  map_add ((relativeChainsπ (TopPair.ofSet X S)).f n).hom x p

lemma πF_surj (P Q : Set X) (n : ℕ) : Function.Surjective ((πF P Q).f n).hom :=
  ses_surj (fSmall_shortExact P Q) n

theorem rel_hyp (P Q : Set X)
    (h1 : ∀ n, SmallChains.smallSub X {P} n ≤
      SmallChains.smallSub X {P} n ⊔ SmallChains.smallSub X {Q} n)
    (h2 : ∀ n, SmallChains.smallSub X {Q} n ≤
      SmallChains.smallSub X {P} n ⊔ SmallChains.smallSub X {Q} n) :
    MVHyp (relativeChains.map (relPairMap (Set.inter_subset_left : P ∩ Q ⊆ P)))
      (relativeChains.map (relPairMap (Set.inter_subset_right : P ∩ Q ⊆ Q)))
      (relToF P Q P h1) (relToF P Q Q h2) where
  comm n c := by
    obtain ⟨z, rfl⟩ := relπ_surj (P ∩ Q) n c
    rw [rel_map_π, rel_map_π, relToF_π, relToF_π]
  inj n c hc1 hc2 := by
    obtain ⟨z, rfl⟩ := relπ_surj (P ∩ Q) n c
    rw [rel_map_π, relπ_ker] at hc1 hc2
    rw [relπ_ker]
    exact Excision.inter_smallSub P Q n z hc1 hc2
  mid n a b hab := by
    obtain ⟨x, rfl⟩ := relπ_surj P n a
    obtain ⟨y, rfl⟩ := relπ_surj Q n b
    rw [relToF_π, relToF_π] at hab
    have hxy : ((πF P Q).f n).hom (x - y) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 ((hF_ker P Q n _).1 hxy)
    refine ⟨((relativeChainsπ (TopPair.ofSet X (P ∩ Q))).f n).hom (x - p), ?_, ?_⟩
    · rw [rel_map_π, relπ_sub, (relπ_ker P n p).2 hp, sub_zero]
    · have hw : x - p = y + q := by
        have : x - y = p + q := hpq.symm
        calc x - p = (x - y) - p + y := by abel
          _ = y + q := by rw [this]; abel
      rw [rel_map_π, hw, relπ_add, (relπ_ker Q n q).2 hq, add_zero]
  surj n s := by
    obtain ⟨z, rfl⟩ := πF_surj P Q n s
    refine ⟨((relativeChainsπ (TopPair.ofSet X P)).f n).hom z, 0, ?_⟩
    rw [relToF_π, map_zero, add_zero]

/-- The comparison map `C(X) / (C(P) + C(Q)) ⟶ C(X, P ∪ Q)`. -/
noncomputable def phiF (P Q : Set X) : Fq P Q ⟶ relativeChains.obj (TopPair.ofSet X (P ∪ Q)) :=
  (fSmall_shortExact P Q).exact.desc (relativeChainsπ (TopPair.ofSet X (P ∪ Q))) (by
    refine (Category.assoc _ _ _).trans ?_
    erw [relativeChains_condition (TopPair.ofSet X (P ∪ Q))]
    exact comp_zero)

lemma πF_phiF (P Q : Set X) :
    πF P Q ≫ phiF P Q = relativeChainsπ (TopPair.ofSet X (P ∪ Q)) :=
  (fSmall_shortExact P Q).exact.g_desc _ _

theorem quasiIso_phiF (P Q : Set X) (hP : IsOpen P) (hQ : IsOpen Q) : QuasiIso (phiF P Q) := by
  let φ : ShortComplex.mk (fSmall P Q) (πF P Q) (cokernel.condition _) ⟶
      pairShortComplex (TopPair.ofSet X (P ∪ Q)) :=
    ShortComplex.homMk (SmallChains.smallChains_inclusion (coverY P Q)) (𝟙 _) (phiF P Q)
      (by simp [fSmall]; rfl) (by exact (Category.id_comp _).trans (πF_phiF P Q).symm)
  have hopen : ∀ A ∈ coverY P Q, IsOpen A := by
    intro A hA
    rcases hA with rfl | hA
    · exact hP.preimage continuous_subtype_val
    · rw [Set.mem_singleton_iff] at hA; subst hA; exact hQ.preimage continuous_subtype_val
  have hc : ⋃₀ coverY P Q = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    rcases y.2 with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have h1 : QuasiIso φ.τ₁ :=
    inferInstanceAs (QuasiIso (Excision.smallChainsHomotopyEquiv _ hopen hc).hom)
  have h2 : QuasiIso φ.τ₂ := by
    show QuasiIso (𝟙 (singularChains.obj X))
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ (fSmall_shortExact P Q)
    (pairShortComplex_shortExact _) h1 h2


lemma relToF_phiF (P Q S : Set X) (hS : S ⊆ P ∪ Q)
    (hle : ∀ n, SmallChains.smallSub X {S} n ≤
      SmallChains.smallSub X {P} n ⊔ SmallChains.smallSub X {Q} n) :
    relToF P Q S hle ≫ phiF P Q = relativeChains.map (relPairMap hS) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  ext y
  obtain ⟨z, rfl⟩ := relπ_surj S n y
  have h1 : (((relToF P Q S hle ≫ phiF P Q).f n).hom
      (((relativeChainsπ (TopPair.ofSet X S)).f n).hom z)) =
      ((phiF P Q).f n).hom (((relToF P Q S hle).f n).hom
        (((relativeChainsπ (TopPair.ofSet X S)).f n).hom z)) := rfl
  rw [h1, relToF_π]
  have h2 := congr($(HomologicalComplex.congr_hom (πF_phiF P Q) n) z)
  have h3 : ((relativeChainsπ (TopPair.ofSet X (P ∪ Q))).f n).hom z =
      ((phiF P Q).f n).hom (((πF P Q).f n).hom z) := h2.symm
  rw [← rel_map_π hS n z] at h3
  exact h3.symm

theorem relative_mv_general (P Q : Set X) (hP : IsOpen P) (hQ : IsOpen Q) :
    ∃ δ : ∀ n : ℕ, (relativeHomology (n + 1)).obj (TopPair.ofSet X (P ∪ Q)) ⟶
        (relativeHomology n).obj (TopPair.ofSet X (P ∩ Q)),
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (biprod.lift
        ((relativeHomology n).map (relPairMap (Set.inter_subset_left : P ∩ Q ⊆ P)))
        ((relativeHomology n).map (relPairMap (Set.inter_subset_right : P ∩ Q ⊆ Q)))).hom) ∧
      (∀ n, LinearMap.range (biprod.lift
        ((relativeHomology n).map (relPairMap (Set.inter_subset_left : P ∩ Q ⊆ P)))
        ((relativeHomology n).map (relPairMap (Set.inter_subset_right : P ∩ Q ⊆ Q)))).hom =
        LinearMap.ker (biprod.desc
          ((relativeHomology n).map (relPairMap (Set.subset_union_left : P ⊆ P ∪ Q)))
          ((relativeHomology n).map (relPairMap (Set.subset_union_right : Q ⊆ P ∪ Q)))).hom) ∧
      (∀ n, LinearMap.range (biprod.desc
          ((relativeHomology (n + 1)).map (relPairMap (Set.subset_union_left : P ⊆ P ∪ Q)))
          ((relativeHomology (n + 1)).map (relPairMap (Set.subset_union_right : Q ⊆ P ∪ Q)))).hom =
        LinearMap.ker (δ n).hom) := by
  have := quasiIso_phiF P Q hP hQ
  obtain ⟨δ, h1, h2, h3⟩ := mv_exact_aux (rel_hyp P Q (fun _ => le_sup_left) (fun _ => le_sup_right))
    (phiF P Q)
  have e1 := relToF_phiF P Q P Set.subset_union_left (fun _ => le_sup_left)
  have e2 := relToF_phiF P Q Q Set.subset_union_right (fun _ => le_sup_right)
  rw [e1, e2] at h2 h3
  exact ⟨δ, h1, h2, h3⟩

end Relative


section Final

open DGPS.Topology

variable {X : TopCat.{0}}

/-- Local homology `H_n(X, X \ K; F2)`. -/
noncomputable abbrev localHomology (K : Set X) (n : ℕ) : F2Mod :=
  (relativeHomology n).obj (TopPair.ofSet X Kᶜ)

/-- Restriction `H_n(X, X \ L) ⟶ H_n(X, X \ K)` for `K ⊆ L`. -/
noncomputable abbrev localRestrict {K L : Set X} (h : K ⊆ L) (n : ℕ) :
    localHomology L n ⟶ localHomology K n :=
  (relativeHomology n).map (relPairMap (Set.compl_subset_compl.2 h))

theorem relative_mv_gen2 (P Q W Z : Set X) (hP : IsOpen P) (hQ : IsOpen Q)
    (hW : W = P ∩ Q) (hZ : Z = P ∪ Q) (hWP : W ⊆ P) (hWQ : W ⊆ Q) (hPZ : P ⊆ Z) (hQZ : Q ⊆ Z) :
    ∃ δ : ∀ n : ℕ, (relativeHomology (n + 1)).obj (TopPair.ofSet X Z) ⟶
        (relativeHomology n).obj (TopPair.ofSet X W),
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (biprod.lift
        ((relativeHomology n).map (relPairMap hWP))
        ((relativeHomology n).map (relPairMap hWQ))).hom) ∧
      (∀ n, LinearMap.range (biprod.lift
        ((relativeHomology n).map (relPairMap hWP))
        ((relativeHomology n).map (relPairMap hWQ))).hom =
        LinearMap.ker (biprod.desc
          ((relativeHomology n).map (relPairMap hPZ))
          ((relativeHomology n).map (relPairMap hQZ))).hom) ∧
      (∀ n, LinearMap.range (biprod.desc
          ((relativeHomology (n + 1)).map (relPairMap hPZ))
          ((relativeHomology (n + 1)).map (relPairMap hQZ))).hom =
        LinearMap.ker (δ n).hom) := by
  subst hW hZ
  exact relative_mv_general P Q hP hQ

end Final

section Compact

open DGPS.Topology

variable {X : TopCat.{0}}

theorem relative_mv_compact [T2Space X] (A B : Set X) (hA : IsCompact A) (hB : IsCompact B) :
    ∃ δ : ∀ n : ℕ, localHomology (A ∩ B) (n + 1) ⟶ localHomology (A ∪ B) n,
      (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (biprod.lift
        (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n)
        (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n)).hom) ∧
      (∀ n, LinearMap.range (biprod.lift
        (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n)
        (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n)).hom =
        LinearMap.ker (biprod.desc
          (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) n)
          (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) n)).hom) ∧
      (∀ n, LinearMap.range (biprod.desc
          (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) (n + 1))
          (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) (n + 1))).hom =
        LinearMap.ker (δ n).hom) := by
  have hP : IsOpen Aᶜ := hA.isClosed.isOpen_compl
  have hQ : IsOpen Bᶜ := hB.isClosed.isOpen_compl
  exact relative_mv_gen2 Aᶜ Bᶜ (A ∪ B)ᶜ (A ∩ B)ᶜ hP hQ (Set.compl_union A B)
    (Set.compl_inter A B) (Set.compl_subset_compl.2 Set.subset_union_left)
    (Set.compl_subset_compl.2 Set.subset_union_right)
    (Set.compl_subset_compl.2 Set.inter_subset_left)
    (Set.compl_subset_compl.2 Set.inter_subset_right)

end Compact

end DGPS.Topology.MayerVietoris

namespace DGPS.Topology

open DGPS.Topology.MayerVietoris

/-- **Relative Mayer-Vietoris** for local homology of compact sets in a Hausdorff space (the
manifold hypothesis is not needed), together with the absolute Mayer-Vietoris sequence for an
open cover, including the reduced degree-zero form. -/
theorem relative_mayer_vietoris :
    (∀ (X : TopCat.{0}) [T2Space X] (A B : Set X), IsCompact A → IsCompact B →
      ∃ δ : ∀ n : ℕ, localHomology (A ∩ B) (n + 1) ⟶ localHomology (A ∪ B) n,
        (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (biprod.lift
          (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n)
          (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n)).hom) ∧
        (∀ n, LinearMap.range (biprod.lift
          (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n)
          (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n)).hom =
          LinearMap.ker (biprod.desc
            (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) n)
            (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) n)).hom) ∧
        (∀ n, LinearMap.range (biprod.desc
            (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) (n + 1))
            (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) (n + 1))).hom =
          LinearMap.ker (δ n).hom) ∧
        (∀ n, (∀ x : localHomology (A ∩ B) (n + 1), x = 0) →
          Function.Injective (biprod.lift
            (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n)
            (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n)).hom) ∧
        (∀ n (a : localHomology A n) (b : localHomology B n),
          (∃ c : localHomology (A ∪ B) n,
            (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n).hom c = a ∧
            (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n).hom c = b) ↔
          (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) n).hom a =
            (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) n).hom b)) ∧
    (∀ (Y : TopCat.{0}) (U V : Set Y), IsOpen U → IsOpen V → U ∪ V = Set.univ →
      (∃ δ : ∀ n : ℕ, (singularHomology (n + 1)).obj Y ⟶
          (singularHomology n).obj (TopCat.of ↥(U ∩ V)),
        (∀ n, LinearMap.range (δ n).hom = LinearMap.ker (biprod.lift
          ((singularHomology n).map (inclSub (Set.inter_subset_left : U ∩ V ⊆ U)))
          ((singularHomology n).map (inclSub (Set.inter_subset_right : U ∩ V ⊆ V)))).hom) ∧
        (∀ n, LinearMap.range (biprod.lift
          ((singularHomology n).map (inclSub (Set.inter_subset_left : U ∩ V ⊆ U)))
          ((singularHomology n).map (inclSub (Set.inter_subset_right : U ∩ V ⊆ V)))).hom =
          LinearMap.ker (biprod.desc ((singularHomology n).map (incl U))
            ((singularHomology n).map (incl V))).hom) ∧
        (∀ n, LinearMap.range (biprod.desc ((singularHomology (n + 1)).map (incl U))
            ((singularHomology (n + 1)).map (incl V))).hom = LinearMap.ker (δ n).hom)) ∧
      Function.Surjective (biprod.desc ((singularHomology 0).map (incl U))
        ((singularHomology 0).map (incl V))).hom ∧
      ((U ∩ V).Nonempty →
        (∀ z : (singularHomology 0).obj Y, (eps Y).hom z = 0 →
          ∃ (a : (singularHomology 0).obj (TopCat.of ↥U))
            (b : (singularHomology 0).obj (TopCat.of ↥V)),
            (eps (TopCat.of ↥U)).hom a = 0 ∧ (eps (TopCat.of ↥V)).hom b = 0 ∧
            ((singularHomology 0).map (incl U)).hom a +
              ((singularHomology 0).map (incl V)).hom b = z) ∧
        (∀ (a : (singularHomology 0).obj (TopCat.of ↥U))
            (b : (singularHomology 0).obj (TopCat.of ↥V)),
          (eps (TopCat.of ↥U)).hom a = 0 → (eps (TopCat.of ↥V)).hom b = 0 →
          ((singularHomology 0).map (incl U)).hom a +
            ((singularHomology 0).map (incl V)).hom b = 0 →
          ∃ c : (singularHomology 0).obj (TopCat.of ↥(U ∩ V)),
            (eps (TopCat.of ↥(U ∩ V))).hom c = 0 ∧
            ((singularHomology 0).map (inclSub (Set.inter_subset_left : U ∩ V ⊆ U))).hom c = a ∧
            ((singularHomology 0).map (inclSub (Set.inter_subset_right : U ∩ V ⊆ V))).hom c = b))) := by
  refine ⟨fun X _ A B hA hB => ?_, fun Y U V hU hV hcov => ?_⟩
  · obtain ⟨δ, h1, h2, h3⟩ := relative_mv_compact A B hA hB
    refine ⟨δ, h1, h2, h3, fun n hz => ?_, fun n a b => bp_gluing _ _ _ _ (h2 n) a b⟩
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hmem : y ∈ LinearMap.ker (biprod.lift
        (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n)
        (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n)).hom := hy
    rw [← h1 n] at hmem
    obtain ⟨x, rfl⟩ := hmem
    rw [hz x, map_zero]
  · exact ⟨absolute_mv U V hU hV hcov, absolute_epi0 U V hU hV hcov,
      fun hne => reduced_deg0 U V hU hV hcov hne⟩

end DGPS.Topology
