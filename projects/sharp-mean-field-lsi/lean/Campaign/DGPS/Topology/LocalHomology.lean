import DGPS.Topology.MayerVietoris
import DGPS.Topology.ContractibleHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic

open CategoryTheory CategoryTheory.Limits

namespace DGPS.Topology.LocalHomology

open DGPS.Topology.MayerVietoris

/-- Five lemma for pairs: a map of pairs that is a quasi-isomorphism on both chain complexes
induces isomorphisms on relative homology. -/
theorem isIso_relativeHomology_of_quasiIso {P Q : TopPair} (f : P ⟶ Q)
    (h1 : QuasiIso (singularChains.map f.left)) (h2 : QuasiIso (singularChains.map f.right))
    (n : ℕ) : IsIso ((relativeHomology n).map f) := by
  have h3 := HomologicalComplex.HomologySequence.quasiIso_τ₃ (pairShortComplexMap f)
    (pairShortComplex_shortExact P) (pairShortComplex_shortExact Q) h1 h2
  exact (quasiIso_iff _ |>.1 h3 n |> (quasiIsoAt_iff_isIso_homologyMap _ _).1)

theorem quasiIso_of_isIso {X Y : TopCat.{0}} (f : X ⟶ Y) [IsIso f] :
    QuasiIso (singularChains.map f) := inferInstance

/-- A homotopy equivalence of spaces induces a quasi-isomorphism of singular chains. -/
theorem quasiIso_of_homotopy {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H1 : TopCat.Homotopy (f ≫ g) (𝟙 X)) (H2 : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    QuasiIso (singularChains.map f) := by
  have h1 := H1.singularChainComplexFunctorObjMap coeffModule
  have h2 := H2.singularChainComplexFunctorObjMap coeffModule
  have e1 : singularChains.map (f ≫ g) = singularChains.map f ≫ singularChains.map g :=
    singularChains.map_comp f g
  have e2 : singularChains.map (g ≫ f) = singularChains.map g ≫ singularChains.map f :=
    singularChains.map_comp g f
  have e3 : singularChains.map (𝟙 X) = 𝟙 (singularChains.obj X) := singularChains.map_id X
  have e4 : singularChains.map (𝟙 Y) = 𝟙 (singularChains.obj Y) := singularChains.map_id Y
  have h1' : Homotopy (singularChains.map f ≫ singularChains.map g) (𝟙 (singularChains.obj X)) := by
    rw [← e1, ← e3]; exact h1
  have h2' : Homotopy (singularChains.map g ≫ singularChains.map f) (𝟙 (singularChains.obj Y)) := by
    rw [← e2, ← e4]; exact h2
  let e : HomotopyEquiv (singularChains.obj X) (singularChains.obj Y) :=
    { hom := singularChains.map f
      inv := singularChains.map g
      homotopyHomInvId := h1'
      homotopyInvHomId := h2' }
  have : QuasiIso e.hom := HomotopyEquiv.quasiIso_hom e
  exact this


theorem quasiIso_of_contractible (X Y : TopCat.{0}) [ContractibleSpace X] [ContractibleSpace Y]
    (f : X ⟶ Y) : QuasiIso (singularChains.map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  cases n with
  | zero =>
    let cX : X ⟶ TopCat.of PUnit.{1} := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
    let cY : Y ⟶ TopCat.of PUnit.{1} := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
    have hX : IsIso ((singularHomology 0).map cX) := isIso_homology_toPoint_of_contractible X
    have hY : IsIso ((singularHomology 0).map cY) := isIso_homology_toPoint_of_contractible Y
    have hc : f ≫ cY = cX := by ext x
    have : IsIso ((singularHomology 0).map f ≫ (singularHomology 0).map cY) := by
      rw [← (singularHomology 0).map_comp, hc]; exact hX
    exact IsIso.of_isIso_comp_right ((singularHomology 0).map f) ((singularHomology 0).map cY)
  | succ m =>
    have hX := contractible_positive_degree_homology X (m + 1) (Nat.succ_pos m)
    have hY := contractible_positive_degree_homology Y (m + 1) (Nat.succ_pos m)
    have h : (singularHomology (m + 1)).map f = (hX.iso hY).hom := hX.eq_of_src _ _
    show IsIso ((singularHomology (m + 1)).map f)
    rw [h]; infer_instance


/-- If `X` and `X ∖ K` are contractible, all local homology groups `H_n(X, X ∖ K)` vanish. -/
theorem isZero_localHomology_of_contractible {X : TopCat.{0}} (K : Set X)
    [ContractibleSpace X] [hK : ContractibleSpace ↥Kᶜ] (n : ℕ) :
    IsZero (localHomology K n) := by
  have hq : QuasiIso (singularChains.map (TopPair.ofSet X Kᶜ).hom) :=
    quasiIso_of_contractible (TopCat.of ↥Kᶜ) X _
  have hac := (pairShortComplex_shortExact (TopPair.ofSet X Kᶜ)).acyclic_X₃ hq
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hac n)


/-- Mayer-Vietoris for two closed sets with acyclic local homology: the connecting map is an
isomorphism `H_{n+1}(X, X ∖ (A ∩ B)) ≅ H_n(X, X ∖ (A ∪ B))`. -/
theorem localHomology_mv_iso {X : TopCat.{0}} (A B S T : Set X) (hA : IsClosed A)
    (hB : IsClosed B) (hAB : A ∩ B = S) (hU : A ∪ B = T)
    (h0A : ∀ n, IsZero (localHomology A n)) (h0B : ∀ n, IsZero (localHomology B n)) (n : ℕ) :
    Nonempty (localHomology S (n + 1) ≅ localHomology T n) := by
  subst hAB hU
  obtain ⟨δ, h1, -, h3⟩ := relative_mv_gen2 Aᶜ Bᶜ (A ∪ B)ᶜ (A ∩ B)ᶜ hA.isOpen_compl hB.isOpen_compl
    (Set.compl_union A B) (Set.compl_inter A B)
    (Set.compl_subset_compl.2 Set.subset_union_left)
    (Set.compl_subset_compl.2 Set.subset_union_right)
    (Set.compl_subset_compl.2 Set.inter_subset_left)
    (Set.compl_subset_compl.2 Set.inter_subset_right)
  have hlift : biprod.lift (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) n)
      (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) n) = 0 := by
    apply biprod.hom_ext
    · exact (h0A n).eq_of_tgt _ _
    · exact (h0B n).eq_of_tgt _ _
  have hdesc : biprod.desc (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) (n + 1))
      (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) (n + 1)) = 0 := by
    apply biprod.hom_ext'
    · exact (h0A (n + 1)).eq_of_src _ _
    · exact (h0B (n + 1)).eq_of_src _ _
  have hs : Function.Surjective (δ n).hom := by
    rw [← LinearMap.range_eq_top, h1 n, hlift]
    simp
  have hi : Function.Injective (δ n).hom := by
    rw [← LinearMap.ker_eq_bot, ← h3 n, hdesc]
    simp
  exact ⟨(LinearEquiv.ofBijective (δ n).hom ⟨hi, hs⟩).toModuleIso⟩


/-- A slice inclusion with a retraction homotopic to the identity is a quasi-isomorphism. -/
theorem quasiIso_of_retract {Y Z : TopCat.{0}} (j : Y ⟶ Z) (π : Z ⟶ Y) (hπj : j ≫ π = 𝟙 Y)
    (H : TopCat.Homotopy (π ≫ j) (𝟙 Z)) :
    QuasiIso (singularChains.map j) := by
  refine quasiIso_of_homotopy j π ?_ H
  rw [hπj]
  exact ContinuousMap.Homotopy.refl _

section Slice

variable (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The closed ray `{0} × [0, ∞)`. -/
def rayPos : Set (F × ℝ) := {p | p.1 = 0 ∧ 0 ≤ p.2}

/-- The closed ray `{0} × (-∞, 0]`. -/
def rayNeg : Set (F × ℝ) := {p | p.1 = 0 ∧ p.2 ≤ 0}

/-- The line `{0} × ℝ`. -/
def axisLine : Set (F × ℝ) := {p | p.1 = 0}

omit [NormedSpace ℝ F] in
theorem isClosed_rayPos : IsClosed (rayPos F) :=
  (isClosed_eq continuous_fst continuous_const).inter (isClosed_le continuous_const continuous_snd)

omit [NormedSpace ℝ F] in
theorem isClosed_rayNeg : IsClosed (rayNeg F) :=
  (isClosed_eq continuous_fst continuous_const).inter (isClosed_le continuous_snd continuous_const)

omit [NormedSpace ℝ F] in
theorem rayPos_inter_rayNeg : rayPos F ∩ rayNeg F = {((0 : F), (0 : ℝ))} := by
  ext p
  simp only [rayPos, rayNeg, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Prod.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h4⟩; exact ⟨h1, le_antisymm h4 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.ge⟩, h1, h2.le⟩

omit [NormedSpace ℝ F] in
theorem rayPos_union_rayNeg : rayPos F ∪ rayNeg F = axisLine F := by
  ext p
  simp only [rayPos, rayNeg, axisLine, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h; rcases le_total 0 p.2 with h2 | h2
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr ⟨h, h2⟩

theorem starConvex_rayPos_compl : StarConvex ℝ ((0 : F), (-1 : ℝ)) (rayPos F)ᶜ := by
  intro y hy a b ha hb hab hmem
  simp only [rayPos, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le] at hy
  simp only [rayPos, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, zero_add, smul_eq_mul] at hmem
  obtain ⟨h1, h2⟩ := hmem
  have ha' : a = 1 - b := by linarith
  rcases hb.eq_or_lt with hb0 | hb0
  · subst ha'; rw [← hb0] at h2; norm_num at h2
  · have hy1 : y.1 = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact absurd h hb0.ne'
      · exact h
    have := hy hy1
    nlinarith

theorem starConvex_rayNeg_compl : StarConvex ℝ ((0 : F), (1 : ℝ)) (rayNeg F)ᶜ := by
  intro y hy a b ha hb hab hmem
  simp only [rayNeg, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_le] at hy
  simp only [rayNeg, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_zero, zero_add, smul_eq_mul] at hmem
  obtain ⟨h1, h2⟩ := hmem
  have ha' : a = 1 - b := by linarith
  rcases hb.eq_or_lt with hb0 | hb0
  · subst ha'; rw [← hb0] at h2; norm_num at h2
  · have hy1 : y.1 = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact absurd h hb0.ne'
      · exact h
    have := hy hy1
    nlinarith

theorem isZero_localHomology_rayPos (n : ℕ) :
    IsZero (localHomology (X := TopCat.of (F × ℝ)) (rayPos F) n) := by
  have : ContractibleSpace (TopCat.of (F × ℝ)) := inferInstanceAs (ContractibleSpace (F × ℝ))
  have : ContractibleSpace ↥((rayPos F)ᶜ) :=
    StarConvex.contractibleSpace (starConvex_rayPos_compl F) ⟨((0 : F), (-1 : ℝ)), by
      simp [rayPos]⟩
  exact isZero_localHomology_of_contractible (X := TopCat.of (F × ℝ)) (rayPos F) n

theorem isZero_localHomology_rayNeg (n : ℕ) :
    IsZero (localHomology (X := TopCat.of (F × ℝ)) (rayNeg F) n) := by
  have : ContractibleSpace (TopCat.of (F × ℝ)) := inferInstanceAs (ContractibleSpace (F × ℝ))
  have : ContractibleSpace ↥((rayNeg F)ᶜ) :=
    StarConvex.contractibleSpace (starConvex_rayNeg_compl F) ⟨((0 : F), (1 : ℝ)), by
      simp [rayNeg]⟩
  exact isZero_localHomology_of_contractible (X := TopCat.of (F × ℝ)) (rayNeg F) n

theorem localHomology_point_iso_axis (n : ℕ) :
    Nonempty (localHomology (X := TopCat.of (F × ℝ)) {((0 : F), (0 : ℝ))} (n + 1) ≅
      localHomology (X := TopCat.of (F × ℝ)) (axisLine F) n) :=
  localHomology_mv_iso (X := TopCat.of (F × ℝ)) (rayPos F) (rayNeg F) _ _ (isClosed_rayPos F)
    (isClosed_rayNeg F) (rayPos_inter_rayNeg F) (rayPos_union_rayNeg F)
    (isZero_localHomology_rayPos F) (isZero_localHomology_rayNeg F) n

end Slice

section OpenEmb

open DGPS.Topology.Excision

variable {Y X : TopCat.{0}}

/-- The map of pairs `(Y, Y ∖ K) ⟶ (X, X ∖ L)` induced by `e` when `e ⁻¹' L ⊆ K`. -/
noncomputable def setPairMap (e : Y ⟶ X) (K : Set Y) (L : Set X) (h : e ⁻¹' L ⊆ K) :
    TopPair.ofSet Y Kᶜ ⟶ TopPair.ofSet X Lᶜ :=
  TopPair.homMk
    (TopCat.ofHom (X := TopCat.of ↥Kᶜ) (Y := TopCat.of ↥Lᶜ)
      ⟨fun y => ⟨e y.1, fun hy => y.2 (h hy)⟩,
        Continuous.subtype_mk (e.hom.continuous.comp continuous_subtype_val) _⟩) e
    (by ext y; rfl)

/-- Excision for open embeddings: if `e : Y ⟶ X` is an open embedding with `e ⁻¹' L = K` and
`closure L ⊆ range e`, then `e` induces an isomorphism `H_n(Y, Y ∖ K) ≅ H_n(X, X ∖ L)`. -/
theorem isIso_setPairMap (e : Y ⟶ X) (he : Topology.IsOpenEmbedding e.hom) (K : Set Y)
    (L : Set X) (hKL : e ⁻¹' L = K) (hcl : closure L ⊆ Set.range e.hom) (n : ℕ) :
    IsIso ((relativeHomology n).map (setPairMap e K L hKL.le)) := by
  set Z : Set X := (Set.range e.hom)ᶜ with hZ
  have hZc : IsClosed Z := he.isOpen_range.isClosed_compl
  have hZL : closure Z ⊆ interior Lᶜ := by
    rw [hZc.closure_eq, interior_compl]
    intro x hx hxc
    exact hx (hcl hxc)
  have hmem : ∀ y : Y, e y ∈ Zᶜ := fun y => not_not.2 ⟨y, rfl⟩
  let φ : TopPair.ofSet Y Kᶜ ⟶ pairP X Lᶜ Z :=
    TopPair.homMk
      (TopCat.ofHom (X := TopCat.of ↥Kᶜ) (Y := TopCat.of (exA X Lᶜ Z))
        ⟨fun y => ⟨⟨e y.1, hmem y.1⟩, fun hy => y.2 (hKL ▸ hy)⟩,
          Continuous.subtype_mk (Continuous.subtype_mk
            (e.hom.continuous.comp continuous_subtype_val) _) _⟩)
      (TopCat.ofHom (X := Y) (Y := exY X Z)
        ⟨fun y => ⟨e y, hmem y⟩, Continuous.subtype_mk e.hom.continuous _⟩)
      (by ext y; rfl)
  have hfac : setPairMap e K L hKL.le = φ ≫ excisionMap X Lᶜ Z := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y; rfl
    · ext y; rfl
  have h1 : IsIso φ.left := by
    rw [TopCat.isIso_iff_isHomeomorph, isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, ?_⟩
    · refine Topology.IsEmbedding.of_comp (φ.left.hom.continuous)
        (continuous_subtype_val.comp continuous_subtype_val)
        (g := fun z : exA X Lᶜ Z => (z.1.1 : X)) ?_
      exact he.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    · rintro ⟨⟨x, hx⟩, hxA⟩
      obtain ⟨y, rfl⟩ : x ∈ Set.range e.hom := not_not.1 hx
      exact ⟨⟨y, fun hy => hxA ((Set.ext_iff.1 hKL _).2 hy)⟩, rfl⟩
  have h2 : IsIso φ.right := by
    rw [TopCat.isIso_iff_isHomeomorph, isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, ?_⟩
    · refine Topology.IsEmbedding.of_comp (φ.right.hom.continuous) continuous_subtype_val
        (g := fun z : exY X Z => (z.1 : X)) ?_
      exact he.isEmbedding
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ : x ∈ Set.range e.hom := not_not.1 hx
      exact ⟨y, rfl⟩
  have h3 := isIso_relativeHomology_of_quasiIso φ (quasiIso_of_isIso _) (quasiIso_of_isIso _) n
  rw [hfac, Functor.map_comp]
  have := excision_iso X Lᶜ Z hZL n
  infer_instance

end OpenEmb

section SlicePair

variable (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The slice inclusion `F ⟶ F × ℝ`, `v ↦ (v, 0)`. -/
def sliceIncl : TopCat.of F ⟶ TopCat.of (F × ℝ) :=
  TopCat.ofHom ⟨fun v => (v, 0), by fun_prop⟩

/-- The projection `F × ℝ ⟶ F`. -/
def sliceProj : TopCat.of (F × ℝ) ⟶ TopCat.of F :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

omit [NormedSpace ℝ F] in
theorem quasiIso_sliceIncl : QuasiIso (singularChains.map (sliceIncl F)) := by
  refine quasiIso_of_retract (sliceIncl F) (sliceProj F) (by ext v; rfl) ?_
  exact
    { toFun := fun p => (p.2.1, (p.1 : ℝ) * p.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun x => by
        change ((x : F × ℝ).1, ((0 : unitInterval) : ℝ) * (x : F × ℝ).2) = ((x : F × ℝ).1, 0)
        simp
      map_one_left := fun x => by
        change ((x : F × ℝ).1, ((1 : unitInterval) : ℝ) * (x : F × ℝ).2) = x
        simp }

/-- The slice inclusion on subspaces: `S ⟶ T` where `T = S × ℝ`. -/
def subSliceIncl (S : Set F) (T : Set (F × ℝ)) (hT : ∀ p, p ∈ T ↔ p.1 ∈ S) :
    TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨fun v => ⟨(v.1, 0), (hT _).2 v.2⟩, by fun_prop⟩

/-- The projection on subspaces: `T ⟶ S`. -/
def subSliceProj (S : Set F) (T : Set (F × ℝ)) (hT : ∀ p, p ∈ T ↔ p.1 ∈ S) :
    TopCat.of T ⟶ TopCat.of S :=
  TopCat.ofHom ⟨fun p => ⟨p.1.1, (hT _).1 p.2⟩, by fun_prop⟩

omit [NormedSpace ℝ F] in
theorem quasiIso_subSliceIncl (S : Set F) (T : Set (F × ℝ)) (hT : ∀ p, p ∈ T ↔ p.1 ∈ S) :
    QuasiIso (singularChains.map (subSliceIncl F S T hT)) := by
  refine quasiIso_of_retract (subSliceIncl F S T hT) (subSliceProj F S T hT) (by ext v; rfl) ?_
  exact
    { toFun := fun p => ⟨(p.2.1.1, (p.1 : ℝ) * p.2.1.2), (hT _).2 ((hT p.2.1).1 p.2.2)⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x => by
        apply Subtype.ext
        change ((x : T).1.1, ((0 : unitInterval) : ℝ) * (x : T).1.2) = ((x : T).1.1, 0)
        simp
      map_one_left := fun x => by
        apply Subtype.ext
        change ((x : T).1.1, ((1 : unitInterval) : ℝ) * (x : T).1.2) = (x : T).1
        simp }

omit [NormedSpace ℝ F] in
/-- Local homology of the axis in `F × ℝ` is local homology of the origin in `F`. -/
theorem localHomology_slice_iso (k : ℕ) :
    Nonempty (localHomology (X := TopCat.of (F × ℝ)) (axisLine F) k ≅
      localHomology (X := TopCat.of F) {(0 : F)} k) := by
  have hle : (sliceIncl F) ⁻¹' (axisLine F) ⊆ {(0 : F)} := fun v hv => hv
  have h := isIso_relativeHomology_of_quasiIso
    (setPairMap (sliceIncl F) {(0 : F)} (axisLine F) hle)
    (quasiIso_subSliceIncl F {(0 : F)}ᶜ (axisLine F)ᶜ (fun p => Iff.rfl))
    (quasiIso_sliceIncl F) k
  exact ⟨(asIso ((relativeHomology k).map (setPairMap (sliceIncl F) {(0 : F)} (axisLine F) hle))).symm⟩

end SlicePair

section Points

variable {Y X : TopCat.{0}}

/-- The map of pairs `(Y, Y ∖ {y}) ⟶ (X, X ∖ {e y})` induced by an injective map. -/
noncomputable def pointPairMap (e : Y ⟶ X) (he : Function.Injective e.hom) (y : Y) :
    TopPair.ofSet Y {y}ᶜ ⟶ TopPair.ofSet X {e y}ᶜ :=
  setPairMap e {y} {e y} (fun _ h => he h)

theorem isIso_pointPairMap [T1Space X] (e : Y ⟶ X) (he : Topology.IsOpenEmbedding e.hom) (y : Y)
    (n : ℕ) : IsIso ((relativeHomology n).map (pointPairMap e he.injective y)) :=
  isIso_setPairMap e he {y} {e y}
    (by ext a; simp [he.injective.eq_iff]) (by rw [isClosed_singleton.closure_eq]; simp) n

theorem localHomology_point_iso [T1Space X] (e : Y ⟶ X) (he : Topology.IsOpenEmbedding e.hom)
    (y : Y) (k : ℕ) :
    Nonempty (localHomology (X := Y) {y} k ≅ localHomology (X := X) {e y} k) :=
  haveI := isIso_pointPairMap e he y k
  ⟨asIso ((relativeHomology k).map (pointPairMap e he.injective y))⟩

/-- The local homology profile at a point: `H_n(X, X ∖ {x}; F2)` is one-dimensional and
`H_i(X, X ∖ {x}; F2)` vanishes for `i > n`. -/
def LocalProfile (X : TopCat.{0}) (x : X) (n : ℕ) : Prop :=
  Module.rank F2 (localHomology (X := X) {x} n) = 1 ∧
    ∀ i, n < i → Limits.IsZero (localHomology (X := X) {x} i)

theorem LocalProfile.of_iso {X' : TopCat.{0}} {x : X} {x' : X'} {n : ℕ}
    (h : ∀ k, Nonempty (localHomology (X := X) {x} k ≅ localHomology (X := X') {x'} k))
    (hp : LocalProfile X x n) : LocalProfile X' x' n := by
  refine ⟨?_, fun i hi => ?_⟩
  · obtain ⟨e⟩ := h n
    rw [← e.toLinearEquiv.rank_eq]
    exact hp.1
  · obtain ⟨e⟩ := h i
    exact Limits.IsZero.of_iso (hp.2 i hi) e.symm

theorem localProfile_of_subsingleton (X : TopCat.{0}) [Nonempty X] [Subsingleton X] (x : X) :
    LocalProfile X x 0 := by
  have hE : IsEmpty ↥({x}ᶜ : Set X) := ⟨fun z => z.2 (Subsingleton.elim _ _)⟩
  have hiso : ∀ k, Nonempty (localHomology (X := X) {x} k ≅ (singularHomology k).obj X) := by
    intro k
    have : IsEmpty (TopPair.ofSet X {x}ᶜ).left := hE
    have := isIso_relativeChainsπ_of_isEmpty (TopPair.ofSet X {x}ᶜ)
    exact ⟨((HomologicalComplex.homologyFunctor F2Mod (ComplexShape.down ℕ) k).mapIso
      (asIso (relativeChainsπ (TopPair.ofSet X {x}ᶜ)))).symm⟩
  refine ⟨?_, fun i hi => ?_⟩
  · obtain ⟨e⟩ := hiso 0
    rw [e.toLinearEquiv.rank_eq]
    have hpc : PathConnectedSpace X := inferInstance
    have : IsIso (TopCat.singularHomology₀ε X coeffModule) := inferInstance
    let e2 : (singularHomology 0).obj X ≅ coeffModule :=
      @asIso _ _ _ _ (TopCat.singularHomology₀ε X coeffModule) this
    rw [e2.toLinearEquiv.rank_eq]
    exact Module.rank_self F2
  · obtain ⟨e⟩ := hiso i
    exact Limits.IsZero.of_iso (contractible_positive_degree_homology X i hi) e

theorem LocalProfile.iff_of_openEmbedding [T1Space X] (e : Y ⟶ X)
    (he : Topology.IsOpenEmbedding e.hom) (y : Y) (n : ℕ) :
    LocalProfile Y y n ↔ LocalProfile X (e y) n :=
  ⟨LocalProfile.of_iso (fun k => localHomology_point_iso e he y k),
    LocalProfile.of_iso (fun k => (localHomology_point_iso e he y k).map Iso.symm)⟩

theorem localProfile_of_homeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [T1Space B] (h : A ≃ₜ B) (a : A) (n : ℕ) (hp : LocalProfile (TopCat.of A) a n) :
    LocalProfile (TopCat.of B) (h a) n :=
  (LocalProfile.iff_of_openEmbedding (X := TopCat.of B) (Y := TopCat.of A)
    (TopCat.ofHom ⟨h, h.continuous⟩) h.isOpenEmbedding a n).1 hp

theorem localProfile_prod (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (m : ℕ)
    (h : LocalProfile (TopCat.of F) (0 : F) m) :
    LocalProfile (TopCat.of (F × ℝ)) ((0 : F), (0 : ℝ)) (m + 1) := by
  have key : ∀ j, Nonempty (localHomology (X := TopCat.of (F × ℝ)) {((0 : F), (0 : ℝ))} (j + 1) ≅
      localHomology (X := TopCat.of F) {(0 : F)} j) := fun j => by
    obtain ⟨a⟩ := localHomology_point_iso_axis F j
    obtain ⟨b⟩ := localHomology_slice_iso F j
    exact ⟨a ≪≫ b⟩
  refine ⟨?_, fun i hi => ?_⟩
  · obtain ⟨e⟩ := key m
    rw [e.toLinearEquiv.rank_eq]
    exact h.1
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨e⟩ := key j
    exact Limits.IsZero.of_iso (h.2 j (by omega)) e

theorem localProfile_euclidean (n : ℕ) :
    LocalProfile (TopCat.of (EuclideanSpace ℝ (Fin n))) (0 : EuclideanSpace ℝ (Fin n)) n := by
  induction n with
  | zero =>
    exact localProfile_of_subsingleton (TopCat.of (EuclideanSpace ℝ (Fin 0))) 0
  | succ n ih =>
    have hp := localProfile_prod (EuclideanSpace ℝ (Fin n)) n ih
    let L : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
    have h2 := localProfile_of_homeo (B := EuclideanSpace ℝ (Fin (n + 1))) L.symm.toHomeomorph
      ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ)) (n + 1) hp
    have h0 : L.symm.toHomeomorph ((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ)) =
        (0 : EuclideanSpace ℝ (Fin (n + 1))) := by
      have : (((0 : EuclideanSpace ℝ (Fin n)), (0 : ℝ)) : EuclideanSpace ℝ (Fin n) × ℝ) = 0 := rfl
      rw [this]
      exact map_zero L.symm
    rw [h0] at h2
    exact h2

end Points

end DGPS.Topology.LocalHomology

namespace DGPS.Topology

open DGPS.Topology.LocalHomology

/-- Local profile of a boundaryless manifold at a point, via a chart. -/
theorem localProfile_manifold {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n) (x : M) :
    LocalProfile (TopCat.of M) x n := by
  have : T1Space M := I.t1Space M
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (hE ▸ hn)
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hE])
  let c := chartAt H x
  let p : E := I (c x)
  let g : E ≃ₜ EuclideanSpace ℝ (Fin n) := (Homeomorph.addRight (-p)).trans L.toHomeomorph
  let U : Set M := c.source
  let f : U → EuclideanSpace ℝ (Fin n) := fun u =>
    g (I.toHomeomorph ((c.toHomeomorphSourceTarget u).1))
  have hf : Topology.IsOpenEmbedding f := by
    have h1 : Topology.IsOpenEmbedding (fun t : c.target => (t : H)) :=
      c.open_target.isOpenEmbedding_subtypeVal
    exact g.isOpenEmbedding.comp (I.toHomeomorph.isOpenEmbedding.comp
      (h1.comp c.toHomeomorphSourceTarget.isOpenEmbedding))
  have hxU : x ∈ U := mem_chart_source H x
  have hf0 : f ⟨x, hxU⟩ = 0 := by
    simp [f, g, p, c, L]
  have hi : Topology.IsOpenEmbedding (Subtype.val : U → M) := c.open_source.isOpenEmbedding_subtypeVal
  have h0 := localProfile_euclidean n
  have h1 : LocalProfile (TopCat.of U) ⟨x, hxU⟩ n := by
    refine (LocalProfile.iff_of_openEmbedding (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
      (TopCat.ofHom ⟨f, hf.continuous⟩) hf ⟨x, hxU⟩ n).2 ?_
    have he : ((TopCat.ofHom ⟨f, hf.continuous⟩ : TopCat.of U ⟶ TopCat.of (EuclideanSpace ℝ (Fin n)))
        ⟨x, hxU⟩ : EuclideanSpace ℝ (Fin n)) = 0 := hf0
    rw [he]
    exact h0
  exact (LocalProfile.iff_of_openEmbedding (X := TopCat.of M) (Y := TopCat.of U)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) hi ⟨x, hxU⟩ n).1 h1

/-- Local homology of a boundaryless `n`-manifold (`n > 0`) at a point `x` with `F2` coefficients:
`H_n(M, M ∖ {x})` is one-dimensional, `H_i(M, M ∖ {x}) = 0` for `i > n`, and the pair map induced
by any open embedding `e : Y ⟶ M` (in particular a chart domain inclusion, composed with chart
homeomorphisms) is an isomorphism on relative homology in every degree. -/
theorem local_homology_in_a_chart {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n) (x : M) :
    Module.rank F2 ((relativeHomology n).obj (TopPair.ofSet (TopCat.of M) {x}ᶜ)) = 1 ∧
      (∀ i, n < i → Limits.IsZero ((relativeHomology i).obj (TopPair.ofSet (TopCat.of M) {x}ᶜ))) ∧
      ∀ (Y : TopCat.{0}) (e : Y ⟶ TopCat.of M) (he : Topology.IsOpenEmbedding e.hom) (y : Y)
        (i : ℕ), IsIso ((relativeHomology i).map (pointPairMap e he.injective y)) := by
  have : T1Space M := I.t1Space M
  have hp := localProfile_manifold I n hn hE x
  exact ⟨hp.1, hp.2, fun Y e he y i => isIso_pointPairMap e he y i⟩

end DGPS.Topology
