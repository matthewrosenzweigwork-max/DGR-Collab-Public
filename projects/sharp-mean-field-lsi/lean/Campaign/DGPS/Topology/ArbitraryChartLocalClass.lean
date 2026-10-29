import DGPS.Topology.FiniteUnionLocalClass

/-!
# Arbitrary compact sets in a chart: the local class (TOP011)

Extends TOP010 (`finite_union_local_class`) from finite unions of compact convex sets to an
arbitrary compact set `K0` of a chart `e : V ⟶ M` of an `n`-manifold (`n > 0`): `H_i(M, M ∖ e '' K0)`
vanishes for `i > n`, and every consistent local section over `e '' K0` is represented by a unique
class in `H_n(M, M ∖ e '' K0)`.

The proof follows Hatcher, Lemma 3.27.  A class of positive degree over `e '' K0` has a chain
representative supported in a compact set `C` disjoint from `e '' K0` (`lift_class_X`); a finite
cover of `K0` by small closed balls avoiding `e⁻¹ C` then lifts the class to a finite union of
closed balls (`lift_to_balls`), where TOP010 applies.  This gives vanishing and uniqueness.
Existence is obtained by Mayer-Vietoris gluing (`rep_union`) of local pieces `K0 ∩ closedBall x ρ`,
each of which carries a class by consistency of the section, using uniqueness over the (arbitrary
compact) overlaps.
-/

open CategoryTheory CategoryTheory.Limits

namespace DGPS.Topology.ArbitraryChartLocalClass

theorem exists_rep {R : Type} [Ring R] (S₂ : ShortComplex (ModuleCat.{0} R)) (q : S₂.homology) :
    ∃ y : S₂.X₂, S₂.g y = 0 ∧ ∀ {S₁ : ShortComplex (ModuleCat.{0} R)} (φ : S₁ ⟶ S₂)
      (x : S₁.X₂), S₁.g x = 0 → (∃ w : S₂.X₁, S₂.f w = φ.τ₂ x - y) →
        ∃ q₁ : S₁.homology, ShortComplex.homologyMap φ q₁ = q := by
  obtain ⟨⟨y, hy⟩, hyq⟩ := Submodule.Quotient.mk_surjective _
    (S₂.moduleCatLeftHomologyData.homologyIso.hom q)
  refine ⟨y, hy, fun {S₁} φ x hx ⟨w, hw⟩ => ?_⟩
  have c12 : ∀ w, φ.τ₂ (S₁.f w) = S₂.f (φ.τ₁ w) := fun w => by
    simpa using (congr($(φ.comm₁₂) w)).symm
  have c23 : ∀ x, S₂.g (φ.τ₂ x) = φ.τ₃ (S₁.g x) := fun x => by
    simpa using congr($(φ.comm₂₃) x)
  have hker : ∀ x ∈ LinearMap.ker S₁.g.hom, φ.τ₂.hom x ∈ LinearMap.ker S₂.g.hom := by
    intro x hx
    have h1 : S₁.g x = 0 := hx
    show S₂.g (φ.τ₂ x) = 0
    rw [c23, h1, map_zero]
  let φK : S₁.moduleCatLeftHomologyData.K ⟶ S₂.moduleCatLeftHomologyData.K :=
    ModuleCat.ofHom (φ.τ₂.hom.restrict hker)
  have hq : LinearMap.range S₁.moduleCatToCycles ≤
      (LinearMap.range S₂.moduleCatToCycles).comap φK.hom := by
    rintro _ ⟨w, rfl⟩
    refine ⟨φ.τ₁ w, ?_⟩
    apply Subtype.ext
    exact (c12 w).symm
  let γ : ShortComplex.LeftHomologyMapData φ S₁.moduleCatLeftHomologyData
      S₂.moduleCatLeftHomologyData :=
    { φK := φK
      φH := ModuleCat.ofHom (Submodule.mapQ _ _ φK.hom hq)
      commi := by ext x; rfl
      commf' := by
        ext x
        apply Subtype.ext
        exact (c12 x)
      commπ := by
        ext x
        rfl }
  refine ⟨S₁.moduleCatLeftHomologyData.homologyIso.inv (Submodule.Quotient.mk ⟨x, hx⟩), ?_⟩
  rw [γ.homologyMap_eq]
  simp only [ConcreteCategory.comp_apply]
  have e1 := Iso.inv_hom_id_apply S₁.moduleCatLeftHomologyData.homologyIso
    (Submodule.Quotient.mk ⟨x, hx⟩ : S₁.moduleCatLeftHomologyData.H)
  erw [e1]
  have h2 : γ.φH (Submodule.Quotient.mk ⟨x, hx⟩ : S₁.moduleCatLeftHomologyData.H) =
      (Submodule.Quotient.mk ⟨y, hy⟩ : S₂.moduleCatLeftHomologyData.H) := by
    show (Submodule.Quotient.mk (⟨φ.τ₂ x, hker x hx⟩ : LinearMap.ker S₂.g.hom) :
          S₂.moduleCatLeftHomologyData.H) = Submodule.Quotient.mk ⟨y, hy⟩
    rw [Submodule.Quotient.eq]
    exact ⟨w, Subtype.ext hw⟩
  rw [h2, hyq]
  exact Iso.hom_inv_id_apply _ _


open DGPS.Topology SmallChains Simplicial

lemma isCompact_range_simplex {X : TopCat.{0}} {m : ℕ} (σ : TopCat.toSSet.obj X _⦋m⦌) :
    IsCompact (Set.range (TopCat.toSSetObjEquiv X (Opposite.op ⦋m⦌) σ)) :=
  isCompact_range (TopCat.toSSetObjEquiv X (Opposite.op ⦋m⦌) σ).continuous

lemma exists_compact_support {X : TopCat.{0}} (S : Set X) (m : ℕ)
    (w : (singularChains.obj X).X m) (hw : w ∈ smallSub X {S} m) :
    ∃ C : Set X, IsCompact C ∧ C ⊆ S ∧ w ∈ smallSub X {C} m := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, ⟨B, hB, hs⟩, rfl⟩ := hx
    rw [Set.mem_singleton_iff] at hB
    subst hB
    exact ⟨_, isCompact_range_simplex σ, hs, gen_mem_smallSub ⟨_, rfl, subset_rfl⟩⟩
  | zero => exact ⟨∅, isCompact_empty, Set.empty_subset _, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1, s1, m1⟩ := hx
    obtain ⟨C2, h2, s2, m2⟩ := hy
    refine ⟨C1 ∪ C2, h1.union h2, Set.union_subset s1 s2, add_mem ?_ ?_⟩
    · exact Excision.smallSub_mono Set.subset_union_left m m1
    · exact Excision.smallSub_mono Set.subset_union_right m m2
  | smul a x _ hx =>
    obtain ⟨C1, h1, s1, m1⟩ := hx
    exact ⟨C1, h1, s1, Submodule.smul_mem _ _ m1⟩


open DGPS.Topology.MayerVietoris

/-- Chain-level lifting: a class of `H_{j+1}(X, X ∖ S)` comes from `H_{j+1}(X, X ∖ S')` for every
`S' ⊇ S` whose complement contains a fixed compact set `C ⊆ X ∖ S`. -/
lemma lift_class_X {X : TopCat.{0}} (S : Set X) (j : ℕ) (q : localHomology S (j + 1)) :
    ∃ C : Set X, IsCompact C ∧ C ⊆ Sᶜ ∧ ∀ (S' : Set X) (h : S ⊆ S'), C ⊆ S'ᶜ →
      ∃ q' : localHomology S' (j + 1), (localRestrict h (j + 1)).hom q' = q := by
  obtain ⟨y, hy, hlift⟩ := exists_rep ((relativeChains.obj (TopPair.ofSet X Sᶜ)).sc (j + 1)) q
  obtain ⟨z, hz⟩ := relπ_surj Sᶜ (j + 1) y
  have hdz : ((relativeChainsπ (TopPair.ofSet X Sᶜ)).f ((ComplexShape.down ℕ).next (j + 1))).hom
      (((singularChains.obj X).dFrom (j + 1)).hom z) = 0 := by
    have h := Excision.cf_from (relativeChainsπ (TopPair.ofSet X Sᶜ)) (j + 1) z
    exact h.symm.trans (hz ▸ hy)
  obtain ⟨C, hC, hCS, hCm⟩ := exists_compact_support Sᶜ _ _ ((relπ_ker Sᶜ _ _).1 hdz)
  refine ⟨C, hC, hCS, fun S' h hCS' => ?_⟩
  have hdz' : ((relativeChainsπ (TopPair.ofSet X S'ᶜ)).f ((ComplexShape.down ℕ).next (j + 1))).hom
      (((singularChains.obj X).dFrom (j + 1)).hom z) = 0 :=
    (relπ_ker S'ᶜ _ _).2 (Excision.smallSub_mono hCS' _ hCm)
  have hx : (relativeChains.obj (TopPair.ofSet X S'ᶜ)).dFrom (j + 1)
      (((relativeChainsπ (TopPair.ofSet X S'ᶜ)).f (j + 1)).hom z) = 0 := by
    have h := Excision.cf_from (relativeChainsπ (TopPair.ofSet X S'ᶜ)) (j + 1) z
    exact h.trans hdz'
  exact hlift ((HomologicalComplex.shortComplexFunctor _ _ (j + 1)).map
    (relativeChains.map (relPairMap (Set.compl_subset_compl.2 h))))
    (((relativeChainsπ (TopPair.ofSet X S'ᶜ)).f (j + 1)).hom z) hx ⟨0, by
      rw [map_zero]
      exact (sub_eq_zero.2 ((rel_map_π (Set.compl_subset_compl.2 h) (j + 1) z).trans hz)).symm⟩


open DGPS.Topology.LocalHomology DGPS.Topology.FiniteUnionLocalClass

section General

variable {X : TopCat.{0}}

/-- Uniqueness of classes with prescribed point restrictions. -/
def Uniq (n : ℕ) (S : Set X) : Prop :=
  ∀ c c' : localHomology S n,
    (∀ x (hx : x ∈ S), (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c =
      (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c') → c = c'

/-- A class over `S` with the prescribed point restrictions `s`. -/
def Rep (n : ℕ) (s : ∀ x : X, localHomology ({x} : Set X) n) (S : Set X) : Prop :=
  ∃ c : localHomology S n, ∀ x (hx : x ∈ S),
    (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c = s x

lemma rep_empty (n : ℕ) (s : ∀ x : X, localHomology ({x} : Set X) n) : Rep n s (∅ : Set X) :=
  ⟨0, fun x hx => absurd hx (by simp)⟩

lemma rep_union [T2Space X] {n : ℕ} {s : ∀ x : X, localHomology ({x} : Set X) n} {A B : Set X}
    (hA : IsCompact A) (hB : IsCompact B) (UAB : Uniq n (A ∩ B))
    (RA : Rep n s A) (RB : Rep n s B) : Rep n s (A ∪ B) := by
  obtain ⟨δ, h1, h2, h3, hinj, hglue⟩ := (relative_mayer_vietoris.1 X A B hA hB)
  obtain ⟨cA, hcA⟩ := RA
  obtain ⟨cB, hcB⟩ := RB
  have heq : (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) n).hom cA =
      (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) n).hom cB :=
    UAB _ _ (fun x hx => by
      rw [restrict_restrict, restrict_restrict, hcA x hx.1, hcB x hx.2])
  obtain ⟨c, hc1, hc2⟩ := (hglue n cA cB).2 heq
  refine ⟨c, fun x hx => ?_⟩
  rcases hx with hx | hx
  · rw [← hcA x hx, ← hc1, restrict_restrict]
  · rw [← hcB x hx, ← hc2, restrict_restrict]

end General


section Cover

variable {V : Type} [PseudoMetricSpace V]

lemma exists_ball_cover (K0 : Set V) (hK0 : IsCompact K0) (r : V → ℝ) (hr : ∀ x ∈ K0, 0 < r x) :
    ∃ t : Finset V, (∀ x ∈ t, x ∈ K0) ∧ K0 ⊆ ⋃ x ∈ t, Metric.ball x (r x) :=
  hK0.elim_nhds_subcover _ (fun x hx => Metric.ball_mem_nhds x (hr x hx))

end Cover

section Lift

variable {M : Type} [TopologicalSpace M] [T2Space M]
  {V : Type} [PseudoMetricSpace V] (e : TopCat.of V ⟶ TopCat.of M)

/-- Compactness lifting: a class of positive degree over `e '' K0` is the restriction of a class
over the image of a finite union of closed balls neighbouring `K0`. -/
lemma lift_to_balls (m : ℕ) (hm : 0 < m) (K0 : Set V) (hK0 : IsCompact K0)
    (q : localHomology (X := TopCat.of M) (e.hom '' K0) m) :
    ∃ (t : Finset V) (ρ : V → ℝ), K0 ⊆ (⋃ x ∈ t, Metric.ball x (ρ x)) ∧
      ∃ q' : localHomology (X := TopCat.of M) (e.hom '' (⋃ x ∈ t, Metric.closedBall x (ρ x))) m,
        ∀ h : K0 ⊆ ⋃ x ∈ t, Metric.closedBall x (ρ x),
          (localRestrict (X := TopCat.of M) (Set.image_mono h) m).hom q' = q := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨C, hCc, hCS, hlift⟩ := lift_class_X (e.hom '' K0) j q
  have hW : IsOpen (e.hom ⁻¹' Cᶜ) := hCc.isClosed.isOpen_compl.preimage e.hom.continuous
  have hr : ∀ x ∈ K0, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ e.hom ⁻¹' Cᶜ := fun x hx => by
    have hxW : x ∈ e.hom ⁻¹' Cᶜ := fun hxC => hCS hxC ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hW x hxW
    exact ⟨r, hr, hb⟩
  choose! r hrpos hrball using hr
  obtain ⟨t, htK, hcov⟩ := exists_ball_cover K0 hK0 (fun x => r x / 2)
    (fun x hx => half_pos (hrpos x hx))
  refine ⟨t, fun x => r x / 2, hcov, ?_⟩
  have hsub : (⋃ x ∈ t, Metric.closedBall x (r x / 2)) ⊆ e.hom ⁻¹' Cᶜ := by
    intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨x, hxt, hw⟩ := hw
    exact hrball x (htK x hxt) (lt_of_le_of_lt (Metric.mem_closedBall.1 hw)
      (by linarith [hrpos x (htK x hxt)]))
  have hK : K0 ⊆ ⋃ x ∈ t, Metric.closedBall x (r x / 2) :=
    hcov.trans (Set.iUnion₂_mono fun x _ => Metric.ball_subset_closedBall)
  obtain ⟨q', hq'⟩ := hlift (e.hom '' ⋃ x ∈ t, Metric.closedBall x (r x / 2))
    (Set.image_mono hK) (by
      rintro z hzC ⟨w, hw, rfl⟩
      exact hsub hw hzC)
  exact ⟨q', fun h => hq'⟩

end Lift

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
  (hE : Module.finrank ℝ E = n)
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (e : TopCat.of V ⟶ TopCat.of M) (he : Topology.IsOpenEmbedding e.hom)

include I hn hE he

omit [T2Space M] [I.Boundaryless] in
lemma properSpace_chart : ProperSpace V := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (hE ▸ hn)
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : LocallyCompactSpace V := he.locallyCompactSpace
  exact ProperSpace.of_locallyCompactSpace ℝ


variable [ProperSpace V]

lemma good_closedBalls (t : Finset V) (ρ : V → ℝ) :
    Good n (e.hom '' (⋃ x ∈ t, Metric.closedBall x (ρ x)) : Set (TopCat.of M)) := by
  classical
  have := good_finite_union I n hn hE e he (t.image fun x => Metric.closedBall x (ρ x))
    (fun A hA => by
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hA
      exact ⟨isCompact_closedBall _ _, convex_closedBall _ _⟩)
  rwa [Finset.set_biUnion_finset_image] at this

lemma vanish (K0 : Set V) (hK0 : IsCompact K0) (i : ℕ) (hi : n < i) :
    IsZero (localHomology (X := TopCat.of M) (e.hom '' K0) i) := by
  refine ModuleCat.isZero_iff_subsingleton.2 (subsingleton_of_forall_eq 0 fun a => ?_)
  obtain ⟨t, ρ, hcov, q', hq'⟩ := lift_to_balls e i (by omega) K0 hK0 a
  have hz := (good_closedBalls I n hn hE e he t ρ).1 i hi
  rw [← hq' (hcov.trans (Set.iUnion₂_mono fun x _ => Metric.ball_subset_closedBall)),
    elem_eq hz q' 0, map_zero]

lemma uniq_compact (K0 : Set V) (hK0 : IsCompact K0) :
    Uniq n (e.hom '' K0 : Set (TopCat.of M)) := by
  classical
  intro c c' hcc
  rw [← sub_eq_zero]
  obtain ⟨d, hd⟩ : ∃ d, d = c - c' := ⟨_, rfl⟩
  rw [← hd]
  have hd0 : ∀ x (hx : x ∈ e.hom '' K0),
      (localRestrict (Set.singleton_subset_iff.2 hx) n).hom d = 0 := by
    intro x hx
    rw [hd, map_sub, hcc x hx, sub_self]
  obtain ⟨t, ρ, hcov, d', hd'⟩ := lift_to_balls e n hn K0 hK0 d
  have hKP : K0 ⊆ ⋃ x ∈ t, Metric.closedBall x (ρ x) :=
    hcov.trans (Set.iUnion₂_mono fun x _ => Metric.ball_subset_closedBall)
  have hd'' := hd' hKP
  have hpt : ∀ x (hx : x ∈ e.hom '' K0) (hxP : x ∈ e.hom '' ⋃ x ∈ t, Metric.closedBall x (ρ x)),
      (localRestrict (Set.singleton_subset_iff.2 hxP) n).hom d' = 0 := by
    intro x hx hxP
    have h1 := restrict_restrict (Set.singleton_subset_iff.2 hx) (Set.image_mono hKP) n d'
    rw [hd''] at h1
    exact h1.symm.trans (hd0 x hx)
  have hloc : ∀ x ∈ K0, ∃ σ : ℝ, 0 < σ ∧
      Metric.closedBall x σ ⊆ ⋃ y ∈ t, Metric.closedBall y (ρ y) := by
    intro x hx
    have hx' := hcov hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨y, hyt, hxy⟩ := hx'
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball x hxy
    refine ⟨ε / 2, half_pos hε, fun z hz => ?_⟩
    have : z ∈ Metric.ball y (ρ y) :=
      hb (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) (by linarith))
    exact Set.mem_iUnion₂.2 ⟨y, hyt, Metric.ball_subset_closedBall this⟩
  choose! σ hσpos hσsub using hloc
  obtain ⟨t', ht'K, hcov'⟩ := exists_ball_cover K0 hK0 σ hσpos
  have hKK : K0 ⊆ ⋃ x ∈ t', Metric.closedBall x (σ x) :=
    hcov'.trans (Set.iUnion₂_mono fun x _ => Metric.ball_subset_closedBall)
  have hK''P : (⋃ x ∈ t', Metric.closedBall x (σ x)) ⊆ ⋃ x ∈ t, Metric.closedBall x (ρ x) :=
    Set.iUnion₂_subset fun x hx => hσsub x (ht'K x hx)
  obtain ⟨d'', hd''def⟩ : ∃ d'', d'' = (localRestrict (X := TopCat.of M)
    (Set.image_mono hK''P) n).hom d' := ⟨_, rfl⟩
  have hd''0 : d'' = 0 := by
    apply (good_closedBalls I n hn hE e he t' σ).2.1 d'' 0
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    simp only [Set.mem_iUnion] at hw
    obtain ⟨x, hxt', hwx⟩ := hw
    have hxK := ht'K x hxt'
    have hBsub := hσsub x hxK
    have hB'' : Metric.closedBall x (σ x) ⊆ ⋃ x ∈ t', Metric.closedBall x (σ x) :=
      Set.subset_biUnion_of_mem (u := fun x => Metric.closedBall x (σ x)) hxt'
    have hxB : x ∈ Metric.closedBall x (σ x) := Metric.mem_closedBall_self (hσpos x hxK).le
    have hdB : (localRestrict (X := TopCat.of M) (Set.image_mono hBsub) n).hom d' = 0 := by
      refine convex_inj I n hn hE e he (Metric.closedBall x (σ x)) (isCompact_closedBall _ _)
        (convex_closedBall _ _) ⟨x, hxB⟩ (x := e.hom x) ⟨x, hxB, rfl⟩ ?_
      rw [restrict_restrict, map_zero]
      exact hpt _ ⟨x, hxK, rfl⟩ ⟨x, hBsub hxB, rfl⟩
    have h2 := restrict_restrict (Set.image_mono hB'') (Set.image_mono hK''P) n d'
    rw [← hd''def] at h2
    have hwB : e.hom w ∈ e.hom '' Metric.closedBall x (σ x) := ⟨w, hwx, rfl⟩
    have h3 := restrict_restrict (Set.singleton_subset_iff.2 hwB) (Set.image_mono hB'') n d''
    rw [map_zero, ← h3, h2, hdB, map_zero]
  have h4 := restrict_restrict (Set.image_mono hKK) (Set.image_mono hK''P) n d'
  rw [← hd''def, hd''0, map_zero] at h4
  rw [← hd'']
  exact h4.symm

lemma rep_biUnion {ι : Type} [DecidableEq ι] (f : ι → Set V) (hf : ∀ i, IsCompact (f i))
    (s : ∀ x : TopCat.of M, localHomology ({x} : Set (TopCat.of M)) n) (t : Finset ι)
    (hrep : ∀ i ∈ t, Rep n s (e.hom '' f i)) : Rep n s (e.hom '' (⋃ i ∈ t, f i)) := by
  induction t using Finset.induction_on with
  | empty => simpa using rep_empty n s
  | insert a t hat ih =>
    rw [Finset.set_biUnion_insert, Set.image_union]
    have hcompf : IsCompact (⋃ i ∈ t, f i) :=
      t.finite_toSet.isCompact_biUnion fun i _ => hf i
    refine rep_union ((hf a).image e.hom.continuous) (hcompf.image e.hom.continuous) ?_
      (hrep a (Finset.mem_insert_self a t)) (ih fun i hi => hrep i (Finset.mem_insert_of_mem hi))
    rw [← Set.image_inter he.injective]
    exact uniq_compact I n hn hE e he _ ((hf a).inter_right hcompf.isClosed)

lemma exists_class (K0 : Set V) (hK0 : IsCompact K0)
    (s : ∀ x, x ∈ e.hom '' K0 → localHomology ({x} : Set (TopCat.of M)) n)
    (hs : IsConsistentSection n (e.hom '' K0 : Set (TopCat.of M)) s) :
    ∃ c : localHomology (X := TopCat.of M) (e.hom '' K0) n,
      ∀ x (hx : x ∈ e.hom '' K0),
        (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) n).hom c = s x hx := by
  classical
  let s' : ∀ x : TopCat.of M, localHomology ({x} : Set (TopCat.of M)) n :=
    fun x => if h : x ∈ e.hom '' K0 then s x h else 0
  have hpiece : ∀ x ∈ K0, ∃ ρ : ℝ, 0 < ρ ∧
      Rep n s' (e.hom '' (K0 ∩ Metric.closedBall x ρ)) := by
    intro x hx
    obtain ⟨U, hU, hxU, cU, hcU⟩ := hs (e.hom x) ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 (hU.preimage e.hom.continuous) x hxU
    refine ⟨r / 2, half_pos hr, ?_⟩
    have hLU : e.hom '' (K0 ∩ Metric.closedBall x (r / 2)) ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hb (lt_of_le_of_lt (Metric.mem_closedBall.1 hz.2) (by linarith))
    refine ⟨(localRestrict hLU n).hom cU, fun y hy => ?_⟩
    have hyK : y ∈ e.hom '' K0 := Set.image_mono Set.inter_subset_left hy
    rw [restrict_restrict, hcU y hyK (hLU hy)]
    simp only [s', hyK, ↓reduceDIte]
  choose! ρ hρpos hρrep using hpiece
  obtain ⟨t, htK, hcov⟩ := exists_ball_cover K0 hK0 ρ hρpos
  obtain ⟨c, hc⟩ := rep_biUnion I n hn hE e he (fun x => K0 ∩ Metric.closedBall x (ρ x))
    (fun x => hK0.inter_right Metric.isClosed_closedBall) s' t (fun x hx => hρrep x (htK x hx))
  have hKt : K0 ⊆ ⋃ x ∈ t, (fun x => K0 ∩ Metric.closedBall x (ρ x)) x := fun z hz => by
    have := hcov hz
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨x, hxt, hzx⟩ := this
    exact ⟨x, hxt, hz, Metric.ball_subset_closedBall hzx⟩
  refine ⟨(localRestrict (Set.image_mono hKt) n).hom c, fun y hy => ?_⟩
  rw [restrict_restrict, hc y (Set.image_mono hKt hy)]
  simp only [s', hy, ↓reduceDIte]

end Chart


end DGPS.Topology.ArbitraryChartLocalClass

namespace DGPS.Topology

open DGPS.Topology.LocalHomology DGPS.Topology.MayerVietoris
  DGPS.Topology.FiniteUnionLocalClass

/-- **Local class over an arbitrary compact set of a chart.**  Let `M` be a Hausdorff boundaryless
`n`-manifold (`n > 0`), `e : V ⟶ M` an open embedding of a real normed space (a chart) and `K0 ⊆ V`
compact.  Then `H_i(M, M ∖ e '' K0; F2) = 0` for `i > n`, and every consistent local section `s`
over `e '' K0` is represented by a unique class in `H_n(M, M ∖ e '' K0; F2)`. -/
theorem arbitrary_chart_compact_local_class {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : TopCat.of V ⟶ TopCat.of M) (he : Topology.IsOpenEmbedding e.hom)
    (K0 : Set V) (hK0 : IsCompact K0) :
    (∀ i, n < i → IsZero (localHomology (X := TopCat.of M) (e.hom '' K0) i)) ∧
    (∀ s : ∀ x, x ∈ e.hom '' K0 → localHomology (X := TopCat.of M) {x} n,
      IsConsistentSection n (e.hom '' K0 : Set (TopCat.of M)) s →
      ∃! c : localHomology (X := TopCat.of M) (e.hom '' K0) n,
        ∀ x (hx : x ∈ e.hom '' K0),
          (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) n).hom c = s x hx) := by
  have := ArbitraryChartLocalClass.properSpace_chart I n hn hE e he
  refine ⟨fun i hi => ArbitraryChartLocalClass.vanish I n hn hE e he K0 hK0 i hi, fun s hs => ?_⟩
  obtain ⟨c, hc⟩ := ArbitraryChartLocalClass.exists_class I n hn hE e he K0 hK0 s hs
  exact ⟨c, hc, fun c' hc' => ArbitraryChartLocalClass.uniq_compact I n hn hE e he K0 hK0 c' c
    (fun x hx => (hc' x hx).trans (hc x hx).symm)⟩

end DGPS.Topology
