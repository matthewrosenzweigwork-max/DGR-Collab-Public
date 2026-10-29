import DGPS.Topology.CompactLocalClass

/-!
# Finite union local class (TOP010)

For a compact set `K` that is a finite union of compact convex sets in one chart of an `n`-manifold
`M`, every consistent local section over `K` is represented by a unique class in
`H_n(M, M ∖ K; F2)`, and `H_i(M, M ∖ K; F2) = 0` for `i > n`.

The property `Good n S` bundles vanishing above degree `n`, uniqueness and existence of the class
for consistent sections.  It holds for compact convex sets in a chart (TOP009 plus a connectedness
argument), and is preserved by unions of compact sets whose intersection is again `Good`
(Mayer-Vietoris, TOP005); an induction on the number of convex pieces concludes.
-/

open CategoryTheory CategoryTheory.Limits DGPS.Topology.LocalHomology
  DGPS.Topology.MayerVietoris

namespace DGPS.Topology.FiniteUnionLocalClass

section General

variable {X : TopCat.{0}}

/-- A local section over `K`: a class in `H_n(X, X ∖ {x})` for each `x ∈ K`, is *consistent* if
every `x ∈ K` has an open neighbourhood `U` and a class in `H_n(X, X ∖ U)` restricting to the
section at every point of `K ∩ U` (Hatcher, Lemma 3.27). -/
def IsConsistentSection (n : ℕ) (K : Set X) (s : ∀ x, x ∈ K → localHomology ({x} : Set X) n) :
    Prop :=
  ∀ x, x ∈ K → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ c : localHomology U n,
    ∀ y (hy : y ∈ K) (hyU : y ∈ U),
      (localRestrict (Set.singleton_subset_iff.2 hyU) n).hom c = s y hy

lemma IsConsistentSection.mono {n : ℕ} {K L : Set X} {s : ∀ x, x ∈ K → localHomology ({x} : Set X) n}
    (hs : IsConsistentSection n K s) (hLK : L ⊆ K) :
    IsConsistentSection n L (fun x hx => s x (hLK hx)) := fun x hx => by
  obtain ⟨U, hU, hxU, c, hc⟩ := hs x (hLK hx)
  exact ⟨U, hU, hxU, c, fun y hy hyU => hc y (hLK hy) hyU⟩

lemma elem_eq {M : F2Mod} (h : IsZero M) (a b : M) : a = b :=
  (ModuleCat.isZero_iff_subsingleton.1 h).elim a b

lemma biprod_elem_ext {K L : F2Mod} (x y : (K ⊞ L : F2Mod))
    (h1 : (biprod.fst : K ⊞ L ⟶ K).hom x = (biprod.fst : K ⊞ L ⟶ K).hom y)
    (h2 : (biprod.snd : K ⊞ L ⟶ L).hom x = (biprod.snd : K ⊞ L ⟶ L).hom y) : x = y := by
  have key : ∀ z : (K ⊞ L : F2Mod), z = (biprod.inl : K ⟶ K ⊞ L).hom ((biprod.fst : K ⊞ L ⟶ K).hom z)
      + (biprod.inr : L ⟶ K ⊞ L).hom ((biprod.snd : K ⊞ L ⟶ L).hom z) := fun z => by
    have h : (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : K ⊞ L ⟶ K ⊞ L).hom z = z := by
      rw [biprod.total]; rfl
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
      LinearMap.comp_apply] at h
    exact h.symm
  rw [key x, key y, h1, h2]

lemma restrict_restrict {K L N : Set X} (h1 : K ⊆ L) (h2 : L ⊆ N) (n : ℕ)
    (c : localHomology N n) :
    (localRestrict h1 n).hom ((localRestrict h2 n).hom c) = (localRestrict (h1.trans h2) n).hom c := by
  have : localRestrict h2 n ≫ localRestrict h1 n = localRestrict (h1.trans h2) n := by
    unfold localRestrict
    rw [← Functor.map_comp]
    congr 1
  rw [← this]
  rfl

/-- The property of a set `S` of being a "good" support of local classes in degree `n`. -/
def Good (n : ℕ) (S : Set X) : Prop :=
  (∀ i, n < i → IsZero (localHomology S i)) ∧
  (∀ c c' : localHomology S n,
    (∀ x (hx : x ∈ S), (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c =
      (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c') → c = c') ∧
  (∀ s : ∀ x, x ∈ S → localHomology ({x} : Set X) n, IsConsistentSection n S s →
    ∃ c : localHomology S n, ∀ x (hx : x ∈ S),
      (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c = s x hx)

lemma good_empty (n : ℕ) : Good n (∅ : Set X) := by
  have hz : ∀ i, IsZero (localHomology (∅ : Set X) i) := by
    intro i
    have hiso : IsIso (TopPair.ofSet X (∅ : Set X)ᶜ).hom :=
      ⟨TopCat.ofHom ⟨fun x => ⟨x, by simp⟩, by fun_prop⟩, by ext; rfl, by ext; rfl⟩
    have hq : QuasiIso (singularChains.map (TopPair.ofSet X (∅ : Set X)ᶜ).hom) :=
      DGPS.Topology.LocalHomology.quasiIso_of_isIso _
    have hac := (pairShortComplex_shortExact (TopPair.ofSet X (∅ : Set X)ᶜ)).acyclic_X₃ hq
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hac i)
  refine ⟨fun i _ => hz i, fun c c' _ => ?_, fun s _ => ⟨0, fun x hx => absurd hx (by simp)⟩⟩
  exact elem_eq (hz n) c c'

lemma good_union [T2Space X] {n : ℕ} {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (GA : Good n A) (GB : Good n B) (GAB : Good n (A ∩ B)) : Good n (A ∪ B) := by
  obtain ⟨δ, h1, h2, h3, hinj, hglue⟩ := (relative_mayer_vietoris.1 X A B hA hB)
  have hlift : ∀ i, n ≤ i → Function.Injective (biprod.lift
      (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) i)
      (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) i)).hom := fun i hi =>
    hinj i (fun x => elem_eq (GAB.1 (i + 1) (by omega)) x 0)
  refine ⟨fun i hi => ?_, fun c c' hcc => ?_, fun s hs => ?_⟩
  · have hmono : Mono (biprod.lift
        (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) i)
        (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) i)) :=
      (ModuleCat.mono_iff_injective _).2 (hlift i hi.le)
    exact IsZero.of_mono (biprod.lift
        (localRestrict (Set.subset_union_left : A ⊆ A ∪ B) i)
        (localRestrict (Set.subset_union_right : B ⊆ A ∪ B) i)) ((biprod_isZero_iff _ _).2 ⟨GA.1 i hi, GB.1 i hi⟩)
  · apply hlift n le_rfl
    have hA' := GA.2.1 ((localRestrict Set.subset_union_left n).hom c)
      ((localRestrict Set.subset_union_left n).hom c') (fun x hx => by
        rw [restrict_restrict, restrict_restrict]; exact hcc x (Or.inl hx))
    have hB' := GB.2.1 ((localRestrict Set.subset_union_right n).hom c)
      ((localRestrict Set.subset_union_right n).hom c') (fun x hx => by
        rw [restrict_restrict, restrict_restrict]; exact hcc x (Or.inr hx))
    exact biprod_elem_ext _ _ (by simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, biprod.lift_fst]; exact hA')
      (by simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, biprod.lift_snd]; exact hB')
  · obtain ⟨cA, hcA⟩ := GA.2.2 (fun x hx => s x (Or.inl hx)) (hs.mono Set.subset_union_left)
    obtain ⟨cB, hcB⟩ := GB.2.2 (fun x hx => s x (Or.inr hx)) (hs.mono Set.subset_union_right)
    have heq : (localRestrict (Set.inter_subset_left : A ∩ B ⊆ A) n).hom cA =
        (localRestrict (Set.inter_subset_right : A ∩ B ⊆ B) n).hom cB :=
      GAB.2.1 _ _ (fun x hx => by
        rw [restrict_restrict, restrict_restrict, hcA x hx.1, hcB x hx.2])
    obtain ⟨c, hc1, hc2⟩ := (hglue n cA cB).2 heq
    refine ⟨c, fun x hx => ?_⟩
    rcases hx with hx | hx
    · rw [← hcA x hx, ← hc1, restrict_restrict]
    · rw [← hcB x hx, ← hc2, restrict_restrict]

end General

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
  (hE : Module.finrank ℝ E = n)
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (e : TopCat.of V ⟶ TopCat.of M) (he : Topology.IsOpenEmbedding e.hom)

include I hn hE he

/-- Restriction to a point of `e '' K0` is injective on `H_n(M, M ∖ e '' K0)`, for nonempty
compact convex `K0` (TOP009). -/
lemma convex_inj (K0 : Set V) (hc : IsCompact K0) (hcv : Convex ℝ K0) (hne : K0.Nonempty)
    {x : TopCat.of M} (hx : x ∈ e.hom '' K0) {c c' : localHomology (e.hom '' K0) n}
    (h : (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c =
      (localRestrict (Set.singleton_subset_iff.2 hx) n).hom c') : c = c' := by
  have hiso := (convex_compact_local_class I n hn hE e he K0 hc hcv hne).1 x hx n
  exact (ConcreteCategory.bijective_of_isIso
    (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) n)).1 h

/-- Compact convex sets in a chart are `Good`. -/
lemma good_convex (K0 : Set V) (hc : IsCompact K0) (hcv : Convex ℝ K0) :
    Good n (e.hom '' K0 : Set (TopCat.of M)) := by
  classical
  rcases K0.eq_empty_or_nonempty with rfl | hne
  · rw [Set.image_empty]; exact good_empty n
  have T := convex_compact_local_class I n hn hE e he K0 hc hcv hne
  obtain ⟨x0, hx0⟩ := hne
  refine ⟨T.2.1, fun c c' h => ?_, fun s hs => ?_⟩
  · exact convex_inj I n hn hE e he K0 hc hcv ⟨x0, hx0⟩ ⟨x0, hx0, rfl⟩ (h _ ⟨x0, hx0, rfl⟩)
  · have hx0S : e.hom x0 ∈ e.hom '' K0 := ⟨x0, hx0, rfl⟩
    obtain ⟨c, hc0, -⟩ := (T.2.2 _ hx0S (s _ hx0S))
    refine ⟨c, ?_⟩
    -- the set of chart points where `c` agrees with `s` is locally constant on `K0`
    let Pr : V → Prop := fun y => ∀ hy : e.hom y ∈ e.hom '' K0,
      (localRestrict (Set.singleton_subset_iff.2 hy) n).hom c = s _ hy
    let f : V → Bool := fun y => decide (Pr y)
    have hloc : ∀ y ∈ K0, f =ᶠ[nhdsWithin y K0] fun _ => f y := by
      intro y hy
      have hyS : e.hom y ∈ e.hom '' K0 := ⟨y, hy, rfl⟩
      obtain ⟨U, hU, hyU, cU, hcU⟩ := hs _ hyS
      have hpre : IsOpen (e.hom ⁻¹' U) := hU.preimage e.hom.continuous
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hpre y hyU
      set K' : Set V := K0 ∩ Metric.closedBall y (r / 2) with hK'
      have hK'c : IsCompact K' := hc.inter_right Metric.isClosed_closedBall
      have hK'cv : Convex ℝ K' := hcv.inter (convex_closedBall _ _)
      have hyK' : y ∈ K' := ⟨hy, Metric.mem_closedBall_self (by positivity)⟩
      have hLS : e.hom '' K' ⊆ e.hom '' K0 := Set.image_mono Set.inter_subset_left
      have hLU : e.hom '' K' ⊆ U := by
        rintro _ ⟨z, hz, rfl⟩
        exact hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz.2) (by linarith))
      have key : ∀ z ∈ K', Pr z ↔ (localRestrict hLS n).hom c = (localRestrict hLU n).hom cU := by
        intro z hz
        have hzL : e.hom z ∈ e.hom '' K' := ⟨z, hz, rfl⟩
        have hzS : e.hom z ∈ e.hom '' K0 := hLS hzL
        have hzU : e.hom z ∈ U := hLU hzL
        have h1 : (localRestrict (Set.singleton_subset_iff.2 hzL) n).hom
            ((localRestrict hLS n).hom c) =
            (localRestrict (Set.singleton_subset_iff.2 hzS) n).hom c :=
          restrict_restrict _ _ n c
        have h2 : (localRestrict (Set.singleton_subset_iff.2 hzL) n).hom
            ((localRestrict hLU n).hom cU) = s _ hzS := by
          rw [restrict_restrict]; exact hcU _ hzS hzU
        constructor
        · intro hP
          exact convex_inj I n hn hE e he K' hK'c hK'cv ⟨y, hyK'⟩ hzL (by
            rw [h1, h2]; exact hP hzS)
        · intro heq hzS'
          rw [← h1, heq, h2]
      refine mem_nhdsWithin.2 ⟨Metric.ball y (r / 2), Metric.isOpen_ball,
        Metric.mem_ball_self (by positivity), ?_⟩
      rintro z ⟨hz1, hz2⟩
      have hzK' : z ∈ K' := ⟨hz2, Metric.ball_subset_closedBall hz1⟩
      exact decide_eq_decide.2 ((key z hzK').trans (key y hyK').symm)
    have hcont : ContinuousOn f K0 := fun y hy =>
      (continuousWithinAt_const (b := f y)).congr_of_eventuallyEq (hloc y hy) rfl
    have hall : ∀ z ∈ K0, Pr z := fun z hz => by
      have := hcv.isPreconnected.constant hcont hx0 hz
      have h0 : f x0 = true := decide_eq_true_iff.2 (fun hy => by exact hc0)
      rw [h0] at this
      exact decide_eq_true_iff.1 this.symm
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact hall z hz _

/-- Finite unions of compact convex sets in a chart are `Good`, by induction on the number of
pieces, using Mayer-Vietoris and the decomposition of the overlap into pairwise intersections. -/
lemma good_finite_union (P : Finset (Set V)) (hP : ∀ A ∈ P, IsCompact A ∧ Convex ℝ A) :
    Good n (e.hom '' (⋃ A ∈ P, A) : Set (TopCat.of M)) := by
  classical
  suffices h : ∀ m : ℕ, ∀ P : Finset (Set V), P.card ≤ m → (∀ A ∈ P, IsCompact A ∧ Convex ℝ A) →
      Good n (e.hom '' (⋃ A ∈ P, A) : Set (TopCat.of M)) from h _ P le_rfl hP
  intro m
  induction m with
  | zero =>
    intro P hcard _
    have : P = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    subst this
    simpa using good_empty n
  | succ m ih =>
    intro P hcard hP
    rcases P.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simpa using good_empty n
    set P' := P.erase a with hP'def
    have hP' : ∀ A ∈ P', IsCompact A ∧ Convex ℝ A := fun A hA => hP A (Finset.mem_of_mem_erase hA)
    have hcard' : P'.card ≤ m := by
      have : P'.card = P.card - 1 := Finset.card_erase_of_mem ha
      omega
    set Q := P'.image (fun p => a ∩ p) with hQdef
    have hQcard : Q.card ≤ m := (Finset.card_image_le).trans hcard'
    have hQ : ∀ q ∈ Q, IsCompact q ∧ Convex ℝ q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      exact ⟨(hP a ha).1.inter_right (hP' p hp).1.isClosed, (hP a ha).2.inter (hP' p hp).2⟩
    have hU : (⋃ A ∈ P, A) = a ∪ ⋃ p ∈ P', p := by
      conv_lhs => rw [← Finset.insert_erase ha]
      rw [Finset.set_biUnion_insert]
    have hI : a ∩ (⋃ p ∈ P', p) = ⋃ q ∈ Q, q := by
      simp [Q, Set.inter_iUnion₂]
    have hAc : IsCompact (e.hom '' a) := (hP a ha).1.image e.hom.continuous
    have hBc : IsCompact (e.hom '' (⋃ p ∈ P', p)) :=
      (P'.finite_toSet.isCompact_biUnion fun p hp => (hP' p hp).1).image e.hom.continuous
    have GA := good_convex I n hn hE e he a (hP a ha).1 (hP a ha).2
    have GB := ih P' hcard' hP'
    have GAB := ih Q hQcard hQ
    rw [← hI, Set.image_inter he.injective] at GAB
    rw [hU, Set.image_union]
    exact good_union hAc hBc GA GB GAB

end Chart

end DGPS.Topology.FiniteUnionLocalClass

namespace DGPS.Topology

open DGPS.Topology.LocalHomology DGPS.Topology.MayerVietoris
  DGPS.Topology.FiniteUnionLocalClass

/-- **Finite union local class.**  Let `M` be a Hausdorff boundaryless `n`-manifold (`n > 0`),
`e : V ⟶ M` an open embedding of a real normed space (a chart), and `K = e '' (⋃ A ∈ P, A)` the
image of a finite union of compact convex sets.  Then `H_i(M, M ∖ K; F2) = 0` for `i > n`, and
every consistent local section `s` over `K` (`IsConsistentSection`) is represented by a unique
class in `H_n(M, M ∖ K; F2)`, i.e. there is exactly one `c` whose restriction to `H_n(M, M ∖ {x})`
is `s x` for every `x ∈ K`. -/
theorem finite_union_local_class {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : TopCat.of V ⟶ TopCat.of M) (he : Topology.IsOpenEmbedding e.hom)
    (P : Finset (Set V)) (hPc : ∀ A ∈ P, IsCompact A) (hPcv : ∀ A ∈ P, Convex ℝ A) :
    (∀ i, n < i → IsZero (localHomology (X := TopCat.of M) (e.hom '' ⋃ A ∈ P, A) i)) ∧
    (∀ s : ∀ x, x ∈ e.hom '' (⋃ A ∈ P, A) → localHomology (X := TopCat.of M) {x} n,
      IsConsistentSection n (e.hom '' (⋃ A ∈ P, A) : Set (TopCat.of M)) s →
      ∃! c : localHomology (X := TopCat.of M) (e.hom '' ⋃ A ∈ P, A) n,
        ∀ x (hx : x ∈ e.hom '' (⋃ A ∈ P, A)),
          (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) n).hom c = s x hx) := by
  obtain ⟨h1, h2, h3⟩ := good_finite_union I n hn hE e he P (fun A hA => ⟨hPc A hA, hPcv A hA⟩)
  refine ⟨h1, fun s hs => ?_⟩
  obtain ⟨c, hc⟩ := h3 s hs
  exact ⟨c, hc, fun c' hc' => h2 c' c (fun x hx => (hc' x hx).trans (hc x hx).symm)⟩

end DGPS.Topology
