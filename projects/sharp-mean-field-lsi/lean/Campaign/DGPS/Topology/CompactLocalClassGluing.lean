import DGPS.Topology.ArbitraryChartLocalClass
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Compact local class gluing (TOP012)

For an arbitrary compact set `K` of a Hausdorff boundaryless `n`-manifold `M` (`n > 0`):
`H_i(M, M ∖ K; F2) = 0` for `i > n`, and every consistent local section over `K` is represented by
a unique class in `H_n(M, M ∖ K; F2)`.

`K` is covered by finitely many compact pieces, each lying in the image of an open embedding of the
model space `E` (a round chart; TOP011 `arbitrary_chart_compact_local_class` applies to every
compact subset of such an image).  The bundled property `Good` of TOP010 is preserved by unions of
compact sets whose intersection is `Good` (Mayer-Vietoris, TOP005 via `good_union`); an induction on
the number of pieces, with the overlap with the last piece again a union of fewer chart-compact
pieces, concludes.
-/

open CategoryTheory CategoryTheory.Limits DGPS.Topology.LocalHomology
  DGPS.Topology.MayerVietoris DGPS.Topology.FiniteUnionLocalClass

namespace DGPS.Topology.CompactLocalClassGluing

section Chart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless]

/-- A compact set of `M` lying in the image of an open embedding of the model space `E`. -/
def ChartCompact (S : Set M) : Prop :=
  IsCompact S ∧ ∃ f : E → M, Topology.IsOpenEmbedding f ∧ S ⊆ Set.range f

omit [T2Space M] in
include I in
/-- Every point of `M` lies in the image of an open embedding `E → M`. -/
lemma exists_chart_embedding (x : M) :
    ∃ f : E → M, Topology.IsOpenEmbedding f ∧ x ∈ Set.range f := by
  let Φ : OpenPartialHomeomorph M E := (chartAt H x).transHomeomorph I.toHomeomorph
  have hxΦ : x ∈ Φ.source := by
    show x ∈ (chartAt H x).source
    exact mem_chart_source H x
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 Φ.open_target (Φ x) (Φ.map_source hxΦ)
  let ψ : OpenPartialHomeomorph E M :=
    (OpenPartialHomeomorph.univBall (Φ x) r).trans Φ.symm
  have hsrc : ψ.source = Set.univ := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.univBall_source,
      Set.univ_inter]
    refine Set.eq_univ_of_forall fun v => ?_
    have hv := (OpenPartialHomeomorph.univBall (Φ x) r).map_source
      (by rw [OpenPartialHomeomorph.univBall_source]; exact Set.mem_univ v)
    rw [OpenPartialHomeomorph.univBall_target _ hr] at hv
    exact hb hv
  refine ⟨ψ, ψ.isOpenEmbedding hsrc, 0, ?_⟩
  show Φ.symm ((OpenPartialHomeomorph.univBall (Φ x) r) 0) = x
  rw [OpenPartialHomeomorph.univBall_apply_zero]
  exact Φ.left_inv hxΦ

include I in
/-- Compact subsets of the image of an open embedding of `E` are `Good`, by TOP011. -/
lemma good_chartCompact (n : ℕ) (hn : 0 < n) (hE : Module.finrank ℝ E = n) {S : Set M}
    (hS : ChartCompact (E := E) S) : Good (X := TopCat.of M) n S := by
  obtain ⟨hc, f, hf, hsub⟩ := hS
  let e : TopCat.of E ⟶ TopCat.of M := TopCat.ofHom ⟨f, hf.continuous⟩
  have he : Topology.IsOpenEmbedding e.hom := hf
  have hK0 : IsCompact (f ⁻¹' S) := by
    rw [hf.isEmbedding.isCompact_iff, Set.image_preimage_eq_of_subset hsub]
    exact hc
  have hSeq : S = e.hom '' (f ⁻¹' S) := (Set.image_preimage_eq_of_subset hsub).symm
  have := ArbitraryChartLocalClass.properSpace_chart I n hn hE e he
  rw [hSeq]
  exact ⟨fun i hi => ArbitraryChartLocalClass.vanish I n hn hE e he _ hK0 i hi,
    fun c c' h => ArbitraryChartLocalClass.uniq_compact I n hn hE e he _ hK0 c c' h,
    fun s hs => ArbitraryChartLocalClass.exists_class I n hn hE e he _ hK0 s hs⟩

include I in
/-- Finite unions of chart-compact sets are `Good`, by induction on the number of pieces. -/
lemma good_finite_union_chart (n : ℕ) (hn : 0 < n) (hE : Module.finrank ℝ E = n) :
    ∀ m : ℕ, ∀ P : Finset (Set M), P.card ≤ m → (∀ A ∈ P, ChartCompact (E := E) A) →
      Good (X := TopCat.of M) n (⋃ A ∈ P, A : Set M) := by
  classical
  intro m
  induction m with
  | zero =>
    intro P hcard _
    have : P = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    subst this
    simpa using good_empty (X := TopCat.of M) n
  | succ m ih =>
    intro P hcard hP
    rcases P.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simpa using good_empty (X := TopCat.of M) n
    set P' := P.erase a with hP'def
    have hP' : ∀ A ∈ P', ChartCompact (E := E) A := fun A hA =>
      hP A (Finset.mem_of_mem_erase hA)
    have hcard' : P'.card ≤ m := by
      have : P'.card = P.card - 1 := Finset.card_erase_of_mem ha
      omega
    set Q := P'.image (fun p => a ∩ p) with hQdef
    have hQcard : Q.card ≤ m := (Finset.card_image_le).trans hcard'
    have hQ : ∀ q ∈ Q, ChartCompact (E := E) q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨hac, f, hf, hsub⟩ := hP a ha
      exact ⟨hac.inter_right (hP' p hp).1.isClosed, f, hf,
        Set.inter_subset_left.trans hsub⟩
    have hU : (⋃ A ∈ P, A) = a ∪ ⋃ p ∈ P', p := by
      conv_lhs => rw [← Finset.insert_erase ha]
      rw [Finset.set_biUnion_insert]
    have hI : a ∩ (⋃ p ∈ P', p) = ⋃ q ∈ Q, q := by
      simp [Q, Set.inter_iUnion₂]
    have hAc : IsCompact a := (hP a ha).1
    have hBc : IsCompact (⋃ p ∈ P', p) :=
      P'.finite_toSet.isCompact_biUnion fun p hp => (hP' p hp).1
    have GA := good_chartCompact I n hn hE (hP a ha)
    have GB := ih P' hcard' hP'
    have GAB := ih Q hQcard hQ
    rw [← hI] at GAB
    rw [hU]
    exact good_union (X := TopCat.of M) (n := n) hAc hBc GA GB GAB

omit [T2Space M] in
include I in
lemma exists_compact_nhds_chart [LocallyCompactSpace M] (x : M) :
    ∃ C : Set M, IsCompact C ∧ x ∈ interior C ∧ ChartCompact (E := E) C := by
  obtain ⟨f, hf, hx⟩ := exists_chart_embedding I x
  obtain ⟨C, hC, hxC, hCs⟩ := exists_compact_subset hf.isOpen_range hx
  exact ⟨C, hC, hxC, hC, f, hf, hCs⟩

end Chart

end DGPS.Topology.CompactLocalClassGluing

namespace DGPS.Topology

open DGPS.Topology.LocalHomology DGPS.Topology.MayerVietoris
  DGPS.Topology.FiniteUnionLocalClass

/-- **Compact local class gluing.**  Let `M` be a Hausdorff boundaryless `n`-manifold (`n > 0`) and
`K ⊆ M` compact.  Then `H_i(M, M ∖ K; F2) = 0` for `i > n`, and every consistent local section `s`
over `K` is represented by a unique class in `H_n(M, M ∖ K; F2)`. -/
theorem compact_local_class_gluing {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n) (K : Set M) (hK : IsCompact K) :
    (∀ i, n < i → IsZero (localHomology (X := TopCat.of M) K i)) ∧
    (∀ s : ∀ x, x ∈ K → localHomology (X := TopCat.of M) {x} n,
      IsConsistentSection (X := TopCat.of M) n K s →
      ∃! c : localHomology (X := TopCat.of M) K n,
        ∀ x (hx : x ∈ K),
          (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) n).hom c = s x hx) := by
  classical
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (hE ▸ hn)
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hx := fun x : M => CompactLocalClassGluing.exists_compact_nhds_chart I x
  choose C hCc hCi hCch using hx
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover C
    (fun x _ => mem_interior_iff_mem_nhds.1 (hCi x))
  let P : Finset (Set M) := t.image (fun x => K ∩ C x)
  have hPc : ∀ A ∈ P, CompactLocalClassGluing.ChartCompact (E := E) A := by
    intro A hA
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨-, f, hf, hsub⟩ := hCch x
    exact ⟨hK.inter_right (hCc x).isClosed, f, hf, Set.inter_subset_right.trans hsub⟩
  have hKP : (⋃ A ∈ P, A) = K := by
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset fun A hA => ?_
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hA
      exact Set.inter_subset_left
    · intro y hy
      obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
      exact Set.mem_iUnion₂.2 ⟨K ∩ C x, Finset.mem_image.2 ⟨x, hxt, rfl⟩, hy, hyx⟩
  have G := CompactLocalClassGluing.good_finite_union_chart I n hn hE P.card P le_rfl hPc
  rw [hKP] at G
  refine ⟨fun i hi => G.1 i hi, fun s hs => ?_⟩
  obtain ⟨c, hc⟩ := G.2.2 s hs
  exact ⟨c, hc, fun c' hc' => G.2.1 c' c (fun x hx => (hc' x hx).trans (hc x hx).symm)⟩

end DGPS.Topology
