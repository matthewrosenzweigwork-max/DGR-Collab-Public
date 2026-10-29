import DGPS.Topology.SingularAdapter
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite compact chart refinement (TOP008)

Every compact subset `K` of a Hausdorff finite-dimensional manifold is a finite union of compact
subsets `K_j`, each contained in the source of a single chart of the atlas.  Finite nonempty
intersections of the `K_j` are compact and lie in the source of every chart containing one of the
intersected members.

The manifold is a Mathlib charted space `M` over a model with corners `I : ModelWithCorners ℝ E H`
with `E` finite-dimensional, and `M` is Hausdorff.  The charts are members of `atlas H M`.

* `DGPS.Topology.finite_compact_chart_refinement`: the packet interface.
-/

namespace DGPS.Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Finite compact chart refinement: a compact `K ⊆ M` is a finite union of compact pieces `K j`,
each inside the source of one atlas chart `c j`; every finite nonempty intersection of pieces is
compact and is contained in the source of every atlas chart whose source contains one of the
intersected pieces (in particular in each `(c j).source`, `j ∈ s`). -/
theorem finite_compact_chart_refinement (I : ModelWithCorners ℝ E H) [T2Space M]
    (K : Set M) (hK : IsCompact K) :
    ∃ (n : ℕ) (c : Fin n → OpenPartialHomeomorph M H) (Kj : Fin n → Set M),
      (∀ j, c j ∈ atlas H M) ∧ (∀ j, IsCompact (Kj j)) ∧ (∀ j, Kj j ⊆ (c j).source) ∧
      K = ⋃ j, Kj j ∧
      (∀ s : Finset (Fin n), s.Nonempty →
        IsCompact (⋂ j ∈ s, Kj j) ∧
        (∀ e ∈ atlas H M, (∃ j ∈ s, Kj j ⊆ e.source) → (⋂ j ∈ s, Kj j) ⊆ e.source)) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hx : ∀ x : M, ∃ C : Set M, IsCompact C ∧ x ∈ interior C ∧ C ⊆ (chartAt H x).source :=
    fun x => exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)
  choose C hCc hCi hCs using hx
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover C
    (fun x _ => mem_interior_iff_mem_nhds.1 (hCi x))
  have hcover : K ⊆ ⋃ x ∈ t, C x := hcov
  let e : t ≃ Fin t.card := t.equivFin
  refine ⟨t.card, fun j => chartAt H (e.symm j : M), fun j => K ∩ C (e.symm j : M),
    fun j => chart_mem_atlas H _, fun j => hK.inter_right (hCc _).isClosed,
    fun j => (inter_subset_right).trans (hCs _), ?_, ?_⟩
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover hy)
      exact mem_iUnion.2 ⟨e ⟨x, hxt⟩, by simpa using And.intro hy hyx⟩
    · exact iUnion_subset fun j => inter_subset_left
  · intro s hs
    obtain ⟨j₀, hj₀⟩ := hs
    have hcl : ∀ j, IsClosed (K ∩ C (e.symm j : M)) := fun j =>
      hK.isClosed.inter (hCc _).isClosed
    have hsub : (⋂ j ∈ s, K ∩ C (e.symm j : M)) ⊆ K ∩ C (e.symm j₀ : M) :=
      biInter_subset_of_mem hj₀
    refine ⟨(hK.inter_right (hCc _).isClosed).of_isClosed_subset
      (isClosed_biInter fun j _ => hcl j) hsub, ?_⟩
    rintro e' _ ⟨j, hj, hjs⟩
    exact (biInter_subset_of_mem hj).trans hjs

end DGPS.Topology
