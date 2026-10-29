import DGPS.Topology.LocalSection
import DGPS.Topology.CompactLocalClassGluing
import DGPS.Topology.CompactLocalClass

/-!
# Nonzero compact fundamental class (TOP013)

For a nonempty compact Hausdorff boundaryless `n`-manifold `M` (`n > 0`) there is a nonzero class
in `H_n(M; F2)` whose image under `H_n(M) ≅ H_n(M, ∅) → H_n(M, M ∖ {x})` is the canonical nonzero
local class, for every point `x`.

The canonical mod two local section (TOP007) is consistent: near `x`, a chart ball `U` lies in a
closed chart ball `K0` over which restriction to any point is an isomorphism (TOP009), so the class
over `K0` lifting the canonical class at `x` restricts to a nonzero, hence canonical, class at every
`y ∈ U`.  Compact local class gluing (TOP012) with `K = univ` then gives a class in
`H_n(M, M ∖ univ) = H_n(M, ∅) = H_n(M)`.
-/

open CategoryTheory CategoryTheory.Limits DGPS.Topology.LocalHomology
  DGPS.Topology.MayerVietoris DGPS.Topology.FiniteUnionLocalClass

namespace DGPS.Topology

section AbsoluteRestriction

variable {X : TopCat.{0}}

/-- The map of pairs `(X, ∅) ⟶ (X, S)`. -/
noncomputable def emptyToSet (S : Set X) : emptyPairFunctor.obj X ⟶ TopPair.ofSet X S :=
  TopPair.homMk (TopCat.ofHom ⟨fun e => e.elim, continuous_of_discreteTopology⟩) (𝟙 X)
    (by ext e; exact e.elim)

/-- Restriction `H_n(X) ≅ H_n(X, ∅) ⟶ H_n(X, S)`. -/
noncomputable def absoluteRestrict (n : ℕ) (S : Set X) :
    (singularHomology n).obj X ⟶ (relativeHomology n).obj (TopPair.ofSet X S) :=
  (relativeHomologyEmptyIso n).hom.app X ≫ (relativeHomology n).map (emptyToSet S)

theorem emptyToSet_relPairMap {S T : Set X} (h : S ⊆ T) :
    emptyToSet S ≫ relPairMap h = emptyToSet T := by
  ext
  · exact (PEmpty.elim ‹_›)
  · rfl

theorem absoluteRestrict_comp (n : ℕ) {S T : Set X} (h : S ⊆ T) :
    absoluteRestrict n S ≫ (relativeHomology n).map (relPairMap h) = absoluteRestrict n T := by
  unfold absoluteRestrict
  rw [Category.assoc, ← (relativeHomology n).map_comp, emptyToSet_relPairMap]

theorem isIso_absoluteRestrict_compl_univ (n : ℕ) :
    IsIso (absoluteRestrict n (Set.univ : Set X)ᶜ) := by
  have hE : IsEmpty ↥((Set.univ : Set X)ᶜ) := ⟨fun y => y.2 trivial⟩
  let e : PEmpty ≃ₜ ↥((Set.univ : Set X)ᶜ) :=
    { toEquiv := Equiv.equivOfIsEmpty _ _
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := by
        rw [continuous_iff_continuousAt]; exact fun y => (hE.false y).elim }
  have hiso : IsIso (emptyToSet (X := X) (Set.univ : Set X)ᶜ).left := by
    have : (emptyToSet (X := X) (Set.univ : Set X)ᶜ).left = (TopCat.isoOfHomeo e).hom := by
      ext y; exact y.elim
    rw [this]; infer_instance
  have hiso' : IsIso (emptyToSet (X := X) (Set.univ : Set X)ᶜ).right :=
    inferInstanceAs (IsIso (𝟙 X))
  have hq : IsIso ((relativeHomology n).map (emptyToSet (X := X) (Set.univ : Set X)ᶜ)) :=
    LocalHomology.isIso_relativeHomology_of_quasiIso _
      (LocalHomology.quasiIso_of_isIso _) (LocalHomology.quasiIso_of_isIso _) n
  unfold absoluteRestrict
  infer_instance

theorem localRestrict_comp {S T U : Set X} (h1 : S ⊆ T) (h2 : T ⊆ U) (n : ℕ) :
    localRestrict h2 n ≫ localRestrict h1 n = localRestrict (h1.trans h2) n := by
  unfold localRestrict
  rw [← (relativeHomology n).map_comp]
  congr 1

end AbsoluteRestriction

section Main

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless]

include I

/-- The canonical mod two local section is consistent. -/
theorem canonical_section_consistent (n : ℕ) (hn : 0 < n) (hE : Module.finrank ℝ E = n) :
    IsConsistentSection (X := TopCat.of M) n Set.univ
      (fun x _ => canonicalLocalClass n (TopCat.of M) x) := by
  intro x _
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (hE ▸ hn)
  obtain ⟨f, hf, z, hz⟩ := CompactLocalClassGluing.exists_chart_embedding (E := E) I x
  let e : TopCat.of E ⟶ TopCat.of M := TopCat.ofHom ⟨f, hf.continuous⟩
  have hfe : e.hom = f := rfl
  have hemb : Topology.IsOpenEmbedding e.hom := hf
  obtain ⟨hiso, -, hex⟩ := convex_compact_local_class I n hn hE e hemb
    (Metric.closedBall z 1) (isCompact_closedBall z 1) (convex_closedBall z 1)
    ⟨z, Metric.mem_closedBall_self zero_le_one⟩
  have hxK : x ∈ e.hom '' Metric.closedBall z 1 :=
    ⟨z, Metric.mem_closedBall_self zero_le_one, hz⟩
  obtain ⟨c0, hc0, -⟩ := hex x hxK (canonicalLocalClass n (TopCat.of M) x)
  have hUK : e.hom '' Metric.ball z 1 ⊆ e.hom '' Metric.closedBall z 1 :=
    Set.image_mono Metric.ball_subset_closedBall
  refine ⟨e.hom '' Metric.ball z 1, hemb.isOpenMap _ Metric.isOpen_ball, ⟨z, Metric.mem_ball_self one_pos, hz⟩,
    (localRestrict (X := TopCat.of M) hUK n).hom c0, fun y _ hyU => ?_⟩
  have hyK : y ∈ e.hom '' Metric.closedBall z 1 := hUK hyU
  have hcomp := localRestrict_comp (X := TopCat.of M) (Set.singleton_subset_iff.2 hyU) hUK n
  have hy : (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hyU) n).hom
      ((localRestrict (X := TopCat.of M) hUK n).hom c0) =
      (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hyK) n).hom c0 := by
    have := congr($(hcomp).hom c0)
    simpa using this
  rw [hy]
  have hne : c0 ≠ 0 := by
    intro h0
    apply (canonical_mod_two_local_section I n hn hE (M := M)).1 x |>.1
    rw [← hc0, h0, map_zero]
  have := hiso y hyK n
  have hinj : Function.Injective
      (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hyK) n).hom :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  refine ((canonical_mod_two_local_section I n hn hE (M := M)).1 y).2 _ fun h0 => hne (hinj ?_)
  simpa using h0

/-- **Nonzero compact fundamental class.**  Let `M` be a nonempty compact Hausdorff boundaryless
`n`-manifold, `n > 0`.  Then `H_n(M; F2)` contains a nonzero class whose image in
`H_n(M, M ∖ {x}; F2)` is the canonical nonzero local class, for every `x`; the canonical local
class is the unique nonzero element of that group. -/
theorem nonzero_compact_fundamental_class [CompactSpace M] [Nonempty M]
    (n : ℕ) (hn : 0 < n) (hE : Module.finrank ℝ E = n) :
    ∃ c : (singularHomology n).obj (TopCat.of M), c ≠ 0 ∧
      ∀ x : M, (absoluteRestrict n ({x}ᶜ : Set M)).hom c = canonicalLocalClass n (TopCat.of M) x ∧
        ∀ d : (relativeHomology n).obj (TopPair.ofSet (TopCat.of M) {x}ᶜ), d ≠ 0 →
          d = canonicalLocalClass n (TopCat.of M) x := by
  obtain ⟨x0⟩ := ‹Nonempty M›
  obtain ⟨-, hglue⟩ := compact_local_class_gluing I n hn hE (Set.univ : Set M) isCompact_univ
  obtain ⟨c0, hc0, -⟩ := hglue (fun x _ => canonicalLocalClass n (TopCat.of M) x)
    (canonical_section_consistent I n hn hE)
  have hiso := isIso_absoluteRestrict_compl_univ (X := TopCat.of M) n
  have hpt : ∀ x : M, (absoluteRestrict n ({x}ᶜ : Set M)).hom
      ((inv (absoluteRestrict n (Set.univ : Set (TopCat.of M))ᶜ)).hom c0) =
      canonicalLocalClass n (TopCat.of M) x := by
    intro x
    have h := absoluteRestrict_comp (X := TopCat.of M) n
      (Set.compl_subset_compl.2 (Set.subset_univ {x}) : (Set.univ : Set M)ᶜ ⊆ ({x}ᶜ : Set M))
    rw [← h]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    have h3 : (absoluteRestrict n (Set.univ : Set (TopCat.of M))ᶜ).hom
        ((inv (absoluteRestrict n (Set.univ : Set (TopCat.of M))ᶜ)).hom c0) = c0 := by
      simp
    rw [h3]
    exact hc0 x trivial
  refine ⟨(inv (absoluteRestrict n (Set.univ : Set (TopCat.of M))ᶜ)).hom c0, ?_, fun x =>
    ⟨hpt x, ((canonical_mod_two_local_section I n hn hE (M := M)).1 x).2⟩⟩
  intro h0
  have := hpt x0
  rw [h0, map_zero] at this
  exact ((canonical_mod_two_local_section I n hn hE (M := M)).1 x0).1 this.symm

end Main

end DGPS.Topology
