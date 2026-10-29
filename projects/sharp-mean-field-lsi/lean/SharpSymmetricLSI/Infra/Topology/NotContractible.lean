import SharpSymmetricLSI.Infra.Topology.EuclideanCompact
import SharpSymmetricLSI.Infra.Topology.ChartTransport
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# A closed manifold of positive dimension is not contractible

Let `M` be a compact Hausdorff space, locally homeomorphic to `ℝⁿ` with `n ≥ 1`.  Following
Hatcher, *Algebraic Topology*, Lemma 3.27 with `𝔽₂` coefficients:

* every compact set inside a chart is `Good` (Euclidean case `good_of_isCompact`, transported by
  `Good.of_homeomorph`); only open sets homeomorphic to open subsets of `ℝⁿ` are used, so the
  result holds for any compact Hausdorff space locally homeomorphic to `ℝⁿ`
  (`SharpLSI.not_contractible_of_locallyEuclidean`);
* `M` is a finite union of compact sets inside charts, so the gluing step `Good.union` gives
  `Good n M`; in particular `Hₙ(M; 𝔽₂) ≠ 0`;
* if `M` were contractible, then `Hₙ(M, ∅) ≅ H̃ₙ₋₁(∅) = 0`, a contradiction.

The main result is `SharpLSI.not_contractible_of_closed_manifold`.
-/

universe u

open CategoryTheory Limits Set Topology Module TopCat

namespace SharpLSI.Topology

section General

variable {X : TopCat.{u}}

/-- Abstract induction: if `Q` is a property of sets, stable under intersection, whose members are
closed and `Good`, then finite unions of members of `Q` are `Good`. -/
theorem good_unionL_of {n : ℕ} (hn : 1 ≤ n)
    (hloc : ∀ x : X, ∀ α β : locH n ({x} : Set X), α ≠ 0 → β ≠ 0 → α = β)
    (Q : Set X → Prop) (hQi : ∀ A B, Q A → Q B → Q (A ∩ B)) (hQc : ∀ A, Q A → IsClosed A)
    (hQg : ∀ A, Q A → Good n A) :
    ∀ L : List (Set X), (∀ P ∈ L, Q P) → Good n (unionL L) := by
  suffices ∀ m, ∀ L : List (Set X), L.length = m → (∀ P ∈ L, Q P) → Good n (unionL L) from
    fun L ↦ this _ L rfl
  intro m
  induction m with
  | zero =>
    intro L hL _
    rw [List.length_eq_zero_iff.1 hL]
    exact good_empty _
  | succ m ih =>
    intro L hlen hL
    cases L with
    | nil => simp at hlen
    | cons C L =>
      simp only [List.length_cons, add_left_inj] at hlen
      have hC : Q C := hL C List.mem_cons_self
      have hL' : ∀ P ∈ L, Q P := fun P hP ↦ hL P (List.mem_cons_of_mem _ hP)
      have g₃ : Good n (C ∩ unionL L) := by
        rw [inter_unionL]
        refine ih _ (by simp [hlen]) fun P hP ↦ ?_
        obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hP
        exact hQi _ _ hC (hL' Q' hQ')
      rw [unionL_cons]
      exact Good.union hn hloc (hQc C hC) (isClosed_unionL fun P hP ↦ hQc P (hL' P hP))
        (hQg C hC) (ih L hlen hL') g₃

/-- If the whole space is contractible, `Hₖ₊₁(X, X ∖ X) = Hₖ₊₁(X, ∅)` vanishes. -/
lemma locH_univ_eq_zero [ContractibleSpace X] (k : ℕ) (α : locH (k + 1) (univ : Set X)) :
    α = 0 := by
  have : ContractibleSpace (TopPair.ofInclusion (subset_univ (univᶜ : Set X))).fst :=
    (Homeomorph.Set.univ X).contractibleSpace
  have : IsEmpty (TopPair.ofInclusion (subset_univ (univᶜ : Set X))).snd :=
    ⟨fun x ↦ x.2 trivial⟩
  have hz : IsZero ((TopPair.ofInclusion (subset_univ (univᶜ : Set X))).singularHomology
      R2 (k + 1)) :=
    (TauCeti.isZero_reducedSingularHomologyFunctor_of_isEmpty R2 _ k).of_iso
      (asIso ((TopPair.ofInclusion (subset_univ (univᶜ : Set X))).reducedSingularHomologyδ
        R2 k))
  exact (ModuleCat.subsingleton_of_isZero hz).elim _ _

end General

section Manifold

/-- The model space, lifted to universe `u`. -/
abbrev Eu (n : ℕ) : Type u := EuclideanSpace ℝ (ULift.{u} (Fin n))

lemma finrank_Eu (n : ℕ) : finrank ℝ (Eu.{u} n) = n := by simp

/-- The isometry `ℝⁿ ≃ Eu n`. -/
noncomputable def toEu (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₜ Eu.{u} n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ Equiv.ulift.symm).toHomeomorph

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]

local notation "𝕄" => TopCat.of M

/-- Compact subsets of an open set homeomorphic to an open subset of `ℝⁿ` are `Good`. -/
theorem good_of_subset_homeo {m : ℕ} (hm : n = m + 1) {U : Set M} {V : Set (Eu.{u} n)}
    (hU : IsOpen U) (hV : IsOpen V) (h : U ≃ₜ V) {A : Set M} (hA : IsCompact A) (hAU : A ⊆ U) :
    Good (X := 𝕄) (m + 1) A := by
  let B : Set (Eu.{u} n) := Subtype.val '' (h '' (Subtype.val ⁻¹' A))
  have hAc : IsCompact (Subtype.val ⁻¹' A : Set U) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_self_of_subset_right hAU]
    exact hA
  have hBc : IsCompact B := (hAc.image h.continuous).image continuous_subtype_val
  have hBV : B ⊆ V := by rintro _ ⟨w, -, rfl⟩; exact w.2
  have hAB : ∀ u : U, (u : M) ∈ A ↔ (h u : Eu.{u} n) ∈ B := by
    intro u
    constructor
    · intro hu; exact ⟨h u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, hau⟩
      rwa [← h.injective (Subtype.ext hau)]
  have hfin : finrank ℝ (Eu.{u} n) = m + 1 := by rw [finrank_Eu, hm]
  exact Good.of_homeomorph (X := 𝕄) (Y := TopCat.of (Eu.{u} n)) h hU hV hAU hBV hA.isClosed
    hBc.isClosed (fun _ ↦ isClosed_singleton) hAB (good_of_isCompact hfin hBc)

/-- A space in which every point has an open neighbourhood homeomorphic to an open subset of
`ℝⁿ`. -/
def LocallyEuclidean (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ Nonempty (U ≃ₜ V)

omit [T2Space M] in
lemma LocallyEuclidean.exists_homeo (hM : LocallyEuclidean n M) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ V : Set (Eu.{u} n), IsOpen V ∧ Nonempty (U ≃ₜ V) := by
  obtain ⟨U, hU, hxU, V, hV, ⟨h⟩⟩ := hM x
  exact ⟨U, hU, hxU, toEu n '' V, (toEu n).isOpenMap _ hV, ⟨h.trans ((toEu n).image V)⟩⟩

omit [T2Space M] in
lemma locallyEuclidean_of_chartedSpace [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    LocallyEuclidean n M := fun x ↦
  ⟨_, (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source, mem_chart_source _ x, _,
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_target,
    ⟨(chartAt (EuclideanSpace ℝ (Fin n)) x).toHomeomorphSourceTarget⟩⟩

/-- Any two nonzero local classes at a point of a locally Euclidean space agree. -/
theorem locH_point_eq_of_locallyEuclidean (hM : LocallyEuclidean n M) {m : ℕ} (hm : n = m + 1)
    (x : M) (α β : locH (X := 𝕄) (m + 1) ({x} : Set M)) (hα : α ≠ 0) (hβ : β ≠ 0) :
    α = β := by
  obtain ⟨U, hU, hxU, V, hV, ⟨h⟩⟩ := hM.exists_homeo x
  have hfin : finrank ℝ (Eu.{u} n) = m + 1 := by rw [finrank_Eu, hm]
  exact locH_point_eq_of_homeomorph (X := 𝕄) (Y := TopCat.of (Eu.{u} n)) h hU hV
    (fun _ ↦ isClosed_singleton) (fun _ ↦ isClosed_singleton) hxU
    (locH_point_eq_of_ne_zero hfin _) α β hα hβ

/-- **A compact locally Euclidean space has a fundamental class**: it satisfies all three
properties of Hatcher's Lemma 3.27 for `A = M`. -/
theorem good_univ [CompactSpace M] (hM : LocallyEuclidean n M) {m : ℕ} (hm : n = m + 1) :
    Good (X := 𝕄) (m + 1) (univ : Set M) := by
  choose U hU hxU V hV hh using hM.exists_homeo
  -- A finite cover of `M` by closed sets inside the chart domains `U x`.
  have hnhds (x : M) : ∃ C ∈ 𝓝 x, IsClosed C ∧ C ⊆ U x :=
    exists_mem_nhds_isClosed_subset ((hU x).mem_nhds (hxU x))
  choose C hCx hCc hCs using hnhds
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover C fun x _ ↦ hCx x
  let Q : Set M → Prop := fun A ↦ IsClosed A ∧ ∃ x, A ⊆ U x
  have hgood := good_unionL_of (X := 𝕄) (n := m + 1) (by omega)
    (fun x ↦ locH_point_eq_of_locallyEuclidean hM hm x) Q
    (fun A B hA hB ↦ ⟨hA.1.inter hB.1, hA.2.elim fun x hx ↦ ⟨x, inter_subset_left.trans hx⟩⟩)
    (fun A hA ↦ hA.1)
    (fun A hA ↦ hA.2.elim fun x hx ↦
      good_of_subset_homeo hm (hU x) (hV x) (hh x).some hA.1.isCompact hx)
    (t.toList.map C) (fun P hP ↦ by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hP
      exact ⟨hCc x, x, hCs x⟩)
  have hcov : unionL (t.toList.map C) = univ := by
    refine eq_univ_of_univ_subset fun y _ ↦ ?_
    obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 (ht.2 (mem_univ y))
    exact mem_unionL.2 ⟨C x, List.mem_map.2 ⟨x, Finset.mem_toList.2 hx, rfl⟩, hy⟩
  rwa [hcov] at hgood

end Manifold

end SharpLSI.Topology

namespace SharpLSI

open SharpLSI.Topology

/-- **A compact Hausdorff space in which every point has an open neighbourhood homeomorphic to an
open subset of `ℝⁿ`, `n ≥ 1`, is not contractible.**  It has `Hₙ(M; 𝔽₂) ≠ 0` (Hatcher,
*Algebraic Topology*, Lemma 3.27), while a contractible space has vanishing homology in positive
degrees. -/
theorem not_contractible_of_locallyEuclidean {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    (hM : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ Nonempty (U ≃ₜ V)) :
    ¬ ContractibleSpace M := by
  intro hC
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨α, hα⟩ := (good_univ (M := M) (n := m + 1) hM (m := m) rfl).fund
  obtain ⟨x⟩ := ‹Nonempty M›
  have : ContractibleSpace (TopCat.of M) := hC
  exact hα x (mem_univ x) (by rw [locH_univ_eq_zero m α, map_zero])

/-- **A closed manifold of positive dimension is not contractible.** -/
theorem not_contractible_of_closed_manifold {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : ¬ ContractibleSpace M :=
  not_contractible_of_locallyEuclidean hn locallyEuclidean_of_chartedSpace

end SharpLSI
