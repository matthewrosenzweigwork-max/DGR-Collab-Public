import SharpSymmetricLSI.Infra.Topology.LocalEuclidean
import SharpSymmetricLSI.Infra.Topology.CompactSupport

/-!
# Compact subsets of a Euclidean space are `Good`

Let `E` be a real inner product space of dimension `n + 1`.  Following Hatcher, *Algebraic
Topology*, Lemma 3.27, step (3):

* a finite union of closed bounded convex sets is `Good`, by induction on the number of pieces
  using the gluing step `Good.union` (`good_unionL`);
* an arbitrary compact set `A` is the intersection of a decreasing sequence `K m` of finite unions
  of closed convex pieces, each piece meeting `A` and of radius at most `1 / (m + 1)` around a point
  of `A`.  By compact supports (`exists_restr_eq_of_iInter`) every class on `A` comes from some
  `K m`, which gives the vanishing and injectivity statements; a large ball gives a fundamental
  class (`good_of_isCompact`).
-/

universe u

open CategoryTheory Limits Set Metric Module TopCat

namespace SharpLSI.Topology

/-- The union of a list of sets. -/
def unionL {α : Type*} (L : List (Set α)) : Set α := L.foldr (· ∪ ·) ∅

@[simp] lemma unionL_nil {α : Type*} : unionL ([] : List (Set α)) = ∅ := rfl

@[simp] lemma unionL_cons {α : Type*} (C : Set α) (L : List (Set α)) :
    unionL (C :: L) = C ∪ unionL L := rfl

lemma mem_unionL {α : Type*} {L : List (Set α)} {x : α} : x ∈ unionL L ↔ ∃ P ∈ L, x ∈ P := by
  induction L with
  | nil => simp
  | cons C L ih => simp [ih]

lemma inter_unionL {α : Type*} (C : Set α) (L : List (Set α)) :
    C ∩ unionL L = unionL (L.map (C ∩ ·)) := by
  induction L with
  | nil => simp
  | cons D L ih => simp [inter_union_distrib_left, ih]

lemma isClosed_unionL {α : Type*} [TopologicalSpace α] {L : List (Set α)}
    (hL : ∀ P ∈ L, IsClosed P) : IsClosed (unionL L) := by
  induction L with
  | nil => exact isClosed_empty
  | cons C L ih =>
    exact (hL C List.mem_cons_self).union (ih fun P hP ↦ hL P (List.mem_cons_of_mem _ hP))

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "𝔼" => TopCat.of E

/-- A set which is convex, closed and bounded. -/
def IsCCB (P : Set E) : Prop := Convex ℝ P ∧ IsClosed P ∧ Bornology.IsBounded P

lemma IsCCB.inter {P Q : Set E} (hP : IsCCB P) (hQ : IsCCB Q) : IsCCB (P ∩ Q) :=
  ⟨hP.1.inter hQ.1, hP.2.1.inter hQ.2.1, hP.2.2.subset inter_subset_left⟩

/-- **Finite unions of closed bounded convex sets are `Good`.** -/
theorem good_unionL {n : ℕ} (hn : finrank ℝ E = n + 1) :
    ∀ L : List (Set E), (∀ P ∈ L, IsCCB P) → Good (X := 𝔼) (n + 1) (unionL L) := by
  suffices ∀ m, ∀ L : List (Set E), L.length = m → (∀ P ∈ L, IsCCB P) →
      Good (X := 𝔼) (n + 1) (unionL L) from fun L ↦ this _ L rfl
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
      have hC : IsCCB C := hL C List.mem_cons_self
      have hL' : ∀ P ∈ L, IsCCB P := fun P hP ↦ hL P (List.mem_cons_of_mem _ hP)
      have hloc : ∀ x : 𝔼, ∀ α β : locH (n + 1) ({x} : Set 𝔼), α ≠ 0 → β ≠ 0 → α = β :=
        fun x ↦ locH_point_eq_of_ne_zero hn x
      have g₁ : Good (X := 𝔼) (n + 1) C := good_of_convex hn hC.1 hC.2.2
      have g₂ : Good (X := 𝔼) (n + 1) (unionL L) := ih L hlen hL'
      have g₃ : Good (X := 𝔼) (n + 1) (C ∩ unionL L) := by
        rw [inter_unionL]
        refine ih _ (by simp [hlen]) fun P hP ↦ ?_
        obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hP
        exact hC.inter (hL' Q hQ)
      have hc₁ : IsClosed (C : Set 𝔼) := hC.2.1
      have hc₂ : IsClosed (unionL L : Set 𝔼) := isClosed_unionL fun P hP ↦ (hL' P hP).2.1
      exact Good.union (n := n + 1) (by omega) hloc hc₁ hc₂ g₁ g₂ g₃

/-- The radius at stage `m`. -/
noncomputable def radius (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

lemma radius_pos (m : ℕ) : 0 < radius m := by unfold radius; positivity

open Classical in
/-- The pieces of the `m`-th approximation of `A` from the centers `cs`. -/
noncomputable def pieces (A : Set E) (cs : ℕ → List E) : ℕ → List (Set E)
  | 0 => [univ]
  | m + 1 => ((pieces A cs m).flatMap fun P ↦ (cs m).map fun c ↦ P ∩ closedBall c (radius m)).filter
      fun P ↦ decide (P ∩ A).Nonempty

section Pieces

variable {A : Set E} {cs : ℕ → List E}

omit [InnerProductSpace ℝ E] in
lemma mem_pieces_succ {m : ℕ} {P : Set E} :
    P ∈ pieces A cs (m + 1) ↔
      (∃ Q ∈ pieces A cs m, ∃ c ∈ cs m, P = Q ∩ closedBall c (radius m)) ∧ (P ∩ A).Nonempty := by
  simp only [pieces, List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨Q, hQ, c, hc, rfl⟩, h⟩
    exact ⟨⟨Q, hQ, c, hc, rfl⟩, h⟩
  · rintro ⟨⟨Q, hQ, c, hc, rfl⟩, h⟩
    exact ⟨⟨Q, hQ, c, hc, rfl⟩, h⟩

lemma pieces_convex_closed (m : ℕ) : ∀ P ∈ pieces A cs m, Convex ℝ P ∧ IsClosed P := by
  induction m with
  | zero => simp [pieces, convex_univ, isClosed_univ]
  | succ m ih =>
    intro P hP
    obtain ⟨⟨Q, hQ, c, -, rfl⟩, -⟩ := mem_pieces_succ.1 hP
    exact ⟨(ih Q hQ).1.inter (convex_closedBall c _), (ih Q hQ).2.inter isClosed_closedBall⟩

lemma pieces_isCCB (hcsA : ∀ m, ∀ c ∈ cs m, c ∈ A) (m : ℕ) {P : Set E}
    (hP : P ∈ pieces A cs (m + 1)) :
    IsCCB P ∧ (P ∩ A).Nonempty ∧ ∃ c ∈ A, P ⊆ closedBall c (radius m) := by
  obtain ⟨⟨Q, hQ, c, hc, rfl⟩, hA⟩ := mem_pieces_succ.1 hP
  have hQ' := pieces_convex_closed m Q hQ
  exact ⟨⟨hQ'.1.inter (convex_closedBall c _), hQ'.2.inter isClosed_closedBall,
    isBounded_closedBall.subset inter_subset_right⟩, hA, c, hcsA m c hc, inter_subset_right⟩

omit [InnerProductSpace ℝ E] in
lemma subset_unionL_pieces (hcs : ∀ m, ∀ a ∈ A, ∃ c ∈ cs m, a ∈ closedBall c (radius m))
    (m : ℕ) : A ⊆ unionL (pieces A cs m) := by
  induction m with
  | zero => simp [pieces]
  | succ m ih =>
    intro a ha
    obtain ⟨Q, hQ, haQ⟩ := mem_unionL.1 (ih ha)
    obtain ⟨c, hc, hac⟩ := hcs m a ha
    exact mem_unionL.2 ⟨Q ∩ closedBall c (radius m),
      mem_pieces_succ.2 ⟨⟨Q, hQ, c, hc, rfl⟩, ⟨a, ⟨haQ, hac⟩, ha⟩⟩, haQ, hac⟩

omit [InnerProductSpace ℝ E] in
lemma unionL_pieces_succ_subset (m : ℕ) :
    unionL (pieces A cs (m + 1)) ⊆ unionL (pieces A cs m) := by
  intro y hy
  obtain ⟨P, hP, hyP⟩ := mem_unionL.1 hy
  obtain ⟨⟨Q, hQ, c, -, rfl⟩, -⟩ := mem_pieces_succ.1 hP
  exact mem_unionL.2 ⟨Q, hQ, hyP.1⟩

end Pieces

/-- **Compact subsets of a Euclidean space are `Good`.** -/
theorem good_of_isCompact {n : ℕ} (hn : finrank ℝ E = n + 1) {A : Set E} (hA : IsCompact A) :
    Good (X := 𝔼) (n + 1) A := by
  -- Centers of finite covers of `A` by balls of radius `1 / (m + 1)`.
  have hcov : ∀ m : ℕ, ∃ l : List E, (∀ c ∈ l, c ∈ A) ∧
      ∀ a ∈ A, ∃ c ∈ l, a ∈ closedBall c (radius m) := by
    intro m
    obtain ⟨t, htA, htf, htcov⟩ := finite_cover_balls_of_compact hA (radius_pos m)
    refine ⟨htf.toFinset.toList, fun c hc ↦ htA (by simpa using hc), fun a ha ↦ ?_⟩
    obtain ⟨c, hc, hac⟩ := mem_iUnion₂.1 (htcov ha)
    exact ⟨c, by simpa using hc, ball_subset_closedBall hac⟩
  choose cs hcsA hcs using hcov
  -- The decreasing approximations `K m ⊇ A`.
  let K : ℕ → Set E := fun m ↦ unionL (pieces A cs (m + 1))
  have hK : Antitone K := antitone_nat_of_succ_le fun m ↦ unionL_pieces_succ_subset (m + 1)
  have hAK : ∀ m, A ⊆ K m := fun m ↦ subset_unionL_pieces hcs (m + 1)
  have hKc : ∀ m, IsClosed (K m) :=
    fun m ↦ isClosed_unionL fun P hP ↦ (pieces_isCCB hcsA m hP).1.2.1
  have hKgood : ∀ m, Good (X := 𝔼) (n + 1) (K m) :=
    fun m ↦ good_unionL hn _ fun P hP ↦ (pieces_isCCB hcsA m hP).1
  have hinter : ⋂ m, K m ⊆ A := by
    intro y hy
    rw [← hA.isClosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨P, hP, hyP⟩ := mem_unionL.1 (mem_iInter.1 hy m)
    obtain ⟨-, -, c, hc, hPc⟩ := pieces_isCCB hcsA m hP
    exact ⟨c, hc, (mem_closedBall.1 (hPc hyP)).trans_lt hm⟩
  -- The homology of `E` vanishes in positive degrees.
  have hX : ∀ i, ∀ a : ((toSSet.obj (TopCat.of (univ : Set 𝔼))).homology R2 (i + 1) :
      ModuleCat.{u} F2.{u}), a = 0 := by
    intro i a
    have : ContractibleSpace (TopCat.of (univ : Set 𝔼)) := contractibleSpace_univ (E := E)
    exact (ModuleCat.subsingleton_of_isZero
      (TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace R2
        (TopCat.of (univ : Set 𝔼)) (n := i + 1) (by omega))).elim _ _
  refine ⟨fun i hi z ↦ ?_, fun z hz ↦ ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    obtain ⟨m, z', rfl⟩ := exists_restr_eq_of_iInter hX hK hAK hKc hinter k z
    rw [(hKgood m).vanish (k + 1) hi z', map_zero]
  · obtain ⟨m, z', rfl⟩ := exists_restr_eq_of_iInter hX hK hAK hKc hinter n z
    suffices z' = 0 by rw [this, map_zero]
    refine (hKgood m).inj z' fun y hy ↦ ?_
    obtain ⟨P, hP, hyP⟩ := mem_unionL.1 hy
    obtain ⟨hPc, ⟨a, haP, haA⟩, -⟩ := pieces_isCCB hcsA m hP
    have hPK : P ⊆ K m := fun x hx ↦ mem_unionL.2 ⟨P, hP, hx⟩
    have hw : restr (X := 𝔼) (n + 1) hPK z' = 0 := by
      have hiso := isIso_restr_of_convex hPc.1 hPc.2.2 haP n
      refine (ConcreteCategory.bijective_of_isIso
        (restr (X := 𝔼) (n + 1) (singleton_subset_iff.2 haP))).1 ?_
      rw [map_zero, restr_restr]
      have := hz a haA
      rwa [restr_restr] at this
    rw [← restr_restr (n + 1) (singleton_subset_iff.2 hyP) hPK, hw, map_zero]
  · obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
    obtain ⟨α, hα⟩ := (good_of_convex hn (convex_closedBall (0 : E) R) isBounded_closedBall).fund
    refine ⟨restr (X := 𝔼) (n + 1) hR α, fun x hx ↦ ?_⟩
    rw [restr_restr]
    exact hα x (hR hx)

end SharpLSI.Topology
