import LeanResearch.PeriodicAttractiveLogGas.LabelOccupations

/-! Finite cell graph in the source residual-exponential proof, lines 2602–2620.
Loops count once. All counts use actual mesh labels and actual particle sets. -/

noncomputable section
open Set
open scoped BigOperators

namespace PeriodicAttractiveLogGas.ResidualCellGraph
open MeshCells MeshNearbyGeometry LabelOccupations

/-- The exact single-cell displacement window, without the extra edge endpoint. -/
def signedWindow (R : ℕ) : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)

theorem card_signedWindow (R : ℕ) : (signedWindow R).card = 2 * R + 1 := by
  rw [signedWindow, Int.card_Icc]
  omega

theorem natAbs_le_of_mem_signedWindow {R : ℕ} {z : ℤ} (hz : z ∈ signedWindow R) :
    z.natAbs ≤ R := by
  have hz' : -(R : ℤ) ≤ z ∧ z ≤ R := Finset.mem_Icc.mp hz
  have ha := abs_le.mpr hz'
  rw [Int.abs_eq_natAbs] at ha
  exact_mod_cast ha

theorem signedWindow_cast_injective {J R : ℕ} (hJ : 2 * R < J)
    {u v : ℤ} (hu : u ∈ signedWindow R) (hv : v ∈ signedWindow R)
    (he : (u : ZMod J) = (v : ZMod J)) : u = v := by
  obtain ⟨k, hk⟩ := exists_integer_period he
  have hu' : -(R : ℤ) ≤ u ∧ u ≤ R := Finset.mem_Icc.mp hu
  have hv' : -(R : ℤ) ≤ v ∧ v ≤ R := Finset.mem_Icc.mp hv
  have hJ' : 2 * (R : ℤ) < J := by exact_mod_cast hJ
  have hk0 : k = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have : k ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ k := by omega
      nlinarith
  simpa only [hk0, mul_zero, add_zero] using hk

theorem shiftIndex_cast (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (d : Frequency) (j : Fin 2) :
    indexClass (shiftIndex J hJ a d) j = indexClass a j + (d j : ZMod J) := by
  change ((residueIndex J hJ ((a j : ℤ) + d j)).val : ZMod J) = _
  rw [residueIndex_cast, Int.cast_add, Int.cast_natCast]
  rfl

theorem shiftIndex_mem_nearby {J R : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (d : Frequency) (hd : ∀ j, d j ∈ signedWindow R) :
    shiftIndex J hJ a d ∈ nearbyCells R a := by
  apply (mem_nearbyCells _ _).mpr
  apply (periodicIndexDistance_le_iff _ _).mpr
  intro j
  have hm : (centeredIndexOffset a (shiftIndex J hJ a d) j).natAbs ≤ (-d j).natAbs := by
    let hJnz : NeZero J := ⟨hJ.ne'⟩
    apply ZMod.natAbs_min_of_le_div_two J
    · rw [centeredIndexOffset_cast, shiftIndex_cast, Int.cast_neg]
      abel
    · exact ZMod.natAbs_valMinAbs_le _
  simpa only [Int.natAbs_neg] using hm.trans (by
    simpa only [Int.natAbs_neg] using natAbs_le_of_mem_signedWindow (hd j))

theorem nearbyCells_eq_image (J : ℕ) (hJ : 0 < J) (R : ℕ) (a : MeshIndex J) :
    nearbyCells R a = ((signedWindow R) ×ˢ (signedWindow R)).image
      (fun p => shiftIndex J hJ a (pairFrequency p)) := by
  apply Finset.Subset.antisymm
  · intro b hb
    obtain ⟨d, hd, hc⟩ := nearby_displacement hb
    apply Finset.mem_image.mpr
    refine ⟨(d 0, d 1), Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_Icc.mpr (hd 0), Finset.mem_Icc.mpr (hd 1)⟩
    · rw [pairFrequency_coordinates]
      exact shiftIndex_eq J hJ a b d hc
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    apply shiftIndex_mem_nearby hJ
    intro j
    fin_cases j
    · simpa [pairFrequency] using (Finset.mem_product.mp hp).1
    · simpa [pairFrequency] using (Finset.mem_product.mp hp).2

theorem shiftIndex_window_injOn {J R : ℕ} (hJ : 0 < J) (hRJ : 2 * R < J)
    (a : MeshIndex J) : Set.InjOn (fun p => shiftIndex J hJ a (pairFrequency p))
      ↑((signedWindow R) ×ˢ (signedWindow R)) := by
  intro u hu v hv he
  have hc (j : Fin 2) : (pairFrequency u j : ZMod J) = (pairFrequency v j : ZMod J) := by
    have hh := congrArg (fun b => indexClass b j) he
    simp only [shiftIndex_cast] at hh
    exact add_left_cancel hh
  apply Prod.ext
  · apply signedWindow_cast_injective hRJ (Finset.mem_product.mp hu).1 (Finset.mem_product.mp hv).1
    simpa [pairFrequency] using hc 0
  · apply signedWindow_cast_injective hRJ (Finset.mem_product.mp hu).2 (Finset.mem_product.mp hv).2
    simpa [pairFrequency] using hc 1

/-- Exact source K, at the original mesh threshold. -/
theorem card_nearbyCells_exact {J R : ℕ} (hmesh : 8 * (R + 1) ≤ J)
    (a : MeshIndex J) : (nearbyCells R a).card = (2 * R + 1) ^ 2 := by
  have hJ : 0 < J := by omega
  rw [nearbyCells_eq_image J hJ R a,
    Finset.card_image_of_injOn (shiftIndex_window_injOn hJ (by omega) a)]
  simp only [Finset.card_product, card_signedWindow, pow_two]

/-- Actual unordered near-cell pairs; a loop is the singleton `{a}`. -/
def cellEdges {J : ℕ} (R : ℕ) : Finset (Finset (MeshIndex J)) :=
  Finset.univ.biUnion fun a => (nearbyCells R a).image fun b => {a, b}

theorem mem_cellEdges {J R : ℕ} {e : Finset (MeshIndex J)} :
    e ∈ cellEdges R ↔ ∃ a b, b ∈ nearbyCells R a ∧ e = {a, b} := by
  simp only [cellEdges, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨a, b, hb, he⟩
    exact ⟨a, b, hb, he.symm⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a, b, hb, rfl⟩

theorem cellEdge_nonempty {J R : ℕ} {e : Finset (MeshIndex J)}
    (he : e ∈ cellEdges R) : e.Nonempty := by
  obtain ⟨a, b, _, rfl⟩ := mem_cellEdges.mp he
  exact ⟨a, by simp⟩

theorem cellEdge_card_le_two {J R : ℕ} {e : Finset (MeshIndex J)}
    (he : e ∈ cellEdges R) : e.card ≤ 2 := by
  obtain ⟨a, b, _, rfl⟩ := mem_cellEdges.mp he
  by_cases hab : a = b <;> simp [hab]

theorem loop_mem_cellEdges {J : ℕ} (R : ℕ) (a : MeshIndex J) : {a} ∈ cellEdges R := by
  apply mem_cellEdges.mpr
  refine ⟨a, a, ?_, by simp⟩
  simp [mem_nearbyCells, periodicIndexDistance, centeredIndexOffset]

def incidentEdges {J : ℕ} (R : ℕ) (a : MeshIndex J) : Finset (Finset (MeshIndex J)) :=
  (cellEdges R).filter fun e => a ∈ e

theorem incidentEdges_eq_image {J : ℕ} (R : ℕ) (a : MeshIndex J) :
    incidentEdges R a = (nearbyCells R a).image (fun b => {a, b}) := by
  ext e
  constructor
  · intro he
    obtain ⟨he, ha⟩ := Finset.mem_filter.mp he
    obtain ⟨u, v, hv, rfl⟩ := mem_cellEdges.mp he
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · have hav : a = v := Finset.mem_singleton.mp ha
      subst v
      refine Finset.mem_image.mpr ⟨u, ?_, by simp [Finset.pair_comm]⟩
      rw [mem_nearbyCells, periodicIndexDistance_comm]
      exact (mem_nearbyCells _ _).mp hv
  · intro he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨mem_cellEdges.mpr ⟨a, b, hb, rfl⟩, by simp⟩

theorem pair_finset_injective {α : Type*} [DecidableEq α] (a : α) :
    Function.Injective (fun b : α => ({a, b} : Finset α)) := by
  intro b c he
  change ({a, b} : Finset α) = {a, c} at he
  by_cases hba : b = a
  · subst b
    have hc : c ∈ ({a, a} : Finset α) := by rw [he]; simp
    have hca : c = a := by simpa using hc
    exact hca.symm
  · have hb : b ∈ ({a, c} : Finset α) := by rw [← he]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton, hba, false_or] using hb

theorem card_incidentEdges {J R : ℕ} (hmesh : 8 * (R + 1) ≤ J) (a : MeshIndex J) :
    (incidentEdges R a).card = (2 * R + 1) ^ 2 := by
  rw [incidentEdges_eq_image, Finset.card_image_of_injOn (pair_finset_injective a).injOn]
  exact card_nearbyCells_exact hmesh a

/-- Actual particles in the one or two cells of an edge. -/
def edgeParticles {J N : ℕ} (η : LabelVector J N) (e : Finset (MeshIndex J)) : Finset (Fin N) :=
  sourceIndices η Finset.univ e

def edgeParticleCount {J N : ℕ} (η : LabelVector J N) (e : Finset (MeshIndex J)) : ℕ :=
  (edgeParticles η e).card

theorem edgeParticleCount_le_cap {J N R : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {η : LabelVector J N} (hη : OccupationCap t η)
    {e : Finset (MeshIndex J)} (he : e ∈ cellEdges R) :
    (edgeParticleCount η e : ℝ) ≤ 2 * t * N := by
  have hec : (e.card : ℝ) ≤ 2 := by exact_mod_cast cellEdge_card_le_two he
  calc
    _ ≤ (e.card : ℝ) * (t * N) := source_count_le hη Finset.univ e
    _ ≤ 2 * (t * N) := mul_le_mul_of_nonneg_right hec (mul_nonneg ht (Nat.cast_nonneg N))
    _ = _ := by ring

theorem sum_edgeParticleCount {J N R : ℕ} (hmesh : 8 * (R + 1) ≤ J)
    (η : LabelVector J N) :
    ∑ e ∈ cellEdges R, edgeParticleCount η e = (2 * R + 1) ^ 2 * N := by
  simp only [edgeParticleCount, edgeParticles, sourceIndices, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  have hcount (i : Fin N) : (∑ e ∈ cellEdges R, if η i ∈ e then (1 : ℕ) else 0) =
      (2 * R + 1) ^ 2 := by
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    exact card_incidentEdges hmesh (η i)
  simp only [hcount, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_comm _ _

theorem sum_sq_edgeParticleCount {J N R : ℕ} (hmesh : 8 * (R + 1) ≤ J)
    {t : ℝ} (ht : 0 ≤ t) {η : LabelVector J N} (hη : OccupationCap t η) :
    ∑ e ∈ cellEdges R, (edgeParticleCount η e : ℝ) ^ 2 ≤
      t * (2 * (2 * (R : ℝ) + 1) ^ 2) * N ^ 2 := by
  have hs : (∑ e ∈ cellEdges R, (edgeParticleCount η e : ℝ)) =
      (2 * (R : ℝ) + 1) ^ 2 * N := by
    exact_mod_cast sum_edgeParticleCount hmesh η
  calc
    _ ≤ ∑ e ∈ cellEdges R, (2 * t * N) * (edgeParticleCount η e : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (edgeParticleCount_le_cap ht hη he) (Nat.cast_nonneg _)
    _ = (2 * t * N) * ((2 * (R : ℝ) + 1) ^ 2 * N) := by rw [← Finset.mul_sum, hs]
    _ = _ := by ring

/-- Finite greedy coloring: at each insertion fewer than χ colors are forbidden.
This proves the supplied elementary coloring argument without an assumed coloring. -/
theorem finite_greedy_coloring {α : Type*} [DecidableEq α] (s : Finset α)
    (r : α → α → Prop) [DecidableRel r] (hsymm : ∀ {a b}, r a b → r b a)
    (hirr : ∀ a, ¬r a a) {χ : ℕ} (hχ : 0 < χ)
    (hdegree : ∀ a ∈ s, (s.filter (r a)).card < χ) :
    ∃ c : α → Fin χ, ∀ a ∈ s, ∀ b ∈ s, r a b → c a ≠ c b := by
  classical
  have aux : ∀ u : Finset α, u ⊆ s →
      ∃ c : α → Fin χ, ∀ a ∈ u, ∀ b ∈ u, r a b → c a ≠ c b := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun _ => ⟨0, hχ⟩, by simp⟩
    | @insert a u hau ih =>
      intro hus
      obtain ⟨c, hc⟩ := ih (fun x hx => hus (Finset.mem_insert_of_mem hx))
      let forbidden : Finset (Fin χ) := (u.filter (r a)).image c
      have ha : a ∈ s := hus (Finset.mem_insert_self _ _)
      have hsub : u.filter (r a) ⊆ s.filter (r a) := by
        intro x hx
        obtain ⟨hx, hr⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hus (Finset.mem_insert_of_mem hx), hr⟩
      have hcard : forbidden.card < χ :=
        (Finset.card_image_le.trans (Finset.card_le_card hsub)).trans_lt (hdegree a ha)
      obtain ⟨z, hz⟩ : ∃ z : Fin χ, z ∉ forbidden := by
        by_contra hn
        push Not at hn
        have hfull : (Finset.univ : Finset (Fin χ)) ⊆ forbidden := fun z _ => hn z
        have hh := Finset.card_le_card hfull
        simp only [Finset.card_univ, Fintype.card_fin] at hh
        omega
      refine ⟨Function.update c a z, ?_⟩
      intro x hx y hy hrxy
      rcases Finset.mem_insert.mp hx with hxa | hxu
      · subst x
        by_cases hya : y = a
        · subst y
          exact (hirr a hrxy).elim
        · rw [Function.update_self, Function.update_of_ne hya]
          intro hzy
          apply hz
          exact Finset.mem_image.mpr ⟨y,
            Finset.mem_filter.mpr ⟨(Finset.mem_insert.mp hy).resolve_left hya, hrxy⟩,
            hzy.symm⟩
      · have hxa : x ≠ a := fun he => hau (he ▸ hxu)
        rcases Finset.mem_insert.mp hy with hya | hyu
        · subst y
          rw [Function.update_of_ne hxa, Function.update_self]
          intro hxz
          apply hz
          exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxu, hsymm hrxy⟩, hxz⟩
        · have hya : y ≠ a := fun he => hau (he ▸ hyu)
          simpa only [Function.update_of_ne hxa, Function.update_of_ne hya] using hc x hxu y hyu hrxy
  exact aux s (Finset.Subset.refl _)

def edgesConflict {J : ℕ} (e d : Finset (MeshIndex J)) : Prop :=
  e ≠ d ∧ ¬Disjoint e d

instance {J : ℕ} : DecidableRel (@edgesConflict J) := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The source ordinary-edge bound, valid also for loops. The common edge is
subtracted once in the incident union and once when excluding self-conflict. -/
theorem conflicting_edges_card_le {J R : ℕ} (hmesh : 8 * (R + 1) ≤ J)
    {e : Finset (MeshIndex J)} (he : e ∈ cellEdges R) :
    ((cellEdges R).filter (edgesConflict e)).card ≤ 2 * (2 * R + 1) ^ 2 - 2 := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := mem_cellEdges.mp he
  let U := incidentEdges R a ∪ incidentEdges R b
  have he : ({a, b} : Finset (MeshIndex J)) ∈ cellEdges R :=
    mem_cellEdges.mpr ⟨a, b, hb, rfl⟩
  have hU : ({a, b} : Finset (MeshIndex J)) ∈ U :=
    Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, by simp⟩)
  have hsub : (cellEdges R).filter (edgesConflict {a, b}) ⊆ U.erase {a, b} := by
    intro d hd
    obtain ⟨hd, hne, hmeet⟩ := Finset.mem_filter.mp hd
    have hab : a ∈ d ∨ b ∈ d := by
      by_contra hn
      push Not at hn
      apply hmeet
      apply Finset.disjoint_left.mpr
      intro x hx hxd
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hn.1 hxd
      · have hxb : x = b := Finset.mem_singleton.mp hx
        exact hn.2 (hxb ▸ hxd)
    apply Finset.mem_erase.mpr
    refine ⟨hne.symm, ?_⟩
    rcases hab with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, hb⟩)
  have hI : 0 < (incidentEdges R a ∩ incidentEdges R b).card := by
    apply Finset.card_pos.mpr
    exact ⟨{a, b}, Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨he, by simp⟩, Finset.mem_filter.mpr ⟨he, by simp⟩⟩⟩
  have hUc := Finset.card_union_add_card_inter (incidentEdges R a) (incidentEdges R b)
  rw [card_incidentEdges hmesh, card_incidentEdges hmesh] at hUc
  change U.card + (incidentEdges R a ∩ incidentEdges R b).card = _ at hUc
  have hUp : 0 < U.card := Finset.card_pos.mpr ⟨_, hU⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hU] at hc
  omega

theorem conflicting_loop_edges_card_le {J R : ℕ} (hmesh : 8 * (R + 1) ≤ J)
    (a : MeshIndex J) :
    ((cellEdges R).filter (edgesConflict {a})).card ≤ (2 * R + 1) ^ 2 - 1 := by
  have hsub : (cellEdges R).filter (edgesConflict {a}) ⊆ (incidentEdges R a).erase {a} := by
    intro d hd
    obtain ⟨hd, hne, hmeet⟩ := Finset.mem_filter.mp hd
    have ha : a ∈ d := by
      by_contra hn
      apply hmeet
      apply Finset.disjoint_left.mpr
      intro x hx hxd
      have hxa : x = a := Finset.mem_singleton.mp hx
      exact hn (hxa ▸ hxd)
    exact Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_filter.mpr ⟨hd, ha⟩⟩
  have hloop : ({a} : Finset (MeshIndex J)) ∈ incidentEdges R a :=
    Finset.mem_filter.mpr ⟨loop_mem_cellEdges R a, by simp⟩
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem hloop, card_incidentEdges hmesh] at hc

theorem conflicting_edges_card_lt {J R : ℕ} (hmesh : 8 * (R + 1) ≤ J)
    {e : Finset (MeshIndex J)} (he : e ∈ cellEdges R) :
    ((cellEdges R).filter (edgesConflict e)).card < 2 * (2 * R + 1) ^ 2 := by
  have hh := conflicting_edges_card_le hmesh he
  have hp : 0 < (2 * R + 1) ^ 2 := by positivity
  omega

/-- The actual loop graph has a proved coloring into the source χ=2K colors.
Equal-colored distinct edges have disjoint cell sets. -/
theorem exists_cell_edge_coloring {J R : ℕ} (hmesh : 8 * (R + 1) ≤ J) :
    ∃ c : Finset (MeshIndex J) → Fin (2 * (2 * R + 1) ^ 2),
      ∀ e ∈ cellEdges R, ∀ d ∈ cellEdges R, e ≠ d → c e = c d → Disjoint e d := by
  classical
  obtain ⟨c, hc⟩ := finite_greedy_coloring (cellEdges R) edgesConflict
    (fun h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩)
    (fun _ h => h.1 rfl) (by positivity)
    (fun _ he => conflicting_edges_card_lt hmesh he)
  refine ⟨c, ?_⟩
  intro e he d hd hne hcolor
  by_contra hmeet
  exact hc e he d hd ⟨hne, hmeet⟩ hcolor

theorem edgeParticles_disjoint {J N : ℕ} (η : LabelVector J N)
    {e d : Finset (MeshIndex J)} (hed : Disjoint e d) :
    Disjoint (edgeParticles η e) (edgeParticles η d) := by
  apply Finset.disjoint_left.mpr
  intro i hi hid
  exact Finset.disjoint_left.mp hed
    ((mem_sourceIndices η Finset.univ e i).mp hi).2
    ((mem_sourceIndices η Finset.univ d i).mp hid).2

end PeriodicAttractiveLogGas.ResidualCellGraph
