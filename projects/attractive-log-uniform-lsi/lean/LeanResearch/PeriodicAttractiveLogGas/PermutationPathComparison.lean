import LeanResearch.PeriodicAttractiveLogGas.FibreProjection
import LeanResearch.PeriodicAttractiveLogGas.BoundaryEdgeSummation
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.Order.Chebyshev

/-! Source Proposition `permutation-paths`, lines 2752--2784: comparison
on the actual outer capped label graph. The paths change two specified
particles, and their weights remain the original unconditioned label masses.
Development checking and source correspondence are recorded in the companion
review note; no protected acceptance is asserted here. -/

noncomputable section
open Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.PermutationPathComparison

open MeshCells MeshAdjacentCells MeshNearbyGeometry LabelOccupations
  LabelExchangeability LabelRatioTransport CellRestrictions ConditionalLawEstimates
  DiscreteOccupationIdentities FibreProjection

section LabelMoves

variable {J N : ℕ} {v t : ℝ}

theorem occupation_update_le (η : LabelVector J N) (i : Fin N)
    (c d : MeshIndex J) : occupation (Function.update η i c) d ≤ occupation η d + 1 := by
  rw [occupation_update η i (η i) c rfl]
  unfold moveOccupation
  split_ifs <;> omega

/-- One spare place in the outer cap admits every intermediate cell. -/
theorem update_cap (hbuffer : 1 ≤ (t - v) * N) {η : LabelVector J N}
    (hη : OccupationCap v η) (i : Fin N) (c : MeshIndex J) :
    OccupationCap t (Function.update η i c) := by
  intro d
  have hc : (occupation (Function.update η i c) d : ℝ) ≤ occupation η d + 1 := by
    exact_mod_cast occupation_update_le η i c d
  have hv := hη d
  nlinarith

def oneMove (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) (i : Fin N) (c : MeshIndex J) : LabelState J N t :=
  ⟨Function.update η.val i c, update_cap hbuffer hη i c⟩

@[simp] theorem oneMove_val (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) (i : Fin N) (c : MeshIndex J) :
    (oneMove hbuffer η hη i c).val = Function.update η.val i c := rfl

@[simp] theorem oneMove_start (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) (i : Fin N) : oneMove hbuffer η hη i (η.val i) = η := by
  apply Subtype.ext
  simp only [oneMove_val, Function.update_eq_self]

theorem oneMove_adjacent (hJ : 0 < J) (hbuffer : 1 ≤ (t - v) * N)
    (η : LabelState J N t) (hη : OccupationCap v η.val) (i : Fin N)
    {c d : MeshIndex J} (hcd : EdgeAdjacent J hJ c d) :
    LabelAdjacent hJ (oneMove hbuffer η hη i c) (oneMove hbuffer η hη i d) := by
  refine ⟨i, ?_, ?_⟩
  · simpa only [oneMove_val, Function.update_self] using hcd
  · simp only [oneMove_val, Function.update_self, Function.update_idem]

/-- The second half has the same occupation as the one-coordinate move.
Its specified particles are literally interchanged. -/
theorem second_half_value (η : LabelVector J N) {i j : Fin N} (hij : i ≠ j)
    (c : MeshIndex J) :
    Function.update (Function.update η i (η j)) j c =
      Function.update η i c ∘ Equiv.swap i j := by
  classical
  funext p
  by_cases hpi : p = i
  · subst p
    simp [hij, hij.symm]
  · by_cases hpj : p = j
    · subst p
      simp
    · simp [hpi, hpj, Equiv.swap_apply_of_ne_of_ne hpi hpj]

theorem second_half_join (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) {i j : Fin N} (hij : i ≠ j) :
    permutedLabel (Equiv.swap i j) (oneMove hbuffer η hη i (η.val j)) =
      oneMove hbuffer η hη i (η.val j) := by
  apply Subtype.ext
  rw [show (permutedLabel (Equiv.swap i j) (oneMove hbuffer η hη i (η.val j))).val =
      Function.update η.val i (η.val j) ∘ Equiv.swap i j from rfl,
    ← second_half_value η.val hij]
  funext p
  change Function.update (Function.update η.val i (η.val j)) j (η.val j) p =
    Function.update η.val i (η.val j) p
  by_cases hp : p = j
  · subst p
    simp only [Function.update_self, Function.update_of_ne hij.symm]
  · exact Function.update_of_ne hp _ _

theorem oneMove_weight_lower {β β₀ δ Cg : ℝ} (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (htδ : t ≤ δ)
    (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hbuffer : 1 ≤ (t - v) * N)
    (η : LabelState J N t) (hη : OccupationCap v η.val) (i : Fin N) (c : MeshIndex J) :
    CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀) *
      labelWeight (mesh_pos hmesh) β η ≤
        labelWeight (mesh_pos hmesh) β (oneMove hbuffer η hη i c) := by
  have h := specified_label_ratio hN hβ hβ₀ hsub hδ₀ hδ hCg hg hmesh η.val
    (oneMove hbuffer η hη i c).val (η.property.mono htδ)
    ((oneMove hbuffer η hη i c).property.mono htδ) i
    (fun k hk => Function.update_of_ne hk _ _)
  exact (le_div_iff₀ (labelWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) η)).mp
    h.2.2.1

/-- Both actual intermediate endpoint weights give the required conductance. -/
theorem conductance_lower {β κ w : ℝ} (hJ : 0 < J)
    {η ζ : LabelState J N t} (he : LabelAdjacent hJ η ζ)
    (hη : 0 < labelWeight hJ β η) (hζ : 0 < labelWeight hJ β ζ)
    (hleft : κ * w ≤ labelWeight hJ β η)
    (hright : κ * w ≤ labelWeight hJ β ζ) :
    κ * w / 2 ≤ labelConductance hJ β η ζ := by
  classical
  rw [labelConductance, ite_eq_left he]
  apply (le_div_iff₀ (add_pos hη hζ)).mpr
  have h1 := mul_le_mul_of_nonneg_right hleft hζ.le
  have h2 := mul_le_mul_of_nonneg_right hright hη.le
  nlinarith

end LabelMoves

section CellPaths

variable {J : ℕ}

def cellGraph (hJ : 0 < J) (hJ2 : 2 ≤ J) : SimpleGraph (MeshIndex J) where
  Adj := EdgeAdjacent J hJ
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.ne hJ2 rfl⟩

def coordinateCell (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) (z : ℤ) : MeshIndex J :=
  Function.update a j (residueIndex J hJ ((a j : ℤ) + z))

theorem coordinateCell_class (hJ : 0 < J) (a : MeshIndex J) (j k : Fin 2) (z : ℤ) :
    indexClass (coordinateCell hJ a j z) k =
      indexClass a k + if k = j then (z : ZMod J) else 0 := by
  by_cases hk : k = j
  · subst k
    simp only [coordinateCell, indexClass, Function.update_self, residueIndex_cast,
      Int.cast_add, Int.cast_natCast, ite_true]
  · simp only [coordinateCell, indexClass, Function.update_of_ne hk, hk, ite_false, add_zero]

@[simp] theorem coordinateCell_zero (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    coordinateCell hJ a j 0 = a := by
  funext k
  apply fin_cast_zmod_injective
  change indexClass (coordinateCell hJ a j 0) k = indexClass a k
  simp only [coordinateCell_class, Int.cast_zero, ite_self, add_zero]

theorem coordinateCell_add_one (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) (z : ℤ) :
    coordinateCell hJ a j (z + 1) = nextCell J hJ (coordinateCell hJ a j z) j := by
  funext k
  apply fin_cast_zmod_injective
  change indexClass (coordinateCell hJ a j (z + 1)) k =
    indexClass (nextCell J hJ (coordinateCell hJ a j z) j) k
  rw [nextCell_indexClass]
  simp only [coordinateCell_class, integerEdgeStep, Int.cast_add, Int.cast_one]
  by_cases hk : k = j <;> simp only [hk, ite_true, ite_false, Int.cast_one, Int.cast_zero] <;> abel

theorem coordinateCell_offset (hJ : 0 < J) (a b : MeshIndex J) (j : Fin 2) :
    coordinateCell hJ a j (centeredIndexOffset b a j) = Function.update a j (b j) := by
  funext k
  by_cases hk : k = j
  · subst k
    apply fin_cast_zmod_injective
    simp only [Function.update_self]
    change indexClass (coordinateCell hJ a j (centeredIndexOffset b a j)) j = indexClass b j
    simp only [coordinateCell_class, ite_true, centeredIndexOffset_cast]
    abel
  · simp only [coordinateCell, Function.update_of_ne hk]

theorem exists_coordinate_walk_nat (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) (n : ℕ) :
    ∃ p : (cellGraph hJ hJ2).Walk a (coordinateCell hJ a j n), p.length = n := by
  induction n with
  | zero =>
      change ∃ p : (cellGraph hJ hJ2).Walk a (coordinateCell hJ a j 0), p.length = 0
      rw [coordinateCell_zero]
      exact ⟨.nil, rfl⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      have he : (cellGraph hJ hJ2).Adj (coordinateCell hJ a j n)
          (coordinateCell hJ a j (n + 1 : ℕ)) := by
        change EdgeAdjacent J hJ _ _
        rw [Nat.cast_add, Nat.cast_one, coordinateCell_add_one]
        exact edgeAdjacent_nextCell J hJ _ j
      exact ⟨p.concat he, by simp only [SimpleGraph.Walk.length_concat, hp]⟩

theorem exists_coordinate_walk_neg (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) (n : ℕ) :
    ∃ p : (cellGraph hJ hJ2).Walk a (coordinateCell hJ a j (-n)), p.length = n := by
  induction n with
  | zero =>
      change ∃ p : (cellGraph hJ hJ2).Walk a (coordinateCell hJ a j 0), p.length = 0
      rw [coordinateCell_zero]
      exact ⟨.nil, rfl⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      have hnext := coordinateCell_add_one hJ a j (-(n + 1 : ℕ))
      have heq : (-(n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
      rw [heq] at hnext
      have he : (cellGraph hJ hJ2).Adj (coordinateCell hJ a j (-n))
          (coordinateCell hJ a j (-(n + 1 : ℕ))) := by
        change EdgeAdjacent J hJ _ _
        rw [hnext]
        exact (edgeAdjacent_nextCell J hJ _ j).symm
      exact ⟨p.concat he, by simp only [SimpleGraph.Walk.length_concat, hp]⟩

theorem exists_coordinate_walk_int (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) (z : ℤ) :
    ∃ p : (cellGraph hJ hJ2).Walk a (coordinateCell hJ a j z), p.length = z.natAbs := by
  cases z with
  | ofNat n => exact exists_coordinate_walk_nat hJ hJ2 a j n
  | negSucc n =>
      obtain ⟨p, hp⟩ := exists_coordinate_walk_neg hJ hJ2 a j (n + 1)
      have he : coordinateCell hJ a j (-((n + 1 : ℕ) : ℤ)) =
          coordinateCell hJ a j (Int.negSucc n) := by congr 1
      refine ⟨p.copy rfl he, ?_⟩
      rw [SimpleGraph.Walk.length_copy]
      change p.length = n + 1
      exact hp

/-- Each cyclic coordinate admits a shortest direction of at most J/2 steps. -/
theorem exists_coordinate_short_walk (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a b : MeshIndex J) (j : Fin 2) :
    ∃ p : (cellGraph hJ hJ2).Walk a (Function.update a j (b j)), p.length ≤ J / 2 := by
  obtain ⟨p, hp⟩ := exists_coordinate_walk_int hJ hJ2 a j (centeredIndexOffset b a j)
  refine ⟨p.copy rfl (coordinateCell_offset hJ a b j), ?_⟩
  rw [SimpleGraph.Walk.length_copy, hp]
  let : NeZero J := ⟨hJ.ne'⟩
  exact ZMod.natAbs_valMinAbs_le _

/-- Concatenating the two shortest coordinate routes proves the diameter bound. -/
theorem exists_cell_walk (hJ : 0 < J) (hJ2 : 2 ≤ J) (a b : MeshIndex J) :
    ∃ p : (cellGraph hJ hJ2).Walk a b, p.length ≤ J := by
  obtain ⟨p, hp⟩ := exists_coordinate_short_walk hJ hJ2 a b 0
  obtain ⟨q, hq⟩ := exists_coordinate_short_walk hJ hJ2 (Function.update a 0 (b 0)) b 1
  have hend : Function.update (Function.update a 0 (b 0)) 1 (b 1) = b := by
    funext k
    fin_cases k <;> simp
  refine ⟨(p.append q).copy rfl hend, ?_⟩
  simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_append]
  omega

theorem exists_shortest_cell_path (hJ : 0 < J) (hJ2 : 2 ≤ J) (a b : MeshIndex J) :
    ∃ p : (cellGraph hJ hJ2).Walk a b,
      p.IsPath ∧ p.length = (cellGraph hJ hJ2).dist a b ∧ p.length ≤ J := by
  obtain ⟨w, hw⟩ := exists_cell_walk hJ hJ2 a b
  obtain ⟨p, hp, hdist⟩ := w.reachable.exists_path_of_dist
  exact ⟨p, hp, hdist, hdist ▸ (SimpleGraph.dist_le w).trans hw⟩

/-- A single deterministic choice for each ordered pair of actual cells. -/
def cellPath (hJ : 0 < J) (hJ2 : 2 ≤ J) (a b : MeshIndex J) :
    (cellGraph hJ hJ2).Walk a b := (exists_shortest_cell_path hJ hJ2 a b).choose

theorem cellPath_isPath (hJ : 0 < J) (hJ2 : 2 ≤ J) (a b : MeshIndex J) :
    (cellPath hJ hJ2 a b).IsPath := (exists_shortest_cell_path hJ hJ2 a b).choose_spec.1

theorem cellPath_length_le (hJ : 0 < J) (hJ2 : 2 ≤ J) (a b : MeshIndex J) :
    (cellPath hJ hJ2 a b).length ≤ J :=
  (exists_shortest_cell_path hJ hJ2 a b).choose_spec.2.2

theorem cellPath_length_eq_dist (hJ : 0 < J) (hJ2 : 2 ≤ J) (a b : MeshIndex J) :
    (cellPath hJ hJ2 a b).length = (cellGraph hJ hJ2).dist a b :=
  (exists_shortest_cell_path hJ hJ2 a b).choose_spec.2.1

end CellPaths

section TwoParticlePaths

open BoundaryEdgeSummation

variable {J N : ℕ} {v t : ℝ}

def movingSite (i j : Fin N) (half : Bool) : Fin N := if half then j else i

def partnerSite (i j : Fin N) (half : Bool) : Fin N := if half then i else j

theorem partnerSite_ne {i j : Fin N} (hij : i ≠ j) (half : Bool) :
    partnerSite i j half ≠ movingSite i j half := by
  cases half
  · exact hij.symm
  · exact hij

def phaseState (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) (i j : Fin N) (half : Bool) (c : MeshIndex J) :
    LabelState J N t :=
  if half then permutedLabel (Equiv.swap i j) (oneMove hbuffer η hη i c)
    else oneMove hbuffer η hη i c

/-- Both halves have the literal source profile `n - e_a + e_c`, with
the unchanged case represented by the existing natural-count update. -/
theorem phaseState_occupation (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) (i j : Fin N) (half : Bool) (c : MeshIndex J) :
    occupation (phaseState hbuffer η hη i j half c).val =
      moveOccupation (occupation η.val) (η.val i) c := by
  cases half
  · exact occupation_update η.val i (η.val i) c rfl
  · change occupation (Function.update η.val i c ∘ Equiv.swap i j) = _
    rw [occupation_permute]
    exact occupation_update η.val i (η.val i) c rfl

theorem phaseState_moving (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) {i j : Fin N} (_hij : i ≠ j)
    (half : Bool) (c : MeshIndex J) :
    (phaseState hbuffer η hη i j half c).val (movingSite i j half) = c := by
  cases half <;> simp [phaseState, movingSite, oneMove, permutedLabel]

theorem phaseState_partner (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) {i j : Fin N} (hij : i ≠ j)
    (half : Bool) (c : MeshIndex J) :
    (phaseState hbuffer η hη i j half c).val (partnerSite i j half) = η.val j := by
  cases half <;> simp [phaseState, partnerSite, oneMove, permutedLabel, hij.symm]

/-- Literal reconstruction from either endpoint of an edge, the half,
the partner, and the original cell of the first particle. -/
def restore (half : Bool) (ζ : LabelVector J N) (p q : Fin N) (a : MeshIndex J) :
    LabelVector J N :=
  if half then Function.update (Function.update ζ p (ζ q)) q a
    else Function.update ζ p a

theorem restore_phaseState (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t)
    (hη : OccupationCap v η.val) {i j : Fin N} (hij : i ≠ j)
    (half : Bool) (c : MeshIndex J) :
    restore half (phaseState hbuffer η hη i j half c).val
      (movingSite i j half) (partnerSite i j half) (η.val i) = η.val := by
  cases half
  · simp only [restore, phaseState, movingSite, partnerSite, Bool.false_eq_true,
      ite_false, oneMove_val, Function.update_idem, Function.update_eq_self]
  · rw [show (phaseState hbuffer η hη i j true c).val =
        Function.update (Function.update η.val i (η.val j)) j c from
        (second_half_value η.val hij c).symm]
    funext p
    by_cases hpi : p = i
    · subst p
      simp [restore, movingSite, partnerSite]
    · by_cases hpj : p = j
      · subst p
        simp [restore, movingSite, partnerSite, hij, hij.symm]
      · simp [restore, movingSite, partnerSite, hpi, hpj, hij]

theorem phaseState_step (hJ : 0 < J) (hbuffer : 1 ≤ (t - v) * N)
    (η : LabelState J N t) (hη : OccupationCap v η.val) {i j : Fin N}
    (hij : i ≠ j) (half : Bool) {c d : MeshIndex J} (hcd : EdgeAdjacent J hJ c d) :
    CoordinateStep hJ (movingSite i j half)
      (phaseState hbuffer η hη i j half c) (phaseState hbuffer η hη i j half d) := by
  refine ⟨by simpa only [phaseState_moving hbuffer η hη hij] using hcd, ?_⟩
  cases half
  · simp only [phaseState, movingSite, Bool.false_eq_true, ite_false, oneMove_val,
      Function.update_self, Function.update_idem]
  · rw [show (phaseState hbuffer η hη i j true c).val =
        Function.update (Function.update η.val i (η.val j)) j c from
        (second_half_value η.val hij c).symm,
      show (phaseState hbuffer η hη i j true d).val =
        Function.update (Function.update η.val i (η.val j)) j d from
        (second_half_value η.val hij d).symm]
    simp only [movingSite, ite_true, Function.update_self, Function.update_idem]

/-- The existing rank chooses one orientation of an actual unordered edge. -/
def orderedEdge (η ζ : LabelState J N t) : LabelState J N t × LabelState J N t :=
  if labelRank η < labelRank ζ then (η, ζ) else (ζ, η)

theorem orderedEdge_cases (η ζ : LabelState J N t) :
    orderedEdge η ζ = (η, ζ) ∨ orderedEdge η ζ = (ζ, η) := by
  classical
  by_cases h : labelRank η < labelRank ζ
  · exact Or.inl (ite_eq_left h)
  · exact Or.inr (ite_eq_right h)

theorem orderedEdge_eq_or {η ζ ξ χ : LabelState J N t}
    (h : orderedEdge η ζ = orderedEdge ξ χ) :
    (η = ξ ∧ ζ = χ) ∨ (η = χ ∧ ζ = ξ) := by
  classical
  unfold orderedEdge at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;>
    rcases h with ⟨rfl, rfl⟩ <;> simp

theorem orderedEdge_step (hJ : 0 < J) {p : Fin N} {η ζ : LabelState J N t}
    (he : CoordinateStep hJ p η ζ) :
    CoordinateStep hJ p (orderedEdge η ζ).1 (orderedEdge η ζ).2 := by
  rcases orderedEdge_cases η ζ with h | h
  · simpa only [h] using he
  · simpa only [h] using he.symm

theorem orderedEdge_term (hJ : 0 < J) (β : ℝ) (Ψ : LabelState J N t → ℝ)
    (η ζ : LabelState J N t) :
    labelTerm hJ β Ψ (orderedEdge η ζ).1 (orderedEdge η ζ).2 = labelTerm hJ β Ψ η ζ := by
  rcases orderedEdge_cases η ζ with h | h
  · simp only [h]
  · simpa only [h] using labelTerm_symm hJ β Ψ ζ η

theorem orderedEdge_lt {η ζ : LabelState J N t} (hne : η ≠ ζ) :
    labelRank (orderedEdge η ζ).1 < labelRank (orderedEdge η ζ).2 := by
  classical
  by_cases h : labelRank η < labelRank ζ
  · simpa only [orderedEdge, ite_eq_left h] using h
  · have hne' : labelRank η ≠ labelRank ζ := fun he =>
      hne ((Fintype.equivFin (LabelState J N t)).injective he)
    simpa only [orderedEdge, ite_eq_right h] using lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne')

theorem ordered_steps_injective {k : ℕ} (f : ℕ → LabelState J N t)
    (hf : Set.InjOn f {r | r ≤ k}) :
    Function.Injective (fun r : Fin k => orderedEdge (f r) (f (r + 1))) := by
  intro r s h
  rcases orderedEdge_eq_or h with h | h
  · exact Fin.ext (hf (by change r.val ≤ k; omega) (by change s.val ≤ k; omega) h.1)
  · have h1 := hf (show r.val ≤ k by omega) (show s.val + 1 ≤ k by omega) h.1
    have h2 := hf (show r.val + 1 ≤ k by omega) (show s.val ≤ k by omega) h.2
    omega

theorem phase_vertices_injOn (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t) (hη : OccupationCap v η.val)
    {i j : Fin N} (hij : i ≠ j) (half : Bool) :
    Set.InjOn (fun r => phaseState hbuffer η hη i j half
      ((cellPath hJ hJ2 (η.val i) (η.val j)).getVert r))
      {r | r ≤ (cellPath hJ hJ2 (η.val i) (η.val j)).length} := by
  intro r hr s hs he
  have hc := congrArg (fun ξ : LabelState J N t => ξ.val (movingSite i j half)) he
  simp only [phaseState_moving hbuffer η hη hij] at hc
  exact (cellPath_isPath hJ hJ2 _ _).getVert_injOn hr hs hc

theorem bool_sum (f : Bool → ℝ) : (∑ b, f b) = f false + f true := by simp [add_comm]

/-- Finite Cauchy--Schwarz along the two joined sequences, including length zero. -/
theorem two_sequences_cauchy (k : ℕ) (f g : ℕ → ℝ) (hjoin : f k = g k) :
    (g 0 - f 0) ^ 2 ≤ 2 * (k : ℝ) *
      ((∑ r : Fin k, (f (r + 1) - f r) ^ 2) +
        ∑ r : Fin k, (g (r + 1) - g r) ^ 2) := by
  let D : Bool × Fin k → ℝ := fun z =>
    if z.1 then g z.2 - g (z.2 + 1) else f (z.2 + 1) - f z.2
  have hsum : (∑ z, D z) = g 0 - f 0 := by
    rw [Fintype.sum_prod_type, bool_sum]
    simp only [D, Bool.false_eq_true, ite_false, ite_true]
    rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1) - f n),
      Fin.sum_univ_eq_sum_range (fun n => g n - g (n + 1)),
      Finset.sum_range_sub, Finset.sum_range_sub', hjoin]
    ring
  have hsq : (∑ z, D z ^ 2) =
      (∑ r : Fin k, (f (r + 1) - f r) ^ 2) +
        ∑ r : Fin k, (g (r + 1) - g r) ^ 2 := by
    rw [Fintype.sum_prod_type, bool_sum]
    simp only [D, Bool.false_eq_true, ite_false, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := D)
  rw [hsum, hsq] at h
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using h

def pathCost (hJ : 0 < J) (hJ2 : 2 ≤ J) (β : ℝ) (Ψ : LabelState J N t → ℝ)
    (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t) (hη : OccupationCap v η.val)
    (i j : Fin N) : ℝ :=
  ∑ half : Bool, ∑ r : Fin (cellPath hJ hJ2 (η.val i) (η.val j)).length,
    labelTerm hJ β Ψ
      (phaseState hbuffer η hη i j half ((cellPath hJ hJ2 (η.val i) (η.val j)).getVert r))
      (phaseState hbuffer η hη i j half ((cellPath hJ hJ2 (η.val i) (η.val j)).getVert (r + 1)))

section SourceWeights

variable {β β₀ δ Cg : ℝ} (hN : 2 ≤ N)
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (htδ : t ≤ δ)
  (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hJ2 : 2 ≤ J)
  (hbuffer : 1 ≤ (t - v) * N) (η : LabelState J N t) (hη : OccupationCap v η.val)

include hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg in
theorem phaseState_weight_lower (i j : Fin N) (half : Bool) (c : MeshIndex J) :
    CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀) *
      labelWeight (mesh_pos hmesh) β η ≤
        labelWeight (mesh_pos hmesh) β (phaseState hbuffer η hη i j half c) := by
  cases half
  · exact oneMove_weight_lower hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg hmesh hbuffer η hη i c
  · change _ ≤ labelWeight _ β (permutedLabel (Equiv.swap i j) (oneMove hbuffer η hη i c))
    rw [labelWeight_permutedLabel]
    exact oneMove_weight_lower hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg hmesh hbuffer η hη i c

include hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg in
theorem phase_energy_lower (Ψ : LabelState J N t → ℝ) {i j : Fin N} (hij : i ≠ j)
    (half : Bool) :
    let p := cellPath (mesh_pos hmesh) hJ2 (η.val i) (η.val j)
    let κ := CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)
    κ * labelWeight (mesh_pos hmesh) β η / 2 *
      (∑ r : Fin p.length, (Ψ (phaseState hbuffer η hη i j half (p.getVert (r + 1))) -
        Ψ (phaseState hbuffer η hη i j half (p.getVert r))) ^ 2) ≤
      ∑ r : Fin p.length, labelTerm (mesh_pos hmesh) β Ψ
        (phaseState hbuffer η hη i j half (p.getVert r))
        (phaseState hbuffer η hη i j half (p.getVert (r + 1))) := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply conductance_lower (mesh_pos hmesh)
    ((phaseState_step (mesh_pos hmesh) hbuffer η hη hij half
      ((cellPath (mesh_pos hmesh) hJ2 _ _).adj_getVert_succ r.isLt)).adjacent)
  · exact labelWeight_pos _ hN hβ (hβ₀.trans_lt hsub) _
  · exact labelWeight_pos _ hN hβ (hβ₀.trans_lt hsub) _
  · exact phaseState_weight_lower hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg hmesh hbuffer η hη i j half _
  · exact phaseState_weight_lower hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg hmesh hbuffer η hη i j half _

include hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg in
/-- The literal single-permutation path estimate with the source factor 4J/kappa. -/
theorem one_permutation_path (Ψ : LabelState J N t → ℝ) {i j : Fin N} (hij : i ≠ j) :
    labelWeight (mesh_pos hmesh) β η *
      (Ψ (permutedLabel (Equiv.swap i j) η) - Ψ η) ^ 2 ≤
      (4 * (J : ℝ) / CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)) *
        pathCost (mesh_pos hmesh) hJ2 β Ψ hbuffer η hη i j := by
  let p := cellPath (mesh_pos hmesh) hJ2 (η.val i) (η.val j)
  let f : ℕ → ℝ := fun r => Ψ (phaseState hbuffer η hη i j false (p.getVert r))
  let g : ℕ → ℝ := fun r => Ψ (phaseState hbuffer η hη i j true (p.getVert r))
  let κ := CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)
  let w := labelWeight (mesh_pos hmesh) β η
  let S := (∑ r : Fin p.length, (f (r + 1) - f r) ^ 2) +
    ∑ r : Fin p.length, (g (r + 1) - g r) ^ 2
  have hκ : 0 < κ := CellNormalizerBounds.kappaConstant_pos _ _ _ (mesh_pos hmesh)
    (by have h := radius_one_le β₀; omega)
  have hw : 0 ≤ w := (labelWeight_pos _ hN hβ (hβ₀.trans_lt hsub) η).le
  have hS : 0 ≤ S := add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hjoin : f p.length = g p.length := by
    simp only [f, g, SimpleGraph.Walk.getVert_length, phaseState, Bool.false_eq_true,
      ite_false, ite_true, second_half_join hbuffer η hη hij]
  have hC := two_sequences_cauchy p.length f g hjoin
  have hf : f 0 = Ψ η := by
    simp only [f, SimpleGraph.Walk.getVert_zero, phaseState, Bool.false_eq_true, ite_false,
      oneMove_start]
  have hgs : g 0 = Ψ (permutedLabel (Equiv.swap i j) η) := by
    simp only [g, SimpleGraph.Walk.getVert_zero, phaseState, ite_true, oneMove_start]
  rw [hf, hgs] at hC
  have hp : (p.length : ℝ) ≤ J := by
    exact_mod_cast cellPath_length_le (mesh_pos hmesh) hJ2 (η.val i) (η.val j)
  have hC' : (Ψ (permutedLabel (Equiv.swap i j) η) - Ψ η) ^ 2 ≤ 2 * (J : ℝ) * S :=
    hC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hS)
  have hE : κ * w / 2 * S ≤ pathCost (mesh_pos hmesh) hJ2 β Ψ hbuffer η hη i j := by
    have hF := phase_energy_lower hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg hmesh hJ2 hbuffer η hη Ψ hij false
    have hG := phase_energy_lower hN hβ hβ₀ hsub hδ₀ hδ htδ hCg hg hmesh hJ2 hbuffer η hη Ψ hij true
    simpa only [κ, w, S, f, g, p, pathCost, bool_sum, mul_add] using add_le_add hF hG
  calc
    _ ≤ w * (2 * (J : ℝ) * S) := mul_le_mul_of_nonneg_left hC' hw
    _ = (4 * (J : ℝ) / κ) * (κ * w / 2 * S) := by field_simp [hκ.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)

end SourceWeights

section Congestion

/-- Only unequal labels contribute to a transposition difference. -/
abbrev PermutationDatum (A : Finset (LabelState J N t)) :=
  {d : LabelState J N t × Fin N × Fin N //
    d.1 ∈ A ∧ d.2.1 < d.2.2 ∧ d.1.val d.2.1 ≠ d.1.val d.2.2}

def datumLength (hJ : 0 < J) (hJ2 : 2 ≤ J) {A : Finset (LabelState J N t)}
    (d : PermutationDatum A) : ℕ := (cellPath hJ hJ2 (d.val.1.val d.val.2.1)
      (d.val.1.val d.val.2.2)).length

/-- Every actual edge occurrence, including its half and position. -/
abbrev PathOccurrence (hJ : 0 < J) (hJ2 : 2 ≤ J) (A : Finset (LabelState J N t)) :=
  Σ d : PermutationDatum A, Bool × Fin (datumLength hJ hJ2 d)

variable (hJ : 0 < J) (hJ2 : 2 ≤ J) (hbuffer : 1 ≤ (t - v) * N)
  (A : Finset (LabelState J N t)) (hA : ∀ η ∈ A, OccupationCap v η.val)

def occurrenceState (o : PathOccurrence hJ hJ2 A) (r : ℕ) : LabelState J N t :=
  phaseState hbuffer o.1.val.1 (hA _ o.1.property.1) o.1.val.2.1 o.1.val.2.2 o.2.1
    ((cellPath hJ hJ2 (o.1.val.1.val o.1.val.2.1) (o.1.val.1.val o.1.val.2.2)).getVert r)

def occurrenceEdge (o : PathOccurrence hJ hJ2 A) : LabelState J N t × LabelState J N t :=
  orderedEdge (occurrenceState hJ hJ2 hbuffer A hA o o.2.2)
    (occurrenceState hJ hJ2 hbuffer A hA o (o.2.2 + 1))

def occurrenceSite (o : PathOccurrence hJ hJ2 A) : Fin N :=
  movingSite o.1.val.2.1 o.1.val.2.2 o.2.1

def occurrenceCode (o : PathOccurrence hJ hJ2 A) : Bool × Fin N × MeshIndex J :=
  (o.2.1, partnerSite o.1.val.2.1 o.1.val.2.2 o.2.1, o.1.val.1.val o.1.val.2.1)

theorem occurrence_step (o : PathOccurrence hJ hJ2 A) :
    CoordinateStep hJ (occurrenceSite hJ hJ2 A o)
      (occurrenceEdge hJ hJ2 hbuffer A hA o).1 (occurrenceEdge hJ hJ2 hbuffer A hA o).2 := by
  apply orderedEdge_step hJ
  exact phaseState_step hJ hbuffer o.1.val.1 (hA _ o.1.property.1) o.1.property.2.1.ne _
    ((cellPath hJ hJ2 _ _).adj_getVert_succ o.2.2.isLt)

theorem occurrence_restore (o : PathOccurrence hJ hJ2 A) :
    restore (occurrenceCode hJ hJ2 A o).1 (occurrenceEdge hJ hJ2 hbuffer A hA o).1.val
      (occurrenceSite hJ hJ2 A o) (occurrenceCode hJ hJ2 A o).2.1
      (occurrenceCode hJ hJ2 A o).2.2 = o.1.val.1.val := by
  rcases orderedEdge_cases (occurrenceState hJ hJ2 hbuffer A hA o o.2.2)
      (occurrenceState hJ hJ2 hbuffer A hA o (o.2.2 + 1)) with h | h
  · change restore _ (orderedEdge _ _).1.val _ _ _ = _
    rw [h]
    exact restore_phaseState hbuffer o.1.val.1 (hA _ o.1.property.1) o.1.property.2.1.ne _ _
  · change restore _ (orderedEdge _ _).1.val _ _ _ = _
    rw [h]
    exact restore_phaseState hbuffer o.1.val.1 (hA _ o.1.property.1) o.1.property.2.1.ne _ _

theorem occurrenceSite_eq {o o' : PathOccurrence hJ hJ2 A}
    (he : occurrenceEdge hJ hJ2 hbuffer A hA o = occurrenceEdge hJ hJ2 hbuffer A hA o') :
    occurrenceSite hJ hJ2 A o = occurrenceSite hJ hJ2 A o' := by
  have h := occurrence_step hJ hJ2 hbuffer A hA o
  rw [he] at h
  exact h.unique hJ2 (occurrence_step hJ hJ2 hbuffer A hA o')

theorem pair_eq_of_sites {i j i' j' : Fin N} {b b' : Bool} (hb : b = b')
    (hm : movingSite i j b = movingSite i' j' b')
    (hp : partnerSite i j b = partnerSite i' j' b') : i = i' ∧ j = j' := by
  subst b'
  cases b
  · exact ⟨hm, hp⟩
  · exact ⟨hp, hm⟩

/-- Fixed edge plus the source's three pieces of data determines the whole
occurrence. This includes uniqueness of the position on the chosen path. -/
theorem occurrence_reconstruction {o o' : PathOccurrence hJ hJ2 A}
    (he : occurrenceEdge hJ hJ2 hbuffer A hA o = occurrenceEdge hJ hJ2 hbuffer A hA o')
    (hc : occurrenceCode hJ hJ2 A o = occurrenceCode hJ hJ2 A o') : o = o' := by
  rcases o with ⟨d, b, r⟩
  rcases o' with ⟨e, c, s⟩
  have hb : b = c := congrArg Prod.fst hc
  have hp : partnerSite d.val.2.1 d.val.2.2 b = partnerSite e.val.2.1 e.val.2.2 c :=
    congrArg (fun z => z.2.1) hc
  have hm := occurrenceSite_eq hJ hJ2 hbuffer A hA he
  have hmi : movingSite d.val.2.1 d.val.2.2 b = movingSite e.val.2.1 e.val.2.2 c := hm
  have hij := pair_eq_of_sites hb hmi hp
  have hdv : d.val.1.val = e.val.1.val := by
    calc
      _ = restore (occurrenceCode hJ hJ2 A ⟨d, b, r⟩).1
          (occurrenceEdge hJ hJ2 hbuffer A hA ⟨d, b, r⟩).1.val
          (occurrenceSite hJ hJ2 A ⟨d, b, r⟩)
          (occurrenceCode hJ hJ2 A ⟨d, b, r⟩).2.1
          (occurrenceCode hJ hJ2 A ⟨d, b, r⟩).2.2 :=
        (occurrence_restore hJ hJ2 hbuffer A hA ⟨d, b, r⟩).symm
      _ = restore (occurrenceCode hJ hJ2 A ⟨e, c, s⟩).1
          (occurrenceEdge hJ hJ2 hbuffer A hA ⟨e, c, s⟩).1.val
          (occurrenceSite hJ hJ2 A ⟨e, c, s⟩)
          (occurrenceCode hJ hJ2 A ⟨e, c, s⟩).2.1
          (occurrenceCode hJ hJ2 A ⟨e, c, s⟩).2.2 := by rw [he, hc, hm]
      _ = _ := occurrence_restore hJ hJ2 hbuffer A hA ⟨e, c, s⟩
  have hd : d = e := Subtype.ext (Prod.ext (Subtype.ext hdv) (Prod.ext hij.1 hij.2))
  subst e
  subst c
  have hinj := ordered_steps_injective
    (fun n => phaseState hbuffer d.val.1 (hA _ d.property.1) d.val.2.1 d.val.2.2 b
      ((cellPath hJ hJ2 (d.val.1.val d.val.2.1) (d.val.1.val d.val.2.2)).getVert n))
    (phase_vertices_injOn hJ hJ2 hbuffer d.val.1 (hA _ d.property.1) d.property.2.1.ne b)
  have hrs : r = s := hinj he
  subst s
  rfl

def occurrenceFiber (e : LabelState J N t × LabelState J N t) :
    Finset (PathOccurrence hJ hJ2 A) := by
  classical
  exact Finset.univ.filter fun o => occurrenceEdge hJ hJ2 hbuffer A hA o = e

/-- Exact source congestion: at most two halves, N-1 partners, and J^2
initial cells. Restrictions on the starting set can only remove occurrences. -/
theorem occurrence_congestion (e : LabelState J N t × LabelState J N t) :
    (occurrenceFiber hJ hJ2 hbuffer A hA e).card ≤ 2 * J ^ 2 * (N - 1) := by
  classical
  let S := occurrenceFiber hJ hJ2 hbuffer A hA e
  by_cases hs : S.Nonempty
  · obtain ⟨o₀, ho₀⟩ := hs
    let p := occurrenceSite hJ hJ2 A o₀
    let T : Finset (Bool × Fin N × MeshIndex J) := Finset.univ.filter fun z => z.2.1 ≠ p
    have hcard : S.card ≤ T.card := by
      apply Finset.card_le_card_of_injOn (occurrenceCode hJ hJ2 A)
      · intro o ho
        have he : occurrenceEdge hJ hJ2 hbuffer A hA o =
            occurrenceEdge hJ hJ2 hbuffer A hA o₀ :=
          (Finset.mem_filter.mp ho).2.trans (Finset.mem_filter.mp ho₀).2.symm
        have hp := occurrenceSite_eq hJ hJ2 hbuffer A hA he
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change partnerSite o.1.val.2.1 o.1.val.2.2 o.2.1 ≠ occurrenceSite hJ hJ2 A o₀
        rw [← hp]
        exact partnerSite_ne o.1.property.2.1.ne o.2.1
      · intro o ho o' ho' hc
        exact occurrence_reconstruction hJ hJ2 hbuffer A hA
          ((Finset.mem_filter.mp ho).2.trans (Finset.mem_filter.mp ho').2.symm) hc
    have hT : T = (Finset.univ : Finset Bool) ×ˢ
        ((Finset.univ.erase p) ×ˢ (Finset.univ : Finset (MeshIndex J))) := by
      ext z
      simp [T]
    have hcount : T.card = 2 * J ^ 2 * (N - 1) := by
      rw [hT]
      simp only [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ, Fintype.card_bool, Fintype.card_fin, MeshIndex, Fintype.card_fun]
      ring
    exact hcard.trans_eq hcount
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

/-- An unordered edge is not repeated even between the two halves: the
halves move different specified particles. -/
theorem path_edges_injective (d : PermutationDatum A) :
    Function.Injective (fun z : Bool × Fin (datumLength hJ hJ2 d) =>
      occurrenceEdge hJ hJ2 hbuffer A hA ⟨d, z⟩) := by
  rintro ⟨b, r⟩ ⟨c, s⟩ he
  have hm := occurrenceSite_eq hJ hJ2 hbuffer A hA he
  have hb : b = c := by
    cases b <;> cases c
    · rfl
    · exact False.elim (d.property.2.1.ne hm)
    · exact False.elim (d.property.2.1.ne hm.symm)
    · rfl
  subst c
  have ho := occurrence_reconstruction hJ hJ2 hbuffer A hA he (by rfl)
  exact Prod.ext rfl (Fin.ext (congrArg (fun o : PathOccurrence hJ hJ2 A => o.2.2.val) ho))

theorem occurrence_edge_lt (o : PathOccurrence hJ hJ2 A) :
    labelRank (occurrenceEdge hJ hJ2 hbuffer A hA o).1 <
      labelRank (occurrenceEdge hJ hJ2 hbuffer A hA o).2 := by
  apply orderedEdge_lt
  exact (phaseState_step hJ hbuffer o.1.val.1 (hA _ o.1.property.1) o.1.property.2.1.ne _
    ((cellPath hJ hJ2 _ _).adj_getVert_succ o.2.2.isLt)).adjacent.ne hJ2

def orientedTerm (β : ℝ) (Ψ : LabelState J N t → ℝ)
    (e : LabelState J N t × LabelState J N t) : ℝ :=
  if labelRank e.1 < labelRank e.2 then labelTerm hJ β Ψ e.1 e.2 else 0

theorem labelTerm_nonneg (β : ℝ) (Ψ : LabelState J N t → ℝ)
    (η ζ : LabelState J N t) : 0 ≤ labelTerm hJ β Ψ η ζ := by
  classical
  unfold labelTerm labelConductance
  split_ifs
  · exact mul_nonneg (div_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) (sq_nonneg _)
  · simp only [zero_mul, le_refl]

theorem orientedTerm_nonneg (β : ℝ) (Ψ : LabelState J N t → ℝ)
    (e : LabelState J N t × LabelState J N t) : 0 ≤ orientedTerm hJ β Ψ e := by
  classical
  unfold orientedTerm
  split_ifs
  · exact labelTerm_nonneg hJ β Ψ _ _
  · exact le_rfl

theorem sum_orientedTerm (β : ℝ) (Ψ : LabelState J N t → ℝ) :
    (∑ e, orientedTerm hJ β Ψ e) = labelEnergy hJ β Ψ := by
  rw [Fintype.sum_prod_type]
  rfl

theorem labelEnergy_nonneg (β : ℝ) (Ψ : LabelState J N t → ℝ) :
    0 ≤ labelEnergy hJ β Ψ := by
  rw [← sum_orientedTerm]
  exact Finset.sum_nonneg fun e _ => orientedTerm_nonneg hJ β Ψ e

theorem occurrence_term (β : ℝ) (Ψ : LabelState J N t → ℝ)
    (o : PathOccurrence hJ hJ2 A) :
    orientedTerm hJ β Ψ (occurrenceEdge hJ hJ2 hbuffer A hA o) =
      labelTerm hJ β Ψ (occurrenceState hJ hJ2 hbuffer A hA o o.2.2)
        (occurrenceState hJ hJ2 hbuffer A hA o (o.2.2 + 1)) := by
  rw [orientedTerm, ite_eq_left (occurrence_edge_lt hJ hJ2 hbuffer A hA o)]
  exact orderedEdge_term hJ β Ψ _ _

theorem sum_finite_fibres {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    (f : α → γ) (w : γ → ℝ) :
    (∑ a, w (f a)) = ∑ b, ((Finset.univ.filter fun a => f a = b).card : ℝ) * w b := by
  classical
  have h := sum_weighted_fibers f (fun _ => (1 : ℝ)) w
  simpa only [one_mul, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] using h

/-- Summing the actual occurrence costs gives the actual outer label energy
with precisely the proved congestion factor. -/
theorem path_cost_sum_le (β : ℝ) (Ψ : LabelState J N t → ℝ) :
    (∑ d : PermutationDatum A, pathCost hJ hJ2 β Ψ hbuffer d.val.1
      (hA _ d.property.1) d.val.2.1 d.val.2.2) ≤
        2 * (J : ℝ) ^ 2 * (N - 1 : ℕ) * labelEnergy hJ β Ψ := by
  classical
  have hid : (∑ d : PermutationDatum A, pathCost hJ hJ2 β Ψ hbuffer d.val.1
      (hA _ d.property.1) d.val.2.1 d.val.2.2) =
      ∑ o : PathOccurrence hJ hJ2 A, orientedTerm hJ β Ψ
        (occurrenceEdge hJ hJ2 hbuffer A hA o) := by
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_prod_type, occurrence_term]
    rfl
  rw [hid, sum_finite_fibres]
  calc
    _ ≤ ∑ e : LabelState J N t × LabelState J N t,
        (2 * (J : ℝ) ^ 2 * (N - 1 : ℕ)) * orientedTerm hJ β Ψ e := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_right _ (orientedTerm_nonneg hJ β Ψ e)
      exact_mod_cast occurrence_congestion hJ hJ2 hbuffer A hA e
    _ = _ := by rw [← Finset.mul_sum, sum_orientedTerm]

end Congestion

section FinalComparison

theorem permutedLabel_swap_eq {η : LabelState J N t} {i j : Fin N}
    (h : η.val i = η.val j) : permutedLabel (Equiv.swap i j) η = η := by
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k
    simpa only [permutedLabel, Function.comp_apply, Equiv.swap_apply_left] using h.symm
  · by_cases hkj : k = j
    · subst k
      simpa only [permutedLabel, Function.comp_apply, Equiv.swap_apply_right] using h
    · simp only [permutedLabel, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- The datum sum is the literal unordered-particle transposition sum.
Pairs with equal cell labels have exactly zero difference. -/
theorem sum_permutationData (hJ : 0 < J) (β : ℝ) (A : Finset (LabelState J N t))
    (Ψ : LabelState J N t → ℝ) :
    (∑ d : PermutationDatum A, labelWeight hJ β d.val.1 *
      (Ψ (permutedLabel (Equiv.swap d.val.2.1 d.val.2.2) d.val.1) - Ψ d.val.1) ^ 2) =
      ∑ η ∈ A, labelWeight hJ β η * ∑ i : Fin N, ∑ j : Fin N,
        if i < j then (Ψ (permutedLabel (Equiv.swap i j) η) - Ψ η) ^ 2 else 0 := by
  classical
  let P := fun d : LabelState J N t × Fin N × Fin N =>
    d.1 ∈ A ∧ d.2.1 < d.2.2 ∧ d.1.val d.2.1 ≠ d.1.val d.2.2
  let f := fun d : LabelState J N t × Fin N × Fin N => labelWeight hJ β d.1 *
    (Ψ (permutedLabel (Equiv.swap d.2.1 d.2.2) d.1) - Ψ d.1) ^ 2
  have hsub := Finset.sum_subtype (p := P)
    (F := (inferInstance : Fintype (PermutationDatum A)))
    (Finset.univ.filter P) (by simp) f
  change (∑ d : PermutationDatum A, f d.val) = _
  rw [← hsub, Finset.sum_filter, Fintype.sum_prod_type]
  have hA : (Finset.univ.filter fun η => η ∈ A) = A := by ext η; simp
  conv_rhs => rw [← hA, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro η _
  rw [Fintype.sum_prod_type]
  by_cases hη : η ∈ A
  · simp only [hη, true_and, ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · by_cases he : η.val i = η.val j
      · simp [hij, he, f, permutedLabel_swap_eq he]
      · simp [hij, he, f]
    · simp [hij, f]
  · simp [hη]

/-- Source Proposition `permutation-paths` on the original outer graph.
The constant is independent of N, the subset of starting labels, the
observable, and beta in the prescribed interval. -/
theorem permutation_paths {β β₀ δ Cg : ℝ} (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hv : 0 < v) (hvt : v < t) (htδ : t < δ) (hδ : δ ≤ occupationBound β₀)
    (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hbuffer : 1 ≤ (t - v) * N)
    (A : Finset (LabelState J N t)) (hA : ∀ η ∈ A, OccupationCap v η.val)
    (Ψ : LabelState J N t → ℝ) :
    (1 / (2 * (N : ℝ))) * (∑ η ∈ A, labelWeight (mesh_pos hmesh) β η *
      ∑ i : Fin N, ∑ j : Fin N,
        if i < j then (Ψ (permutedLabel (Equiv.swap i j) η) - Ψ η) ^ 2 else 0) ≤
      (4 * (J : ℝ) ^ 3 /
        CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)) *
          labelEnergy (mesh_pos hmesh) β Ψ := by
  classical
  let κ := CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)
  let E := labelEnergy (mesh_pos hmesh) β Ψ
  have hκ : 0 < κ := CellNormalizerBounds.kappaConstant_pos _ _ _ (mesh_pos hmesh)
    (by have h := radius_one_le β₀; omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hE : 0 ≤ E := labelEnergy_nonneg (mesh_pos hmesh) β Ψ
  have hδ₀ : 0 < δ := hv.trans (hvt.trans htδ)
  let hJ2 : 2 ≤ J := mesh_two_le hmesh
  have hpaths :
      (∑ d : PermutationDatum A, labelWeight (mesh_pos hmesh) β d.val.1 *
        (Ψ (permutedLabel (Equiv.swap d.val.2.1 d.val.2.2) d.val.1) - Ψ d.val.1) ^ 2) ≤
      (4 * (J : ℝ) / κ) * ∑ d : PermutationDatum A,
        pathCost (mesh_pos hmesh) hJ2 β Ψ hbuffer d.val.1
          (hA _ d.property.1) d.val.2.1 d.val.2.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    exact one_permutation_path hN hβ hβ₀ hsub hδ₀ hδ htδ.le hCg hg hmesh hJ2 hbuffer
      d.val.1 (hA _ d.property.1) Ψ d.property.2.1.ne
  have hcost := path_cost_sum_le (mesh_pos hmesh) hJ2 hbuffer A hA β Ψ
  have hcombined := hpaths.trans (mul_le_mul_of_nonneg_left hcost (by positivity))
  have hNm : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  rw [← sum_permutationData (mesh_pos hmesh) β A Ψ]
  calc
    _ ≤ (1 / (2 * (N : ℝ))) * ((4 * (J : ℝ) / κ) *
        (2 * (J : ℝ) ^ 2 * (N - 1 : ℕ) * E)) :=
      mul_le_mul_of_nonneg_left hcombined (by positivity)
    _ ≤ (1 / (2 * (N : ℝ))) * ((4 * (J : ℝ) / κ) *
        (2 * (J : ℝ) ^ 2 * (N : ℝ) * E)) := by
      gcongr
    _ = _ := by dsimp only [κ, E]; field_simp [hNr.ne', hκ.ne']

end FinalComparison

end TwoParticlePaths

end PeriodicAttractiveLogGas.PermutationPathComparison
