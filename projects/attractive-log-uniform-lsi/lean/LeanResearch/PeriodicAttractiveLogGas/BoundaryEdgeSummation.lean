import LeanResearch.PeriodicAttractiveLogGas.DiscreteOccupationIdentities
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationSections
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Source Proposition 3.12, lines 948--966: actual label-edge transport,
four-edge incidence, and the final finite summation. The quantitative
single-edge estimate remains an explicitly identified intermediate input.
SOURCE_ONLY candidate; central Lean checking is pending.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.BoundaryEdgeSummation

open MeshCells MeshAdjacentCells CellRestrictions LabelOccupations
  DiscreteOccupationIdentities ConditionalLawEstimates

section FourCellEdges

variable {J : ℕ}

theorem successorIndex_injective (hJ : 0 < J) : Function.Injective (successorIndex J hJ) := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  by_cases ha : a.val + 1 < J <;> by_cases hb : b.val + 1 < J <;>
    simp only [successorIndex, ha, hb, dite_true, dite_false] at hv <;> omega

theorem successorIndex_twice_ne (hJ : 0 < J) (hJ3 : 3 ≤ J) (a : Fin J) :
    successorIndex J hJ (successorIndex J hJ a) ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  by_cases ha : a.val + 1 < J
  · by_cases hb : a.val + 1 + 1 < J
    · simp only [successorIndex, ha, dite_true, hb] at hv
      omega
    · simp only [successorIndex, ha, dite_true, hb, dite_false] at hv
      omega
  · have hz : (0 : ℕ) + 1 < J := by omega
    simp only [successorIndex, ha, dite_false, hz, dite_true] at hv
    omega

theorem nextCell_injective (hJ : 0 < J) (d : Fin 2) : Function.Injective (fun a ↦ nextCell J hJ a d) := by
  intro a b h
  funext k
  by_cases hk : k = d
  · subst k
    apply successorIndex_injective hJ
    simpa only [nextCell_apply_same] using congrFun h d
  · simpa only [nextCell_apply_of_ne J hJ a d k hk,
      nextCell_apply_of_ne J hJ b d k hk] using congrFun h k

def nextCellEquiv (hJ : 0 < J) (d : Fin 2) : MeshIndex J ≃ MeshIndex J :=
  Equiv.ofBijective (fun a ↦ nextCell J hJ a d)
    ⟨nextCell_injective hJ d, Finite.surjective_of_injective (nextCell_injective hJ d)⟩

def previousCell (hJ : 0 < J) (a : MeshIndex J) (d : Fin 2) : MeshIndex J :=
  (nextCellEquiv hJ d).symm a

theorem next_previousCell (hJ : 0 < J) (a : MeshIndex J) (d : Fin 2) :
    nextCell J hJ (previousCell hJ a d) d = a := (nextCellEquiv hJ d).apply_symm_apply a

theorem previousCell_apply_of_ne (hJ : 0 < J) (a : MeshIndex J) (d k : Fin 2) (hk : k ≠ d) :
    previousCell hJ a d k = a k := by
  simpa only [nextCell_apply_of_ne J hJ _ d k hk] using congrFun (next_previousCell hJ a d) k

theorem previousCell_apply_same_ne (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : MeshIndex J) (d : Fin 2) :
    previousCell hJ a d d ≠ a d := by
  intro h
  have hh := congrFun (next_previousCell hJ a d) d
  rw [nextCell_apply_same, h] at hh
  exact successorIndex_ne J hJ hJ2 (a d) hh

theorem nextCell_ne_previousCell (hJ : 0 < J) (hJ3 : 3 ≤ J) (a : MeshIndex J) (d : Fin 2) :
    nextCell J hJ a d ≠ previousCell hJ a d := by
  intro h
  have hh := congrArg (fun b ↦ nextCell J hJ b d) h
  rw [next_previousCell] at hh
  have hv := congrFun hh d
  simp only [nextCell_apply_same] at hv
  exact successorIndex_twice_ne hJ hJ3 (a d) hv

/-- The four directions enumerate the actual unoriented adjacency relation. -/
def cellNeighbor (hJ : 0 < J) (a : MeshIndex J) : Fin 2 × Bool → MeshIndex J
  | (d, true) => nextCell J hJ a d
  | (d, false) => previousCell hJ a d

theorem cellNeighbor_apply_same_ne (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : MeshIndex J)
    (d : Fin 2) (s : Bool) : cellNeighbor hJ a (d, s) d ≠ a d := by
  cases s
  · exact previousCell_apply_same_ne hJ hJ2 a d
  · simpa only [cellNeighbor, nextCell_apply_same] using successorIndex_ne J hJ hJ2 (a d)

theorem cellNeighbor_apply_of_ne (hJ : 0 < J) (a : MeshIndex J)
    (d k : Fin 2) (s : Bool) (hk : k ≠ d) : cellNeighbor hJ a (d, s) k = a k := by
  cases s
  · exact previousCell_apply_of_ne hJ a d k hk
  · exact nextCell_apply_of_ne J hJ a d k hk

theorem cellNeighbor_injective (hJ : 0 < J) (hJ3 : 3 ≤ J) (a : MeshIndex J) :
    Function.Injective (cellNeighbor hJ a) := by
  rintro ⟨d, s⟩ ⟨e, r⟩ h
  have hde : d = e := by
    by_contra hde
    have hh := congrFun h d
    rw [cellNeighbor_apply_of_ne hJ a e d r hde] at hh
    exact cellNeighbor_apply_same_ne hJ (by omega) a d s hh
  subst e
  cases s <;> cases r
  · rfl
  · exact False.elim (nextCell_ne_previousCell hJ hJ3 a d h.symm)
  · exact False.elim (nextCell_ne_previousCell hJ hJ3 a d h)
  · rfl

theorem edgeAdjacent_iff_neighbor (hJ : 0 < J) (a b : MeshIndex J) :
    EdgeAdjacent J hJ a b ↔ ∃ r, cellNeighbor hJ a r = b := by
  constructor
  · rintro ⟨d, h | h⟩
    · exact ⟨(d, true), h.symm⟩
    · refine ⟨(d, false), ?_⟩
      apply nextCell_injective hJ d
      exact (next_previousCell hJ a d).trans h
  · rintro ⟨⟨d, s⟩, rfl⟩
    cases s
    · exact ⟨d, Or.inr (next_previousCell hJ a d).symm⟩
    · exact edgeAdjacent_nextCell J hJ a d

def cellNeighbors (hJ : 0 < J) (a : MeshIndex J) : Finset (MeshIndex J) := by
  classical
  exact Finset.univ.filter (EdgeAdjacent J hJ a)

theorem mem_cellNeighbors (hJ : 0 < J) (a b : MeshIndex J) :
    b ∈ cellNeighbors hJ a ↔ EdgeAdjacent J hJ a b := by
  classical
  simp only [cellNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem cellNeighbors_eq_image (hJ : 0 < J) (a : MeshIndex J) :
    cellNeighbors hJ a = Finset.univ.image (cellNeighbor hJ a) := by
  classical
  ext b
  simp only [mem_cellNeighbors, Finset.mem_image, Finset.mem_univ, true_and,
    edgeAdjacent_iff_neighbor]

theorem card_cellNeighbors (hJ : 0 < J) (hJ3 : 3 ≤ J) (a : MeshIndex J) :
    (cellNeighbors hJ a).card = 4 := by
  rw [cellNeighbors_eq_image, Finset.card_image_of_injective _ (cellNeighbor_injective hJ hJ3 a)]
  simp

/-- Actual unordered cell pairs incident to the unique half-open cell of a
point. This is an enumeration of the existing EdgeAdjacent relation. -/
def incidentCellEdges (hJ : 0 < J) (a : MeshIndex J) : Finset (Finset (MeshIndex J)) := by
  classical
  exact (cellNeighbors hJ a).image (fun b ↦ {a, b})

theorem card_incidentCellEdges (hJ : 0 < J) (hJ3 : 3 ≤ J) (a : MeshIndex J) :
    (incidentCellEdges hJ a).card = 4 := by
  classical
  have hinj : Set.InjOn (fun b : MeshIndex J ↦ ({a, b} : Finset (MeshIndex J)))
      (cellNeighbors hJ a : Set (MeshIndex J)) := by
    intro b hb c hc hbc
    change ({a, b} : Finset (MeshIndex J)) = {a, c} at hbc
    have hbne : b ≠ a := (((mem_cellNeighbors hJ a b).mp hb).ne (by omega)).symm
    have hmem : b ∈ ({a, c} : Finset (MeshIndex J)) := by rw [← hbc]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton, hbne, false_or] using hmem
  rw [incidentCellEdges, Finset.card_image_of_injOn hinj, card_cellNeighbors hJ hJ3 a]

theorem mem_incidentCellEdges_iff (hJ : 0 < J) (a : MeshIndex J) (e : Finset (MeshIndex J)) :
    e ∈ incidentCellEdges hJ a ↔
      ∃ b c, EdgeAdjacent J hJ b c ∧ e = {b, c} ∧ a ∈ e := by
  classical
  constructor
  · rintro he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    exact ⟨a, b, (mem_cellNeighbors hJ a b).mp hb, rfl, by simp⟩
  · rintro ⟨b, c, hbc, rfl, ha⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · subst a
      exact Finset.mem_image.mpr ⟨c, (mem_cellNeighbors hJ b c).mpr hbc, rfl⟩
    · subst a
      exact Finset.mem_image.mpr ⟨b, (mem_cellNeighbors hJ c b).mpr hbc.symm, by simp [Finset.pair_comm]⟩

theorem point_incident_edges_card (hJ : 0 < J) (hJ3 : 3 ≤ J) (z : Torus) :
    (incidentCellEdges hJ (meshLabel J hJ z)).card = 4 := card_incidentCellEdges hJ hJ3 _

theorem point_incident_edges_iff (hJ : 0 < J) (z : Torus) (e : Finset (MeshIndex J)) :
    e ∈ incidentCellEdges hJ (meshLabel J hJ z) ↔
      ∃ a b, EdgeAdjacent J hJ a b ∧ e = {a, b} ∧
        z ∈ meshCell J hJ a ∪ meshCell J hJ b := by
  classical
  rw [mem_incidentCellEdges_iff]
  constructor
  · rintro ⟨a, b, hab, rfl, hz⟩
    refine ⟨a, b, hab, rfl, ?_⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_union, mem_meshCell] using hz
  · rintro ⟨a, b, hab, rfl, hz⟩
    refine ⟨a, b, hab, rfl, ?_⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_union, mem_meshCell] using hz

theorem source_mesh_three_le {β₀ : ℝ} (hmesh : 8 * (radius β₀ + 4) ≤ J) : 3 ≤ J := by
  have hr := radius_one_le β₀
  omega

end FourCellEdges

section ActualLabelEdges

variable {J N : ℕ} {t : ℝ}

/-- The coordinate witness in the existing labelGraph adjacency. -/
def CoordinateStep (hJ : 0 < J) (i : Fin N) (η ζ : LabelState J N t) : Prop :=
  EdgeAdjacent J hJ (η.val i) (ζ.val i) ∧ Function.update η.val i (ζ.val i) = ζ.val

theorem CoordinateStep.adjacent {hJ : 0 < J} {i : Fin N} {η ζ : LabelState J N t}
    (h : CoordinateStep hJ i η ζ) : LabelAdjacent hJ η ζ := ⟨i, h⟩

theorem CoordinateStep.symm {hJ : 0 < J} {i : Fin N} {η ζ : LabelState J N t}
    (h : CoordinateStep hJ i η ζ) : CoordinateStep hJ i ζ η := by
  refine ⟨h.1.symm, ?_⟩
  funext k
  by_cases hk : k = i
  · subst k
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne hk]
    simpa only [Function.update_of_ne hk] using (congrFun h.2 k).symm

theorem CoordinateStep.unique {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {i j : Fin N} {η ζ : LabelState J N t}
    (hi : CoordinateStep hJ i η ζ) (hj : CoordinateStep hJ j η ζ) : i = j :=
  (update_site_unique η.val (hi.1.ne hJ2) (hi.2.trans hj.2.symm)).1

def coordinateNeighbors (hJ : 0 < J) (i : Fin N) (η : LabelState J N t) :
    Finset (LabelState J N t) := by
  classical
  exact Finset.univ.filter (CoordinateStep hJ i η)

theorem mem_coordinateNeighbors (hJ : 0 < J) (i : Fin N) (η ζ : LabelState J N t) :
    ζ ∈ coordinateNeighbors hJ i η ↔ CoordinateStep hJ i η ζ := by
  classical
  simp only [coordinateNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The changed cell determines the complete neighbor once the other
particle labels are fixed. Thus the cap can only remove incident edges. -/
theorem coordinateNeighbors_card_le_four (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (i : Fin N) (η : LabelState J N t) : (coordinateNeighbors hJ i η).card ≤ 4 := by
  rw [← card_cellNeighbors hJ hJ3 (η.val i)]
  apply Finset.card_le_card_of_injOn (fun ζ : LabelState J N t ↦ ζ.val i)
  · intro ζ hζ
    exact (mem_cellNeighbors hJ _ _).mpr ((mem_coordinateNeighbors hJ i η ζ).mp hζ).1
  · intro ζ hζ ξ hξ he
    apply Subtype.ext
    have hz := ((mem_coordinateNeighbors hJ i η ζ).mp hζ).2
    have hx := ((mem_coordinateNeighbors hJ i η ξ).mp hξ).2
    exact hz.symm.trans ((congrArg (Function.update η.val i) he).trans hx)

def edgeEvent (hJ : 0 < J) (η ζ : LabelState J N t) : Set (Configuration N) :=
  labelFiber hJ η.val ∪ labelFiber hJ ζ.val

theorem edgeEvent_symm (hJ : 0 < J) (η ζ : LabelState J N t) :
    edgeEvent hJ η ζ = edgeEvent hJ ζ η := union_comm _ _

theorem edgeEvent_eq_twoCellFiber {hJ : 0 < J} {i : Fin N} {η ζ : LabelState J N t}
    (h : CoordinateStep hJ i η ζ) :
    edgeEvent hJ η ζ = twoCellFiber hJ η.val i (η.val i) (ζ.val i) := by
  rw [twoCellFiber_eq_union]
  have hu : Function.update η.val i (η.val i) = η.val := by funext k; simp
  rw [hu, h.2]
  rfl

/-- Different prescribed outside labels give disjoint actual two-cell
events. The exceptional coordinate is excluded from this test. -/
theorem disjoint_twoCellFiber_of_outside_ne (hJ : 0 < J)
    (η ζ : LabelVector J N) (i : Fin N) (a b c d : MeshIndex J)
    (hne : ∃ k, k ≠ i ∧ η k ≠ ζ k) :
    Disjoint (twoCellFiber hJ η i a b) (twoCellFiber hJ ζ i c d) := by
  obtain ⟨k, hki, hk⟩ := hne
  apply Set.disjoint_left.mpr
  intro X hX hY
  change (X i ∈ meshCell J hJ a ∪ meshCell J hJ b ∧
    ∀ j, j ≠ i → X j ∈ meshCell J hJ (η j)) at hX
  change (X i ∈ meshCell J hJ c ∪ meshCell J hJ d ∧
    ∀ j, j ≠ i → X j ∈ meshCell J hJ (ζ j)) at hY
  exact hk ((hX.2 k hki).symm.trans (hY.2 k hki))

/-- The unrestricted label fibers are a genuine partition, so their
subfamily at the prescribed cap has total nonnegative integral at most
the global integral. This includes the empty capped graph. -/
theorem sum_label_fiber_integrals_le (hJ : 0 < J) {μ : Measure (Configuration N)}
    {F : Configuration N → ℝ} (hF : Integrable F μ) (hF0 : ∀ X, 0 ≤ F X) :
    (∑ η : LabelState J N t, ∫ X in labelFiber hJ η.val, F X ∂μ) ≤ ∫ X, F X ∂μ := by
  rw [← integral_iUnion_fintype (fun η : LabelState J N t ↦ measurableSet_labelFiber hJ η.val)
    (fun η ζ hηζ ↦ disjoint_labelFiber hJ (fun h ↦ hηζ (Subtype.ext h)))
    (fun _ ↦ hF.integrableOn)]
  exact setIntegral_le_integral hF (Eventually.of_forall hF0)

/-- Actual directed edge restrictions at a fixed changed coordinate. -/
def directedRestrictionSum (hJ : 0 < J) (μ : Measure (Configuration N))
    (i : Fin N) (F : Configuration N → ℝ) : ℝ := by
  classical
  exact ∑ η : LabelState J N t, ∑ ζ : LabelState J N t,
    if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F X ∂μ else 0

theorem directedRestrictionSum_eq (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (μ : Measure (Configuration N)) (i : Fin N) {F : Configuration N → ℝ}
    (hF : Integrable F μ) :
    directedRestrictionSum (t := t) hJ μ i F =
      2 * ∑ η : LabelState J N t, ((coordinateNeighbors hJ i η).card : ℝ) *
        ∫ X in labelFiber hJ η.val, F X ∂μ := by
  classical
  have hsplit (η ζ : LabelState J N t) :
      (if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F X ∂μ else 0) =
      (if CoordinateStep hJ i η ζ then ∫ X in labelFiber hJ η.val, F X ∂μ else 0) +
      (if CoordinateStep hJ i ζ η then ∫ X in labelFiber hJ ζ.val, F X ∂μ else 0) := by
    by_cases he : CoordinateStep hJ i η ζ
    · rw [ite_eq_left he, ite_eq_left he, ite_eq_left he.symm]
      exact setIntegral_union (disjoint_labelFiber hJ
        (fun h ↦ he.adjacent.ne hJ2 (Subtype.ext h))) (measurableSet_labelFiber hJ _)
        hF.integrableOn hF.integrableOn
    · have hr : ¬ CoordinateStep hJ i ζ η := fun hh ↦ he hh.symm
      simp only [he, hr, ite_false, add_zero]
  have hrow (η : LabelState J N t) :
      (∑ ζ : LabelState J N t,
        if CoordinateStep hJ i η ζ then ∫ X in labelFiber hJ η.val, F X ∂μ else 0) =
      ((coordinateNeighbors hJ i η).card : ℝ) * ∫ X in labelFiber hJ η.val, F X ∂μ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  unfold directedRestrictionSum
  simp_rw [hsplit]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun η ζ : LabelState J N t ↦
    if CoordinateStep hJ i ζ η then ∫ X in labelFiber hJ ζ.val, F X ∂μ else 0)]
  simp_rw [hrow]
  ring

/-- The factor eight is the directed count. The actual label energy has
one half of the directed sum, leaving precisely the source factor four. -/
theorem directedRestrictionSum_le (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (μ : Measure (Configuration N)) (i : Fin N) {F : Configuration N → ℝ}
    (hF : Integrable F μ) (hF0 : ∀ X, 0 ≤ F X) :
    directedRestrictionSum (t := t) hJ μ i F ≤ 8 * ∫ X, F X ∂μ := by
  rw [directedRestrictionSum_eq hJ (by omega) μ i hF]
  have hrow (η : LabelState J N t) :
      ((coordinateNeighbors hJ i η).card : ℝ) * (∫ X in labelFiber hJ η.val, F X ∂μ) ≤
        4 * ∫ X in labelFiber hJ η.val, F X ∂μ := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast coordinateNeighbors_card_le_four hJ hJ3 i η
    · exact integral_nonneg hF0
  calc
    _ ≤ 2 * ∑ η : LabelState J N t, 4 * ∫ X in labelFiber hJ η.val, F X ∂μ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun η _ ↦ hrow η) (by norm_num)
    _ = 8 * ∑ η : LabelState J N t, ∫ X in labelFiber hJ η.val, F X ∂μ := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_label_fiber_integrals_le hJ hF hF0) (by norm_num)

/-- Exactly the orientation enumeration used by the actual labelEnergy. -/
def unorderedRestrictionSum (hJ : 0 < J) (μ : Measure (Configuration N))
    (i : Fin N) (F : Configuration N → ℝ) : ℝ := by
  classical
  exact ∑ η : LabelState J N t, ∑ ζ : LabelState J N t,
    if labelRank η < labelRank ζ then
      (if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F X ∂μ else 0) else 0

theorem directedRestrictionSum_eq_twice_unordered (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (μ : Measure (Configuration N)) (i : Fin N) (F : Configuration N → ℝ) :
    directedRestrictionSum (t := t) hJ μ i F = 2 * unorderedRestrictionSum (t := t) hJ μ i F := by
  classical
  let T := fun η ζ : LabelState J N t ↦
    if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F X ∂μ else 0
  have hsym (η ζ : LabelState J N t) : T η ζ = T ζ η := by
    have hs : CoordinateStep hJ i η ζ ↔ CoordinateStep hJ i ζ η :=
      ⟨CoordinateStep.symm, CoordinateStep.symm⟩
    simp only [T, hs, edgeEvent_symm hJ η ζ]
  have hself (η : LabelState J N t) : T η η = 0 := by
    apply ite_eq_right
    intro h
    exact h.adjacent.ne hJ2 rfl
  have hsplit (η ζ : LabelState J N t) : T η ζ =
      (if labelRank η < labelRank ζ then T η ζ else 0) +
      (if labelRank ζ < labelRank η then T ζ η else 0) := by
    rcases lt_trichotomy (labelRank η) (labelRank ζ) with h | h | h
    · simp only [ite_eq_left h, ite_eq_right (not_lt.mpr h.le), add_zero]
    · have he : η = ζ := (Fintype.equivFin (LabelState J N t)).injective h
      subst ζ
      simp only [lt_self_iff_false, ite_false, hself, add_zero]
    · simp only [ite_eq_right (not_lt.mpr h.le), ite_eq_left h, zero_add]
      exact hsym η ζ
  change (∑ η : LabelState J N t, ∑ ζ : LabelState J N t, T η ζ) = _
  calc
    _ = ∑ η : LabelState J N t, ∑ ζ : LabelState J N t,
        ((if labelRank η < labelRank ζ then T η ζ else 0) +
          (if labelRank ζ < labelRank η then T ζ η else 0)) := by
      apply Finset.sum_congr rfl
      intro η hη
      apply Finset.sum_congr rfl
      intro ζ hζ
      exact hsplit η ζ
    _ = unorderedRestrictionSum (t := t) hJ μ i F + unorderedRestrictionSum (t := t) hJ μ i F := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun η ζ : LabelState J N t ↦
        if labelRank ζ < labelRank η then T ζ η else 0)]
      rfl
    _ = _ := by ring

/-- Restricted events, summed over the actual permitted outside labels
and unordered label edges at one coordinate, cost at most four global
integrals. There is no conditioning of the graph weights at the cap. -/
theorem unorderedRestrictionSum_le_four (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (μ : Measure (Configuration N)) (i : Fin N) {F : Configuration N → ℝ}
    (hF : Integrable F μ) (hF0 : ∀ X, 0 ≤ F X) :
    unorderedRestrictionSum (t := t) hJ μ i F ≤ 4 * ∫ X, F X ∂μ := by
  have h := directedRestrictionSum_le (t := t) hJ hJ3 μ i hF hF0
  rw [directedRestrictionSum_eq_twice_unordered hJ (by omega)] at h
  linarith

/-- Summation on the actual capped graph from a local restricted-integral
bound. No graph energy, incidence estimate, or measure transport is assumed. -/
theorem labelEnergy_le_of_restricted_edge_bound (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (μ : Measure (Configuration N)) (β : ℝ) (Φ : LabelState J N t → ℝ)
    (F : Fin N → Configuration N → ℝ)
    (hFi : ∀ i, Integrable (F i) μ) (hF0 : ∀ i X, 0 ≤ F i X)
    (hedge : ∀ η ζ : LabelState J N t, ∀ i, CoordinateStep hJ i η ζ →
      labelTerm hJ β Φ η ζ ≤ ∫ X in edgeEvent hJ η ζ, F i X ∂μ) :
    labelEnergy hJ β Φ ≤ 4 * ∑ i, ∫ X, F i X ∂μ := by
  classical
  have hterm (η ζ : LabelState J N t) : labelTerm hJ β Φ η ζ ≤
      ∑ i : Fin N, if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F i X ∂μ else 0 := by
    by_cases he : LabelAdjacent hJ η ζ
    · obtain ⟨i, hi⟩ := he
      have hi : CoordinateStep hJ i η ζ := hi
      have hsum := Finset.single_le_sum
        (fun j _ ↦ show 0 ≤ (if CoordinateStep hJ j η ζ then
            ∫ X in edgeEvent hJ η ζ, F j X ∂μ else 0) from by
          split_ifs
          · exact integral_nonneg (hF0 j)
          · exact le_rfl)
        (Finset.mem_univ i)
      exact (hedge η ζ i hi).trans (by simpa only [ite_eq_left hi] using hsum)
    · have hi (i : Fin N) : ¬ CoordinateStep hJ i η ζ := fun h ↦ he h.adjacent
      simp only [labelTerm, labelConductance, he, ite_false, zero_mul, hi, Finset.sum_const_zero, le_refl]
  have hsum := Finset.sum_le_sum fun η (_ : η ∈ (Finset.univ : Finset (LabelState J N t))) ↦
    Finset.sum_le_sum fun ζ (_ : ζ ∈ (Finset.univ : Finset (LabelState J N t))) ↦ hterm η ζ
  have hswap : (∑ η : LabelState J N t, ∑ ζ : LabelState J N t, ∑ i : Fin N,
      if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F i X ∂μ else 0) =
      ∑ i : Fin N, directedRestrictionSum (t := t) hJ μ i (F i) := by
    calc
      _ = ∑ η : LabelState J N t, ∑ i : Fin N, ∑ ζ : LabelState J N t,
          if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F i X ∂μ else 0 := by
        apply Finset.sum_congr rfl
        intro η hη
        rw [Finset.sum_comm]
      _ = ∑ i : Fin N, ∑ η : LabelState J N t, ∑ ζ : LabelState J N t,
          if CoordinateStep hJ i η ζ then ∫ X in edgeEvent hJ η ζ, F i X ∂μ else 0 :=
        Finset.sum_comm
      _ = _ := rfl
  rw [directed_label_sum_eq_twice, hswap] at hsum
  have hbound := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) ↦
    directedRestrictionSum_le (t := t) hJ hJ3 μ i (hFi i) (hF0 i)
  rw [← Finset.mul_sum] at hbound
  linarith

end ActualLabelEdges

section GibbsTransport

variable {J N : ℕ} {t : ℝ}

/-- The exact finite positive mass cancels the conditional normalization.
This is a measure identity for the actual Gibbs restriction. -/
theorem twoCell_mass_smul (hJ : 0 < J) (hN : 2 ≤ N)
    (η : LabelVector J N) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    (labelProbability hJ (Function.update η i a) β +
      labelProbability hJ (Function.update η i b) β) • twoCellGibbsMeasure hJ η i a b β =
      (gibbsMeasure greenRealRepresentative N β).restrict (twoCellFiber hJ η i a b) := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let s := twoCellFiber hJ η i a b
  let : IsProbabilityMeasure μ := isProbabilityMeasure_greenGibbs N hN hβ hsub
  have hz : μ s ≠ 0 := greenGibbs_twoCellFiber_ne_zero hJ hN η i hab hβ hsub
  have ht : μ s ≠ ⊤ := measure_ne_top _ _
  rw [← greenGibbs_twoCellFiber hJ η i hab]
  change μ s • ((μ s)⁻¹ • μ.restrict s) = μ.restrict s
  rw [smul_smul, ENNReal.mul_inv_cancel hz ht, one_smul]

/-- Nonnegative extended integrands need no a priori finite moment. -/
theorem twoCell_lintegral_transport (hJ : 0 < J) (hN : 2 ≤ N)
    (η : LabelVector J N) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (F : Configuration N → ℝ≥0∞) :
    (labelProbability hJ (Function.update η i a) β +
      labelProbability hJ (Function.update η i b) β) *
        (∫⁻ X, F X ∂twoCellGibbsMeasure hJ η i a b β) =
      ∫⁻ X in twoCellFiber hJ η i a b, F X ∂gibbsMeasure greenRealRepresentative N β := by
  have h := congrArg (fun ν : Measure (Configuration N) ↦ ∫⁻ X, F X ∂ν)
    (twoCell_mass_smul hJ hN η i hab hβ hsub)
  simpa only [lintegral_smul_measure, smul_eq_mul] using h

/-- Genuine integrability and the exact mass-times-expectation identity.
The original global Gibbs law is retained throughout. -/
theorem twoCell_integral_transport (hJ : 0 < J) (hN : 2 ≤ N)
    (η : LabelVector J N) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration N → ℝ} (hF : Integrable F (gibbsMeasure greenRealRepresentative N β)) :
    Integrable F (twoCellGibbsMeasure hJ η i a b β) ∧
      ((labelProbability hJ (Function.update η i a) β).toReal +
        (labelProbability hJ (Function.update η i b) β).toReal) *
          (∫ X, F X ∂twoCellGibbsMeasure hJ η i a b β) =
        ∫ X in twoCellFiber hJ η i a b, F X ∂gibbsMeasure greenRealRepresentative N β := by
  have hz := greenGibbs_twoCellFiber_ne_zero hJ hN η i hab hβ hsub
  have hi : Integrable F (twoCellGibbsMeasure hJ η i a b β) :=
    hF.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hz)
  have he := congrArg (fun ν : Measure (Configuration N) ↦ ∫ X, F X ∂ν)
    (twoCell_mass_smul hJ hN η i hab hβ hsub)
  rw [integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_add (labelProbability_ne_top hJ hN _ hβ hsub)
      (labelProbability_ne_top hJ hN _ hβ hsub)] at he
  exact ⟨hi, he⟩

theorem graph_edge_integral_transport (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (η ζ : LabelState J N t) (i : Fin N) (he : CoordinateStep hJ i η ζ)
    {F : Configuration N → ℝ} (hF : Integrable F (gibbsMeasure greenRealRepresentative N β)) :
    Integrable F (twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β) ∧
      (labelWeight hJ β η + labelWeight hJ β ζ) *
        (∫ X, F X ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β) =
        ∫ X in edgeEvent hJ η ζ, F X ∂gibbsMeasure greenRealRepresentative N β := by
  have hu : Function.update η.val i (η.val i) = η.val := by funext k; simp
  have h := twoCell_integral_transport hJ hN η.val i (he.1.ne hJ2) hβ hsub hF
  rw [hu, he.2, ← edgeEvent_eq_twoCellFiber he] at h
  exact h

/-- The conductance already used by labelEnergy is exactly the source
unconditioned edge weight w0*p*(1-p). -/
theorem labelConductance_eq_mass_mixing (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (η ζ : LabelState J N t) (i : Fin N) (he : CoordinateStep hJ i η ζ) :
    let p := (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal
    labelConductance hJ β η ζ = (labelWeight hJ β η + labelWeight hJ β ζ) * p * (1 - p) := by
  classical
  have hu : Function.update η.val i (η.val i) = η.val := by funext k; simp
  have hp : 0 < labelWeight hJ β η + labelWeight hJ β ζ :=
    add_pos (labelWeight_pos hJ hN hβ hsub η) (labelWeight_pos hJ hN hβ hsub ζ)
  have hmix : (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal =
      labelWeight hJ β η / (labelWeight hJ β η + labelWeight hJ β ζ) := by
    rw [twoCellMixingWeight, hu, he.2, ENNReal.toReal_div,
      ENNReal.toReal_add (labelProbability_ne_top hJ hN η.val hβ hsub)
        (labelProbability_ne_top hJ hN ζ.val hβ hsub)]
    rfl
  dsimp only
  rw [hmix, labelConductance, ite_eq_left he.adjacent]
  field_simp [hp.ne']
  ring

theorem labelTerm_eq_mass_mixing (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (Φ : LabelState J N t → ℝ) (η ζ : LabelState J N t) (i : Fin N)
    (he : CoordinateStep hJ i η ζ) :
    let p := (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal
    labelTerm hJ β Φ η ζ = (labelWeight hJ β η + labelWeight hJ β ζ) * p * (1 - p) *
      (Φ η - Φ ζ) ^ 2 := by
  dsimp only
  rw [labelTerm, labelConductance_eq_mass_mixing hJ hN hβ hsub η ζ i he]
  ring

def labelMean (hJ : 0 < J) (β : ℝ) (f : Configuration N → ℝ) (η : LabelState J N t) : ℝ :=
  ∫ X, f X ∂labelGibbsMeasure hJ η.val β

theorem labelMean_integrable (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) {f : Configuration N → ℝ}
    (hf : Continuous f) (η : LabelState J N t) :
    Integrable f (labelGibbsMeasure hJ η.val β) := by
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN η.val hβ hsub
  have hm : MemLp f 2 (labelGibbsMeasure hJ η.val β) :=
    ContinuousMap.memLp (μ := labelGibbsMeasure hJ η.val β) (p := 2) ℝ ⟨f, hf⟩
  exact hm.integrable (by norm_num)

/-- The same actual local estimate, in the normalization used by the
source before summation, yields a restricted-integral estimate on the
actual capped label graph. -/
theorem labelEnergy_le_of_twoCell_edge_bound (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (Φ : LabelState J N t → ℝ) (F : Fin N → Configuration N → ℝ)
    (hFi : ∀ i, Integrable (F i) (gibbsMeasure greenRealRepresentative N β))
    (hF0 : ∀ i X, 0 ≤ F i X)
    (hedge : ∀ η ζ : LabelState J N t, ∀ i, CoordinateStep hJ i η ζ →
      labelTerm hJ β Φ η ζ ≤ (labelWeight hJ β η + labelWeight hJ β ζ) *
        (∫ X, F i X ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β)) :
    labelEnergy hJ β Φ ≤ 4 * ∑ i, ∫ X, F i X ∂gibbsMeasure greenRealRepresentative N β := by
  apply labelEnergy_le_of_restricted_edge_bound hJ hJ3 _ β Φ F hFi hF0
  intro η ζ i he
  rw [← (graph_edge_integral_transport hJ (by omega) hN hβ hsub η ζ i he (hFi i)).2]
  exact hedge η ζ i he

end GibbsTransport

section PhysicalEnergySummation

variable {N J : ℕ} {t : ℝ}

def coordinateEnergy (f : Configuration N → ℝ) (i : Fin N) (X : Configuration N) : ℝ :=
  ‖coordinateOrdinaryGradient f i X‖ ^ 2

def totalEnergyDensity (f : Configuration N → ℝ) (X : Configuration N) : ℝ :=
  ∑ i, coordinateEnergy f i X

def outsideEnergy (f : Configuration N → ℝ) (i : Fin N) (X : Configuration N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, coordinateEnergy f j X

theorem outsideEnergy_eq_sub (f : Configuration N → ℝ) (i : Fin N) (X : Configuration N) :
    outsideEnergy f i X = totalEnergyDensity f X - coordinateEnergy f i X := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin N))
    (fun j ↦ coordinateEnergy f j X) (Finset.mem_univ i)
  change outsideEnergy f i X + coordinateEnergy f i X = totalEnergyDensity f X at h
  linarith

/-- Exact original-particle-count identity, before cancelling any factor N. -/
theorem sum_outsideEnergy (f : Configuration N → ℝ) (X : Configuration N) :
    (∑ i, outsideEnergy f i X) = ((N : ℝ) - 1) * totalEnergyDensity f X := by
  simp only [outsideEnergy_eq_sub, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (N : ℝ) * totalEnergyDensity f X - totalEnergyDensity f X = _
  ring

theorem totalEnergyDensity_nonneg (f : Configuration N → ℝ) (X : Configuration N) :
    0 ≤ totalEnergyDensity f X := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem sum_outsideEnergy_le (f : Configuration N → ℝ) (X : Configuration N) :
    (∑ i, outsideEnergy f i X) ≤ (N : ℝ) * totalEnergyDensity f X := by
  rw [sum_outsideEnergy]
  nlinarith [totalEnergyDensity_nonneg f X]

/-- The literal single-edge integrand in the manuscript, retaining both
original N denominators until the coordinate summation. -/
def singleEdgeDensity (A B C : ℝ) (f : Configuration N → ℝ)
    (i : Fin N) (X : Configuration N) : ℝ :=
  A * coordinateEnergy f i X + B / N *
    (outsideEnergy f i X + C / N * coordinateEnergy f i X)

theorem singleEdgeDensity_nonneg {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (f : Configuration N → ℝ) (i : Fin N) (X : Configuration N) :
    0 ≤ singleEdgeDensity A B C f i X := by
  have hi : 0 ≤ coordinateEnergy f i X := sq_nonneg _
  have ho : 0 ≤ outsideEnergy f i X := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold singleEdgeDensity
  positivity

theorem sum_singleEdgeDensity_le (hN : 1 ≤ N) {A B C : ℝ}
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (f : Configuration N → ℝ) (X : Configuration N) :
    (∑ i, singleEdgeDensity A B C f i X) ≤
      (A + B * (1 + C)) * totalEnergyDensity f X := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hb : 0 ≤ B / N := div_nonneg hB (Nat.cast_nonneg N)
  have hc : 0 ≤ C / N := div_nonneg hC (Nat.cast_nonneg N)
  have hbc : B / N * (C / N) ≤ B * C :=
    mul_le_mul (div_le_self hB hn) (div_le_self hC hn) hc hB
  calc
    _ = A * totalEnergyDensity f X + B / N * (∑ i, outsideEnergy f i X) +
        (B / N * (C / N)) * totalEnergyDensity f X := by
      simp only [singleEdgeDensity, mul_add, Finset.sum_add_distrib,
        ← Finset.mul_sum, mul_assoc, totalEnergyDensity]; ring
    _ ≤ A * totalEnergyDensity f X + B / N * ((N : ℝ) * totalEnergyDensity f X) +
        (B * C) * totalEnergyDensity f X := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (sum_outsideEnergy_le f X) hb)) (mul_le_mul_of_nonneg_right hbc
          (totalEnergyDensity_nonneg f X))
    _ = _ := by field_simp [hn0]; ring

theorem integrable_totalEnergyDensity {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {L : ℝ≥0} {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f) :
    Integrable (totalEnergyDensity f) μ := by
  apply integrable_finsetSum
  intro i hi
  exact integrable_coordinate_energy hf μ i

theorem integrable_singleEdgeDensity {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {L : ℝ≥0} {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f)
    (A B C : ℝ) (i : Fin N) : Integrable (singleEdgeDensity A B C f i) μ := by
  have hi := integrable_coordinate_energy hf μ i
  have ho : Integrable (outsideEnergy f i) μ := by
    apply integrable_finsetSum
    intro j hj
    exact integrable_coordinate_energy hf μ j
  exact (hi.const_mul A).add ((ho.add (hi.const_mul (C / N))).const_mul (B / N))

/-- Conditional global boundary estimate. The sole unresolved analytic
input is the genuine quantitative one-edge estimate for actual two-cell
laws; all graph counting, normalization, and summation are derived here.
The coefficient is exactly 4*(A+B*(1+C))/J^2. -/
theorem boundary_energy_of_single_edge (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    {β A B C : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {L : ℝ≥0} {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f)
    (hedge : ∀ η ζ : LabelState J N t, ∀ i, CoordinateStep hJ i η ζ →
      labelTerm hJ β (labelMean hJ β f) η ζ ≤
        (1 / (J : ℝ) ^ 2) * (labelWeight hJ β η + labelWeight hJ β ζ) *
          (∫ X, singleEdgeDensity A B C f i X
            ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β)) :
    labelEnergy (t := t) hJ β (labelMean hJ β f) ≤
      (4 * (A + B * (1 + C)) / (J : ℝ) ^ 2) *
        ∫ X, totalEnergyDensity f X ∂gibbsMeasure greenRealRepresentative N β := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let : IsProbabilityMeasure μ := isProbabilityMeasure_greenGibbs N hN hβ hsub
  let F := fun i X ↦ (1 / (J : ℝ) ^ 2) * singleEdgeDensity A B C f i X
  have hFi (i : Fin N) : Integrable (F i) μ :=
    (integrable_singleEdgeDensity hf A B C i).const_mul _
  have hF0 (i : Fin N) (X : Configuration N) : 0 ≤ F i X :=
    mul_nonneg (by positivity) (singleEdgeDensity_nonneg hA hB hC f i X)
  have hlocal (η ζ : LabelState J N t) (i : Fin N) (he : CoordinateStep hJ i η ζ) :
      labelTerm hJ β (labelMean hJ β f) η ζ ≤
        (labelWeight hJ β η + labelWeight hJ β ζ) *
          (∫ X, F i X ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β) := by
    calc
      _ ≤ _ := hedge η ζ i he
      _ = _ := by rw [integral_const_mul]; ring
  have hgraph := labelEnergy_le_of_twoCell_edge_bound hJ hJ3 hN hβ hsub
    (labelMean hJ β f) F hFi hF0 hlocal
  have hDi (i : Fin N) : Integrable (singleEdgeDensity A B C f i) μ :=
    integrable_singleEdgeDensity hf A B C i
  have hD : Integrable (fun X ↦ ∑ i, singleEdgeDensity A B C f i X) μ :=
    integrable_finsetSum Finset.univ (fun i _ ↦ hDi i)
  have hE := integrable_totalEnergyDensity (μ := μ) hf
  have hi := integral_mono_ae hD (hE.const_mul (A + B * (1 + C)))
    (Eventually.of_forall (sum_singleEdgeDensity_le (by omega) hA hB hC f))
  rw [integral_const_mul] at hi
  have hsum : (∑ i, ∫ X, F i X ∂μ) =
      (1 / (J : ℝ) ^ 2) * ∫ X, ∑ i, singleEdgeDensity A B C f i X ∂μ := by
    simp only [F, integral_const_mul, ← Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hDi i)]
  change labelEnergy (t := t) hJ β (labelMean hJ β f) ≤ 4 * ∑ i, ∫ X, F i X ∂μ at hgraph
  rw [hsum] at hgraph
  calc
    _ ≤ _ := hgraph
    _ ≤ 4 * ((1 / (J : ℝ) ^ 2) * ((A + B * (1 + C)) *
        ∫ X, totalEnergyDensity f X ∂μ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (by positivity)) (by norm_num)
    _ = _ := by ring

/-- Source mesh and coupling wrapper. Capped endpoints are the actual
LabelState vertices. The quantitative local estimate is deliberately
retained until the analytic Proposition 3.11 assembly discharges it. -/
theorem source_boundary_energy_of_single_edge (hN : 2 ≤ N)
    {β β₀ A B C : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    {L : ℝ≥0} {f : Configuration N → ℝ} (hf : ConfigurationEuclideanLipschitzWith L f)
    (hedge : ∀ η ζ : LabelState J N t, ∀ i, CoordinateStep (mesh_pos hmesh) i η ζ →
      labelTerm (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β f) η ζ ≤
        (1 / (J : ℝ) ^ 2) * (labelWeight (mesh_pos hmesh) β η + labelWeight (mesh_pos hmesh) β ζ) *
          (∫ X, singleEdgeDensity A B C f i X
            ∂twoCellGibbsMeasure (mesh_pos hmesh) η.val i (η.val i) (ζ.val i) β)) :
    labelEnergy (t := t) (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β f) ≤
      (4 * (A + B * (1 + C)) / (J : ℝ) ^ 2) *
        ∫ X, totalEnergyDensity f X ∂gibbsMeasure greenRealRepresentative N β :=
  boundary_energy_of_single_edge (mesh_pos hmesh) (source_mesh_three_le hmesh) hN
    hβ (hβ₀.trans_lt hsub) hA hB hC hf hedge

end PhysicalEnergySummation

end PeriodicAttractiveLogGas.BoundaryEdgeSummation
