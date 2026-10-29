import LeanResearch.PeriodicAttractiveLogGas.MeshCells
import LeanResearch.PeriodicAttractiveLogGas.RectangleDilation
import Mathlib.MeasureTheory.Group.Measure

/-! Source-only development of the adjacent-cell geometry in source lines
356–386. The coordinate successor includes periodic wrap. Its two-cell chart
is the literal affine map followed by the torus quotient, and the half-open
seam belongs to the successor cell. Both coordinate directions use the same
construction. Normalized transport is proved by splitting into two squares;
no chart, Jacobian, adjacency, or probability identity is assumed.

This candidate has not been elaborated by its author. Central diagnostics,
transitive axiom inspection, independent review, and protected replay are
separate obligations. Nearby/far counting and conditional Gibbs laws are not
asserted here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.MeshAdjacentCells

open MeshCells

/-- Increment one cyclic coordinate, retaining its prescribed representative. -/
def successorIndex (J : ℕ) (hJ : 0 < J) (a : Fin J) : Fin J :=
  if h : a.val + 1 < J then ⟨a.val + 1, h⟩ else ⟨0, hJ⟩

theorem successorIndex_val (J : ℕ) (hJ : 0 < J) (a : Fin J) :
    (successorIndex J hJ a).val = (a.val + 1) % J := by
  by_cases h : a.val + 1 < J
  · simp [successorIndex, h, Nat.mod_eq_of_lt h]
  · have ha : a.val + 1 = J := by omega
    simp [successorIndex, ha]

theorem successorIndex_cast_of_lt (J : ℕ) (hJ : 0 < J) (a : Fin J)
    (ha : a.val + 1 < J) : (successorIndex J hJ a : ℝ) = (a : ℝ) + 1 := by
  simp [successorIndex, ha]

theorem successorIndex_cast_of_wrap (J : ℕ) (hJ : 0 < J) (a : Fin J)
    (ha : ¬ a.val + 1 < J) : (successorIndex J hJ a : ℝ) = 0 := by
  simp [successorIndex, ha]

theorem successorIndex_ne (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : Fin J) :
    successorIndex J hJ a ≠ a := by
  intro he
  have hv := congrArg Fin.val he
  by_cases h : a.val + 1 < J
  · simp only [successorIndex, dite_eq_left h] at hv
    omega
  · simp only [successorIndex, dite_eq_right h] at hv
    have ha := a.isLt
    omega

/-- The positive edge neighbor in coordinate `j`. -/
def nextCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) : MeshIndex J :=
  Function.update a j (successorIndex J hJ (a j))

@[simp] theorem nextCell_apply_same (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    nextCell J hJ a j j = successorIndex J hJ (a j) := by
  simp [nextCell]

theorem nextCell_apply_of_ne (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (j k : Fin 2) (hk : k ≠ j) : nextCell J hJ a j k = a k := by
  simp [nextCell, hk]

theorem nextCell_ne (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J) (a : MeshIndex J) (j : Fin 2) :
    nextCell J hJ a j ≠ a := by
  intro he
  exact successorIndex_ne J hJ hJ2 (a j)
    (by simpa only [nextCell_apply_same] using congrFun he j)

/-- Unoriented periodic edge adjacency. The common closed face is proved below. -/
def EdgeAdjacent (J : ℕ) (hJ : 0 < J) (a b : MeshIndex J) : Prop :=
  ∃ j : Fin 2, b = nextCell J hJ a j ∨ a = nextCell J hJ b j

theorem EdgeAdjacent.symm {J : ℕ} {hJ : 0 < J} {a b : MeshIndex J}
    (h : EdgeAdjacent J hJ a b) : EdgeAdjacent J hJ b a := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, hj.symm⟩

theorem edgeAdjacent_nextCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    EdgeAdjacent J hJ a (nextCell J hJ a j) := ⟨j, Or.inl rfl⟩

theorem EdgeAdjacent.ne {J : ℕ} {hJ : 0 < J} (hJ2 : 2 ≤ J) {a b : MeshIndex J}
    (h : EdgeAdjacent J hJ a b) : a ≠ b := by
  rintro rfl
  obtain ⟨j, hj | hj⟩ := h
  · exact nextCell_ne J hJ hJ2 a j hj.symm
  · exact nextCell_ne J hJ hJ2 a j hj.symm

def edgeStep (j : Fin 2) : PlanarSpace :=
  WithLp.toLp 2 (fun k ↦ if k = j then 1 else 0)

@[simp] theorem edgeStep_apply (j k : Fin 2) : edgeStep j k = if k = j then 1 else 0 := rfl

def edgeWidth (j k : Fin 2) : ℝ := if k = j then 2 else 1

theorem edgeWidth_pos (j k : Fin 2) : 0 < edgeWidth j k := by
  by_cases h : k = j <;> simp [edgeWidth, h]

theorem edgeWidth_le_two (j k : Fin 2) : edgeWidth j k ≤ 2 := by
  by_cases h : k = j <;> simp [edgeWidth, h]

def edgeRectangle (j : Fin 2) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun k : Fin 2 ↦ Ico (0 : ℝ) (edgeWidth j k))

def closedEdgeRectangle (j : Fin 2) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun k : Fin 2 ↦ Icc (0 : ℝ) (edgeWidth j k))

def openEdgeRectangle (j : Fin 2) : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun k : Fin 2 ↦ Ioo (0 : ℝ) (edgeWidth j k))

def secondSquare (j : Fin 2) : Set PlanarSpace :=
  (fun Z : PlanarSpace ↦ Z - edgeStep j) ⁻¹' halfOpenMeshSquare

theorem measurableSet_edgeRectangle (j : Fin 2) : MeasurableSet (edgeRectangle j) :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

theorem measurableSet_openEdgeRectangle (j : Fin 2) : MeasurableSet (openEdgeRectangle j) :=
  (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).measurable

theorem measurableSet_secondSquare (j : Fin 2) : MeasurableSet (secondSquare j) :=
  measurableSet_halfOpenMeshSquare.preimage (measurable_id.sub measurable_const)

theorem secondSquare_eq_image (j : Fin 2) :
    secondSquare j = (fun Z : PlanarSpace ↦ Z + edgeStep j) '' halfOpenMeshSquare := by
  ext Z
  constructor
  · intro hZ
    exact ⟨Z - edgeStep j, hZ, sub_add_cancel _ _⟩
  · rintro ⟨W, hW, rfl⟩
    simpa only [secondSquare, mem_preimage, add_sub_cancel_right] using hW

/-- The seam at coordinate one belongs only to the second half-open square. -/
theorem edgeRectangle_eq_union (j : Fin 2) :
    edgeRectangle j = halfOpenMeshSquare ∪ secondSquare j := by
  ext Z
  constructor
  · intro hZ
    by_cases hj : Z j < 1
    · left
      intro k _
      by_cases hk : k = j
      · subst k
        exact ⟨(hZ j (mem_univ j)).1, hj⟩
      · simpa only [edgeWidth, hk, ite_false] using hZ k (mem_univ k)
    · right
      intro k _
      by_cases hk : k = j
      · subst k
        have hz := hZ j (mem_univ j)
        simp only [edgeWidth, ite_true, mem_Ico] at hz
        change Z j - edgeStep j j ∈ Ico (0 : ℝ) 1
        simp only [edgeStep_apply, ite_true, mem_Ico]
        constructor <;> linarith
      · change Z k - edgeStep j k ∈ Ico (0 : ℝ) 1
        simpa only [edgeStep_apply, hk, ite_false, sub_zero, edgeWidth] using
          hZ k (mem_univ k)
  · rintro (hZ | hZ)
    · intro k _
      have hz := hZ k (mem_univ k)
      by_cases hk : k = j
      · simpa only [edgeWidth, hk, ite_true, mem_Ico] using
          (show 0 ≤ Z k ∧ Z k < 2 from ⟨hz.1, hz.2.trans (by norm_num)⟩)
      · simpa only [edgeWidth, hk, ite_false] using hz
    · intro k _
      have hz := hZ k (mem_univ k)
      change Z k - edgeStep j k ∈ Ico (0 : ℝ) 1 at hz
      by_cases hk : k = j
      · simp only [edgeStep_apply, hk, ite_true, mem_Ico] at hz
        change 0 ≤ Z k ∧ Z k < edgeWidth j k
        rw [edgeWidth, ite_eq_left hk]
        simp only [hk]
        constructor <;> linarith
      · simpa only [edgeStep_apply, hk, ite_false, sub_zero, edgeWidth] using hz

theorem disjoint_square_secondSquare (j : Fin 2) :
    Disjoint halfOpenMeshSquare (secondSquare j) := by
  apply Set.disjoint_left.mpr
  intro Z hZ hS
  have hz := (hZ j (mem_univ j)).2
  have hs := (hS j (mem_univ j)).1
  change 0 ≤ Z j - edgeStep j j at hs
  simp only [edgeStep_apply, ite_true] at hs
  linarith

theorem edgeRectangle_subset_closed (j : Fin 2) : edgeRectangle j ⊆ closedEdgeRectangle j := by
  intro Z hZ k hk
  exact ⟨(hZ k hk).1, (hZ k hk).2.le⟩

theorem edgeRectangle_mem_nhds {j : Fin 2} {Z : PlanarSpace} (hZ : Z ∈ openEdgeRectangle j) :
    edgeRectangle j ∈ 𝓝 Z :=
  (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ)).continuousAt.preimage_mem_nhds
    (set_pi_mem_nhds Set.finite_univ fun k _ ↦
      Ico_mem_nhds_iff.mpr (hZ k (mem_univ k)))

theorem closure_edgeRectangle (j : Fin 2) : closure (edgeRectangle j) = closedEdgeRectangle j := by
  change closure ((PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)) ⁻¹'
      Set.pi Set.univ (fun k : Fin 2 ↦ Ico (0 : ℝ) (edgeWidth j k))) =
    (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)) ⁻¹'
      Set.pi Set.univ (fun k : Fin 2 ↦ Icc (0 : ℝ) (edgeWidth j k))
  rw [← Homeomorph.preimage_closure, closure_pi_set]
  have h (k : Fin 2) : closure (Ico (0 : ℝ) (edgeWidth j k)) = Icc 0 (edgeWidth j k) :=
    closure_Ico (ne_of_lt (edgeWidth_pos j k))
  simp only [h]

theorem isCompact_closedEdgeRectangle (j : Fin 2) : IsCompact (closedEdgeRectangle j) :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

/-- Incrementing the reference coordinate advances the cell, also at wrap. -/
theorem meshChart_add_edgeStep (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (j : Fin 2) (Z : PlanarSpace) :
    meshChart J a (Z + edgeStep j) = meshChart J (nextCell J hJ a j) Z := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  ext k
  rw [meshChart_apply, meshChart_apply]
  by_cases hk : k = j
  · subst k
    simp only [PiLp.add_apply, edgeStep_apply, ite_true, nextCell_apply_same]
    by_cases ha : (a j).val + 1 < J
    · rw [successorIndex_cast_of_lt J hJ (a j) ha]
      congr 1
      ring
    · rw [successorIndex_cast_of_wrap J hJ (a j) ha, zero_add]
      have hav : (a j).val + 1 = J := by omega
      have har : (a j : ℝ) + 1 = J := by exact_mod_cast hav
      have he : ((a j : ℝ) + (Z j + 1)) / J = Z j / J + 1 := by
        apply (div_eq_iff hJr.ne').mpr
        rw [add_mul, div_mul_cancel₀ _ hJr.ne', one_mul]
        linarith
      rw [he]
      exact AddCircle.coe_add_period (1 : ℝ) (Z j / J)
  · rw [nextCell_apply_of_ne J hJ a j k hk]
    change ((((a k : ℝ) + (Z k + edgeStep j k)) / (J : ℝ) : ℝ) : UnitAddCircle) = _
    simp only [edgeStep_apply, hk, ite_false, add_zero]

def edgeCellUnion (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) : Set Torus :=
  meshCell J hJ a ∪ meshCell J hJ (nextCell J hJ a j)

theorem measurableSet_edgeCellUnion (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    MeasurableSet (edgeCellUnion J hJ a j) :=
  (measurableSet_meshCell J hJ a).union (measurableSet_meshCell J hJ _)

theorem disjoint_edgeCells (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) :
    Disjoint (meshCell J hJ a) (meshCell J hJ (nextCell J hJ a j)) :=
  pairwiseDisjoint_meshCell J hJ (Ne.symm (nextCell_ne J hJ hJ2 a j))

theorem meshChart_image_secondSquare (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    meshChart J a '' secondSquare j = meshCell J hJ (nextCell J hJ a j) := by
  rw [secondSquare_eq_image, ← Set.image_comp]
  have hf : meshChart J a ∘ (fun Z : PlanarSpace ↦ Z + edgeStep j) =
      meshChart J (nextCell J hJ a j) := funext (meshChart_add_edgeStep J hJ a j)
  rw [hf, meshChart_image_square J hJ]

theorem meshChart_image_edgeRectangle (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    meshChart J a '' edgeRectangle j = edgeCellUnion J hJ a j := by
  rw [edgeRectangle_eq_union, Set.image_union, meshChart_image_square J hJ,
    meshChart_image_secondSquare J hJ]
  rfl

/-- Exact labels on both sides of the seam; the equality case uses the second cell. -/
theorem meshLabel_meshChart_edgeRectangle (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (j : Fin 2) {Z : PlanarSpace} (hZ : Z ∈ edgeRectangle j) :
    meshLabel J hJ (meshChart J a Z) = if Z j < 1 then a else nextCell J hJ a j := by
  by_cases hj : Z j < 1
  · rw [ite_eq_left hj]
    apply meshLabel_meshChart J hJ a
    intro k _
    by_cases hk : k = j
    · subst k
      exact ⟨(hZ j (mem_univ j)).1, hj⟩
    · simpa only [edgeWidth, hk, ite_false] using hZ k (mem_univ k)
  · rw [ite_eq_right hj]
    have hs : Z - edgeStep j ∈ halfOpenMeshSquare := by
      have hu := hZ
      rw [edgeRectangle_eq_union] at hu
      rcases hu with hu | hu
      · exact False.elim (hj (hu j (mem_univ j)).2)
      · exact hu
    have he := meshChart_add_edgeStep J hJ a j (Z - edgeStep j)
    rw [sub_add_cancel] at he
    rw [he]
    exact meshLabel_meshChart J hJ _ hs

theorem continuous_meshChart (J : ℕ) (a : MeshIndex J) : Continuous (meshChart J a) :=
  isOpenQuotientMap_torusQuotient.continuous.comp (continuous_meshAffine J a)

theorem closure_halfOpenMeshSquare : closure halfOpenMeshSquare = closedUnitSquare := by
  change closure ((PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ : Fin 2 ↦ Ico (0 : ℝ) 1)) =
    (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ : Fin 2 ↦ Icc (0 : ℝ) 1)
  rw [← Homeomorph.preimage_closure, closure_pi_set]
  simp only [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]

theorem closure_meshCell (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    closure (meshCell J hJ a) = meshChart J a '' closedUnitSquare := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rw [← meshChart_image_square J hJ a]
      apply Set.image_mono
      intro Z hZ k hk
      exact ⟨(hZ k hk).1, (hZ k hk).2.le⟩
    · exact (isCompact_closedUnitSquare.image (continuous_meshChart J a)).isClosed
  · rw [← closure_halfOpenMeshSquare, ← meshChart_image_square J hJ a]
    exact image_closure_subset_closure_image (continuous_meshChart J a)

theorem meshAffine_eq_dilation (J : ℕ) (a : MeshIndex J) :
    meshAffine J a = RectangleDilation.affine ((J : ℝ)⁻¹ • meshIndexVector a) J := by
  funext Z
  simp only [meshAffine, RectangleDilation.affine, smul_add]

theorem isOpenMap_meshChart (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    IsOpenMap (meshChart J a) := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have ha : IsOpenMap (meshAffine J a) := by
    rw [meshAffine_eq_dilation]
    exact (RectangleDilation.affineHomeomorph ((J : ℝ)⁻¹ • meshIndexVector a) hJr).isOpenMap
  exact isOpenQuotientMap_torusQuotient.isOpenMap.comp ha

/-- Width strictly below a full period makes even the closed chart injective. -/
theorem injOn_meshChart_closedEdgeRectangle (J : ℕ) (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (a : MeshIndex J) (j : Fin 2) : Set.InjOn (meshChart J a) (closedEdgeRectangle j) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJr2 : (2 : ℝ) < J := by exact_mod_cast (show 2 < J by omega)
  have hmem (Z : PlanarSpace) (hZ : Z ∈ closedEdgeRectangle j) (k : Fin 2) :
      meshAffine J a Z k ∈ Ico ((a k : ℝ) / J) ((a k : ℝ) / J + 1) := by
    rw [meshAffine_apply]
    constructor
    · apply (div_le_div_iff_of_pos_right hJr).mpr
      linarith [(hZ k (mem_univ k)).1]
    · apply (div_lt_iff₀ hJr).mpr
      rw [add_mul, div_mul_cancel₀ _ hJr.ne', one_mul]
      have hw := (edgeWidth_le_two j k).trans_lt hJr2
      linarith [(hZ k (mem_univ k)).2]
  intro Z hZ W hW he
  apply (meshAffine_left_inverse J hJ a).injective
  ext k
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem Z hZ k) (hmem W hW k)).mp
    (congrFun he k)

theorem bijOn_meshChart_edgeRectangle (J : ℕ) (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (a : MeshIndex J) (j : Fin 2) :
    Set.BijOn (meshChart J a) (edgeRectangle j) (edgeCellUnion J hJ a j) := by
  refine ⟨?_, (injOn_meshChart_closedEdgeRectangle J hJ hJ3 a j).mono
    (edgeRectangle_subset_closed j), ?_⟩
  · intro Z hZ
    rw [← meshChart_image_edgeRectangle J hJ a j]
    exact ⟨Z, hZ, rfl⟩
  · intro z hz
    rw [← meshChart_image_edgeRectangle J hJ a j] at hz
    exact hz

theorem closure_edgeCellUnion (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    closure (edgeCellUnion J hJ a j) = meshChart J a '' closedEdgeRectangle j := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rw [← meshChart_image_edgeRectangle J hJ a j]
      exact Set.image_mono (edgeRectangle_subset_closed j)
    · exact ((isCompact_closedEdgeRectangle j).image (continuous_meshChart J a)).isClosed
  · rw [← closure_edgeRectangle, ← meshChart_image_edgeRectangle J hJ a j]
    exact image_closure_subset_closure_image (continuous_meshChart J a)

theorem edgeCellUnion_mem_nhds (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    {j : Fin 2} {Z : PlanarSpace} (hZ : Z ∈ openEdgeRectangle j) :
    edgeCellUnion J hJ a j ∈ 𝓝 (meshChart J a Z) := by
  rw [← meshChart_image_edgeRectangle J hJ a j]
  exact (isOpenMap_meshChart J hJ a).image_mem_nhds (edgeRectangle_mem_nhds hZ)

/-- An actual shared closed edge, not just equality of combinatorial labels. -/
theorem meshChart_shared_edge (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    meshChart J a '' {Z ∈ closedUnitSquare | Z j = 1} =
      meshChart J (nextCell J hJ a j) '' {Z ∈ closedUnitSquare | Z j = 0} := by
  ext z
  constructor
  · rintro ⟨Z, ⟨hZ, hj⟩, rfl⟩
    refine ⟨Z - edgeStep j, ⟨?_, ?_⟩, ?_⟩
    · intro k _
      change Z k - edgeStep j k ∈ Icc (0 : ℝ) 1
      by_cases hk : k = j
      · subst k
        simp [hj]
      · simpa only [edgeStep_apply, hk, ite_false, sub_zero] using hZ k (mem_univ k)
    · change Z j - edgeStep j j = 0
      simp [hj]
    · simpa only [sub_add_cancel] using (meshChart_add_edgeStep J hJ a j (Z - edgeStep j)).symm
  · rintro ⟨Z, ⟨hZ, hj⟩, rfl⟩
    refine ⟨Z + edgeStep j, ⟨?_, ?_⟩, meshChart_add_edgeStep J hJ a j Z⟩
    · intro k _
      change Z k + edgeStep j k ∈ Icc (0 : ℝ) 1
      by_cases hk : k = j
      · subst k
        simp [hj]
      · simpa only [edgeStep_apply, hk, ite_false, add_zero] using hZ k (mem_univ k)
    · change Z j + edgeStep j j = 1
      simp [hj]

theorem shared_edge_subset_closures (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    meshChart J a '' {Z ∈ closedUnitSquare | Z j = 1} ⊆
      closure (meshCell J hJ a) ∩ closure (meshCell J hJ (nextCell J hJ a j)) := by
  intro z hz
  constructor
  · rw [closure_meshCell J hJ a]
    obtain ⟨Z, ⟨hZ, _⟩, he⟩ := hz
    exact ⟨Z, hZ, he⟩
  · rw [meshChart_shared_edge J hJ a j] at hz
    rw [closure_meshCell J hJ (nextCell J hJ a j)]
    obtain ⟨Z, ⟨hZ, _⟩, he⟩ := hz
    exact ⟨Z, hZ, he⟩

theorem shared_edge_nonempty (J : ℕ) (a : MeshIndex J) (j : Fin 2) :
    (meshChart J a '' {Z ∈ closedUnitSquare | Z j = 1}).Nonempty := by
  refine ⟨meshChart J a (edgeStep j), edgeStep j, ⟨?_, ?_⟩, rfl⟩
  · intro k _
    change edgeStep j k ∈ Icc (0 : ℝ) 1
    by_cases hk : k = j <;> simp [hk]
  · simp

/-- The actual normalized planar reference measure in either direction. -/
def edgeLebesgue (j : Fin 2) : Measure PlanarSpace :=
  (2 : ℝ≥0∞)⁻¹ • volume.restrict (edgeRectangle j)

/-- Equal weights arise from the equal Haar masses of the two distinct cells. -/
def edgeCellMeasure (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) : Measure Torus :=
  (2 : ℝ≥0∞)⁻¹ • (meshCellMeasure J hJ a + meshCellMeasure J hJ (nextCell J hJ a j))

theorem torusMeasure_edgeCellUnion (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) :
    torusMeasure (edgeCellUnion J hJ a j) = 2 * ((J : ℝ≥0∞) ^ 2)⁻¹ := by
  rw [edgeCellUnion, measure_union (disjoint_edgeCells J hJ hJ2 a j)
    (measurableSet_meshCell J hJ _), torusMeasure_meshCell J hJ,
    torusMeasure_meshCell J hJ, two_mul]

theorem edgeCellMeasure_eq_normalized (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) :
    edgeCellMeasure J hJ a j =
      ((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict (edgeCellUnion J hJ a j) := by
  rw [edgeCellUnion, Measure.restrict_union (disjoint_edgeCells J hJ hJ2 a j)
    (measurableSet_meshCell J hJ _)]
  simp only [edgeCellMeasure, meshCellMeasure, smul_add, smul_smul, div_eq_mul_inv,
    mul_comm (2 : ℝ≥0∞)⁻¹]

theorem edgeCellMeasure_univ (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    edgeCellMeasure J hJ a j Set.univ = 1 := by
  simp only [edgeCellMeasure, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    meshCellMeasure_univ]
  norm_num only [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (by norm_num) (by finiteness)

instance isProbabilityMeasure_edgeCellMeasure (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (j : Fin 2) : IsProbabilityMeasure (edgeCellMeasure J hJ a j) :=
  ⟨edgeCellMeasure_univ J hJ a j⟩

theorem edgeCellMeasure_absolutelyContinuous (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) : edgeCellMeasure J hJ a j ≪ torusMeasure := by
  rw [edgeCellMeasure_eq_normalized J hJ hJ2 a j]
  exact Measure.absolutelyContinuous_restrict.smul_left _

theorem measurePreserving_meshChart_secondSquare (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (j : Fin 2) :
    MeasurePreserving (meshChart J a) (volume.restrict (secondSquare j))
      (meshCellMeasure J hJ (nextCell J hJ a j)) := by
  have ht : MeasurePreserving (fun Z : PlanarSpace ↦ Z - edgeStep j)
      (volume.restrict (secondSquare j)) (volume.restrict halfOpenMeshSquare) :=
    (measurePreserving_sub_right (volume : Measure PlanarSpace) (edgeStep j)).restrict_preimage
      measurableSet_halfOpenMeshSquare
  have hm := measurePreserving_meshChart J hJ (nextCell J hJ a j)
  rw [← restrict_halfOpenMeshSquare_eq_squareLebesgue] at hm
  apply (hm.comp ht).congr (measurable_meshChart J a)
  exact Eventually.of_forall fun Z ↦ by
    change meshChart J (nextCell J hJ a j) (Z - edgeStep j) = meshChart J a Z
    rw [← meshChart_add_edgeStep J hJ a j (Z - edgeStep j), sub_add_cancel]

/-- Normalized distribution preservation, proved by the two disjoint pieces. -/
theorem measurePreserving_meshChart_edgeRectangle (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (j : Fin 2) :
    MeasurePreserving (meshChart J a) (edgeLebesgue j) (edgeCellMeasure J hJ a j) := by
  have h0 := measurePreserving_meshChart J hJ a
  rw [← restrict_halfOpenMeshSquare_eq_squareLebesgue] at h0
  have h1 := measurePreserving_meshChart_secondSquare J hJ a j
  have h := (h0.add_measure h1).smul_measure (2 : ℝ≥0∞)⁻¹
  have hs : (volume : Measure PlanarSpace).restrict (edgeRectangle j) =
      volume.restrict halfOpenMeshSquare + volume.restrict (secondSquare j) := by
    rw [edgeRectangle_eq_union, Measure.restrict_union (disjoint_square_secondSquare j)
      (measurableSet_secondSquare j)]
  simpa only [edgeLebesgue, edgeCellMeasure, hs] using h

theorem edgeLebesgue_univ (j : Fin 2) : edgeLebesgue j Set.univ = 1 := by
  let a : MeshIndex 3 := fun _ ↦ 0
  have h := (measurePreserving_meshChart_edgeRectangle 3 (by decide) a j).measure_preimage
    nullMeasurableSet_univ
  simpa only [preimage_univ, edgeCellMeasure_univ] using h

instance isProbabilityMeasure_edgeLebesgue (j : Fin 2) : IsProbabilityMeasure (edgeLebesgue j) :=
  ⟨edgeLebesgue_univ j⟩

theorem edgeLebesgue_eq_closed (j : Fin 2) :
    edgeLebesgue j = (2 : ℝ≥0∞)⁻¹ • volume.restrict (closedEdgeRectangle j) := by
  rw [edgeLebesgue]
  exact congrArg (fun μ : Measure PlanarSpace ↦ (2 : ℝ≥0∞)⁻¹ • μ)
    (volume_restrict_halfOpenRectangle_eq_closed (edgeWidth j))

theorem ae_mem_openEdgeRectangle (j : Fin 2) :
    ∀ᵐ Z ∂edgeLebesgue j, Z ∈ openEdgeRectangle j := by
  rw [edgeLebesgue_eq_closed]
  have h : (volume : Measure PlanarSpace).restrict (openEdgeRectangle j) =
      volume.restrict (closedEdgeRectangle j) :=
    volume_restrict_openRectangle_eq_closed (edgeWidth j)
  rw [← h]
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_openEdgeRectangle j)) _

theorem ae_edgeCellUnion_mem_nhds (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    ∀ᵐ z ∂edgeCellMeasure J hJ a j, edgeCellUnion J hJ a j ∈ 𝓝 z := by
  have hm := measurePreserving_meshChart_edgeRectangle J hJ a j
  have h : ∀ᵐ z ∂edgeCellMeasure J hJ a j, z ∈ interior (edgeCellUnion J hJ a j) := by
    rw [← hm.map_eq]
    apply (ae_map_iff hm.aemeasurable isOpen_interior.measurableSet).mpr
    exact (ae_mem_openEdgeRectangle j).mono fun Z hZ ↦
      mem_interior_iff_mem_nhds.mpr (edgeCellUnion_mem_nhds J hJ a hZ)
  exact h.mono fun z hz ↦ mem_interior_iff_mem_nhds.mp hz

/-- The horizontal specialization is the exact source double rectangle. -/
theorem edgeRectangle_zero : edgeRectangle 0 = RectangleDilation.halfOpen .double := rfl

theorem closedEdgeRectangle_zero : closedEdgeRectangle 0 = closedDoubleRectangle := rfl

theorem edgeLebesgue_zero : edgeLebesgue 0 = rectangleLebesgue := by
  rw [edgeLebesgue_eq_closed, closedEdgeRectangle_zero, rectangleLebesgue]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem measurePreserving_meshChart_rectangle (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    MeasurePreserving (meshChart J a) rectangleLebesgue (edgeCellMeasure J hJ a 0) := by
  simpa only [edgeLebesgue_zero] using measurePreserving_meshChart_edgeRectangle J hJ a 0

/-- Every unoriented adjacent pair has one of the proved charts, with its
literal normalized restricted Haar measure. -/
theorem exists_chart_of_edgeAdjacent (J : ℕ) (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (a b : MeshIndex J) (hab : EdgeAdjacent J hJ a b) :
    ∃ c : MeshIndex J, ∃ j : Fin 2,
      Set.BijOn (meshChart J c) (edgeRectangle j) (meshCell J hJ a ∪ meshCell J hJ b) ∧
      MeasurePreserving (meshChart J c) (edgeLebesgue j)
        (((J : ℝ≥0∞) ^ 2 / 2) • torusMeasure.restrict (meshCell J hJ a ∪ meshCell J hJ b)) := by
  have hJ2 : 2 ≤ J := by omega
  obtain ⟨j, hb | ha⟩ := hab
  · subst b
    refine ⟨a, j, bijOn_meshChart_edgeRectangle J hJ hJ3 a j, ?_⟩
    have hm := measurePreserving_meshChart_edgeRectangle J hJ a j
    simpa only [edgeCellMeasure_eq_normalized J hJ hJ2, edgeCellUnion] using hm
  · subst a
    refine ⟨b, j, ?_, ?_⟩
    · simpa only [edgeCellUnion, union_comm] using bijOn_meshChart_edgeRectangle J hJ hJ3 b j
    · have hm := measurePreserving_meshChart_edgeRectangle J hJ b j
      simpa only [edgeCellMeasure_eq_normalized J hJ hJ2, edgeCellUnion, union_comm] using hm

theorem integrable_meshChart_edge_comp (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (j : Fin 2) {f : Torus → ℝ} (hf : Integrable f (edgeCellMeasure J hJ a j)) :
    Integrable (fun Z ↦ f (meshChart J a Z)) (edgeLebesgue j) :=
  (measurePreserving_meshChart_edgeRectangle J hJ a j).integrable_comp_of_integrable hf

theorem integral_meshChart_edge (J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (j : Fin 2) {f : Torus → ℝ} (hf : Integrable f (edgeCellMeasure J hJ a j)) :
    (∫ Z, f (meshChart J a Z) ∂edgeLebesgue j) = ∫ z, f z ∂edgeCellMeasure J hJ a j := by
  have hm := measurePreserving_meshChart_edgeRectangle J hJ a j
  rw [← hm.map_eq]
  exact (integral_map hm.aemeasurable
    (by simpa only [hm.map_eq] using hf.aestronglyMeasurable)).symm

/-- The ordinary affine differential has the literal source factor `1/J`. -/
theorem hasFDerivAt_meshAffine (J : ℕ) (a : MeshIndex J) (Z : PlanarSpace) :
    HasFDerivAt (meshAffine J a) ((J : ℝ)⁻¹ • ContinuousLinearMap.id ℝ PlanarSpace) Z := by
  rw [meshAffine_eq_dilation]
  exact RectangleDilation.hasFDerivAt_affine _ _ _

theorem fderiv_meshChart_pullback (J : ℕ) (a : MeshIndex J) {f : Torus → ℝ}
    {Z : PlanarSpace} (hf : DifferentiableAt ℝ (fun x ↦ f (torusQuotient x)) (meshAffine J a Z)) :
    fderiv ℝ (fun W ↦ f (meshChart J a W)) Z =
      (J : ℝ)⁻¹ • fderiv ℝ (fun x ↦ f (torusQuotient x)) (meshAffine J a Z) := by
  have hd := hf.hasFDerivAt.comp Z (hasFDerivAt_meshAffine J a Z)
  change HasFDerivAt (fun W ↦ f (meshChart J a W))
    ((fderiv ℝ (fun x ↦ f (torusQuotient x)) (meshAffine J a Z)).comp
      ((J : ℝ)⁻¹ • ContinuousLinearMap.id ℝ PlanarSpace)) Z at hd
  rw [hd.fderiv]
  ext v
  simp

/-- For an actual globally Lipschitz torus lift, Haar-a.e. differentiability
is transported by the proved chart. No derivative compatibility is assumed. -/
theorem ae_gradient_meshChart (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun x : PlanarSpace ↦ f (torusQuotient x))) :
    rectangleOrdinaryGradient (fun Z ↦ f (meshChart J a Z)) =ᵐ[edgeLebesgue j]
      fun Z ↦ (J : ℝ)⁻¹ • torusLiftGradient f (meshChart J a Z) := by
  have hd := (edgeCellMeasure_absolutelyContinuous J hJ hJ2 a j).ae_le
    (ae_hasFDerivAt_torusLiftGradient f hf)
  have hp := (measurePreserving_meshChart_edgeRectangle J hJ a j).quasiMeasurePreserving.ae hd
  filter_upwards [hp] with Z hZ
  have hder := hZ (meshAffine J a Z) rfl
  unfold rectangleOrdinaryGradient
  rw [fderiv_meshChart_pullback J a hder.differentiableAt, hder.fderiv, map_smul]
  have hdual (v : PlanarSpace) : innerSL ℝ v = (InnerProductSpace.toDual ℝ PlanarSpace) v := by
    ext w
    rfl
  rw [hdual, LinearIsometryEquiv.symm_apply_apply]

theorem integrable_torusGradient_energy_edge (J : ℕ) (hJ : 0 < J)
    (a : MeshIndex J) (j : Fin 2) (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun x : PlanarSpace ↦ f (torusQuotient x))) :
    Integrable (fun z ↦ ‖torusLiftGradient f z‖ ^ 2) (edgeCellMeasure J hJ a j) := by
  have hm : MemLp (torusLiftGradient f) 2 (edgeCellMeasure J hJ a j) := by
    apply MemLp.of_bound (measurable_torusLiftGradient f).aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun z ↦ by
      rw [torusLiftGradient_norm]
      exact norm_descendedLiftGradient_le _ (lipschitz_torusConfigurationValue_lift f hf) _
  exact (memLp_two_iff_integrable_sq_norm (measurable_torusLiftGradient f).aestronglyMeasurable).mp hm

theorem integrable_gradient_meshChart_energy (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun x : PlanarSpace ↦ f (torusQuotient x))) :
    Integrable (fun Z ↦ ‖rectangleOrdinaryGradient (fun W ↦ f (meshChart J a W)) Z‖ ^ 2)
      (edgeLebesgue j) := by
  have h := ((measurePreserving_meshChart_edgeRectangle J hJ a j).integrable_comp_of_integrable
    (integrable_torusGradient_energy_edge J hJ a j f hf)).const_mul ((J : ℝ)⁻¹ ^ 2)
  apply h.congr
  filter_upwards [ae_gradient_meshChart J hJ hJ2 a j f hf] with Z hZ
  rw [hZ, norm_smul, mul_pow]
  simp only [Real.norm_eq_abs, sq_abs, Function.comp_def]

/-- Exact squared-gradient factor for either orientation and across wrap.
The remaining extension from functions given only on a closed patch is not
part of this globally Lipschitz statement. -/
theorem integral_gradient_meshChart_energy (J : ℕ) (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (j : Fin 2) (f : C(Torus, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun x : PlanarSpace ↦ f (torusQuotient x))) :
    (∫ Z, ‖rectangleOrdinaryGradient (fun W ↦ f (meshChart J a W)) Z‖ ^ 2 ∂edgeLebesgue j) =
      ((J : ℝ) ^ 2)⁻¹ * ∫ z, ‖torusLiftGradient f z‖ ^ 2 ∂edgeCellMeasure J hJ a j := by
  calc
    _ = ∫ Z, (J : ℝ)⁻¹ ^ 2 * ‖torusLiftGradient f (meshChart J a Z)‖ ^ 2 ∂edgeLebesgue j := by
      apply integral_congr_ae
      filter_upwards [ae_gradient_meshChart J hJ hJ2 a j f hf] with Z hZ
      rw [hZ, norm_smul, mul_pow]
      simp only [Real.norm_eq_abs, sq_abs]
    _ = _ := by
      rw [integral_const_mul, integral_meshChart_edge J hJ a j
        (integrable_torusGradient_energy_edge J hJ a j f hf), inv_pow]

end PeriodicAttractiveLogGas.MeshAdjacentCells
