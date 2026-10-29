import LeanResearch.PeriodicAttractiveLogGas.MeshAdjacentCells
import LeanResearch.PeriodicAttractiveLogGas.TorusDistance
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

/-! SOURCE_ONLY candidate for the prescribed-index geometry in source lines
378–383 and 496–501. Cyclic index distance is identified with an attained
integer-lattice minimum in the sup norm. Counting uses one common displacement
box, and pointwise geometry retains the prescribed closed-cell index. No
separation of sources, unique closed-cell membership, or gap/count premise is
assumed. This source has not been elaborated by its author.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.MeshNearbyGeometry

open MeshCells MeshAdjacentCells

def indexClass {J : ℕ} (a : MeshIndex J) (j : Fin 2) : ZMod J := (a j).val

/-- The signed representative of `a-b`, in the interval closest to zero. -/
def centeredIndexOffset {J : ℕ} (a b : MeshIndex J) (j : Fin 2) : ℤ :=
  (indexClass a j - indexClass b j).valMinAbs

def periodicIndexDistance {J : ℕ} (a b : MeshIndex J) : ℕ :=
  max (centeredIndexOffset a b 0).natAbs (centeredIndexOffset a b 1).natAbs

@[simp] theorem centeredIndexOffset_cast {J : ℕ} (a b : MeshIndex J) (j : Fin 2) :
    (centeredIndexOffset a b j : ZMod J) = indexClass a j - indexClass b j :=
  ZMod.coe_valMinAbs _

theorem periodicIndexDistance_le_iff {J R : ℕ} (a b : MeshIndex J) :
    periodicIndexDistance a b ≤ R ↔ ∀ j : Fin 2, (centeredIndexOffset a b j).natAbs ≤ R := by
  constructor
  · intro h j
    have h0 := (max_le_iff.mp h).1
    have h1 := (max_le_iff.mp h).2
    fin_cases j <;> assumption
  · intro h
    exact max_le (h 0) (h 1)

theorem periodicIndexDistance_comm {J : ℕ} (a b : MeshIndex J) :
    periodicIndexDistance a b = periodicIndexDistance b a := by
  have h (j : Fin 2) : (centeredIndexOffset a b j).natAbs =
      (centeredIndexOffset b a j).natAbs := by
    unfold centeredIndexOffset
    rw [show indexClass a j - indexClass b j = -(indexClass b j - indexClass a j) by abel,
      ZMod.natAbs_valMinAbs_neg]
  simp only [periodicIndexDistance, h]

theorem exists_integer_period {J : ℕ} {u v : ℤ} (h : (u : ZMod J) = (v : ZMod J)) :
    ∃ k : ℤ, u = v + (J : ℤ) * k := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub u v J).mp h
  refine ⟨-m, ?_⟩
  nlinarith

theorem centeredIndexOffset_lattice {J : ℕ} (a b : MeshIndex J) :
    ∃ k : Frequency, ∀ j : Fin 2,
      centeredIndexOffset a b j = (a j : ℤ) - (b j : ℤ) + (J : ℤ) * k j := by
  have h (j : Fin 2) : ∃ k : ℤ,
      centeredIndexOffset a b j = (a j : ℤ) - (b j : ℤ) + (J : ℤ) * k := by
    apply exists_integer_period
    simp only [centeredIndexOffset_cast, Int.cast_sub, Int.cast_natCast, indexClass]
  choose k hk using h
  exact ⟨k, hk⟩

theorem centeredIndexOffset_natAbs_le {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (k : Frequency) (j : Fin 2) :
    (centeredIndexOffset a b j).natAbs ≤
      ((a j : ℤ) - (b j : ℤ) + (J : ℤ) * k j).natAbs := by
  let hJnz : NeZero J := ⟨hJ.ne'⟩
  apply ZMod.natAbs_min_of_le_div_two J
  · simp only [centeredIndexOffset_cast, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero, indexClass]
  · exact ZMod.natAbs_valMinAbs_le _

theorem real_norm_intCast (m : ℤ) : ‖(m : ℝ)‖ = (m.natAbs : ℝ) := by
  rw [Real.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

/-- This is the Pi sup norm, used only for the manuscript's index distance. -/
theorem norm_integer_coordinates (d : Frequency) :
    ‖(fun j : Fin 2 ↦ (d j : ℝ))‖ = ((max (d 0).natAbs (d 1).natAbs : ℕ) : ℝ) := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    rw [real_norm_intCast]
    apply Nat.cast_le.mpr
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  · by_cases h : (d 0).natAbs ≤ (d 1).natAbs
    · rw [max_eq_right h, ← real_norm_intCast]
      exact norm_le_pi_norm (fun j : Fin 2 ↦ (d j : ℝ)) 1
    · rw [max_eq_left (le_of_not_ge h), ← real_norm_intCast]
      exact norm_le_pi_norm (fun j : Fin 2 ↦ (d j : ℝ)) 0

/-- Exact source minimum over `J ℤ²`, with a witness attaining the minimum. -/
theorem periodicIndexDistance_isLeast_lattice {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J) :
    IsLeast (Set.range (fun k : Frequency ↦
      ‖(fun j : Fin 2 ↦ (a j : ℝ) - (b j : ℝ) + (J : ℝ) * (k j : ℝ))‖))
      (periodicIndexDistance a b : ℝ) := by
  constructor
  · obtain ⟨k, hk⟩ := centeredIndexOffset_lattice a b
    refine ⟨k, ?_⟩
    have he : (fun j : Fin 2 ↦ (a j : ℝ) - (b j : ℝ) + (J : ℝ) * (k j : ℝ)) =
        (fun j : Fin 2 ↦ (centeredIndexOffset a b j : ℝ)) := by
      funext j
      exact_mod_cast (hk j).symm
    exact (congrArg norm he).trans (norm_integer_coordinates (centeredIndexOffset a b))
  · rintro r ⟨k, rfl⟩
    let d : Frequency := fun j ↦ (a j : ℤ) - (b j : ℤ) + (J : ℤ) * k j
    have hle : periodicIndexDistance a b ≤ max (d 0).natAbs (d 1).natAbs :=
      max_le ((centeredIndexOffset_natAbs_le hJ a b k 0).trans (le_max_left _ _))
        ((centeredIndexOffset_natAbs_le hJ a b k 1).trans (le_max_right _ _))
    have he : (fun j : Fin 2 ↦ (a j : ℝ) - (b j : ℝ) + (J : ℝ) * (k j : ℝ)) =
        (fun j : Fin 2 ↦ (d j : ℝ)) := by
      funext j
      simp only [d, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    change (periodicIndexDistance a b : ℝ) ≤
      ‖(fun j : Fin 2 ↦ (a j : ℝ) - (b j : ℝ) + (J : ℝ) * (k j : ℝ))‖
    rw [he, norm_integer_coordinates]
    exact_mod_cast hle

def nearbyCells {J : ℕ} (R : ℕ) (a : MeshIndex J) : Finset (MeshIndex J) :=
  Finset.univ.filter fun b ↦ periodicIndexDistance a b ≤ R

def nearbyEdgeCells (J : ℕ) (hJ : 0 < J) (R : ℕ) (a : MeshIndex J) (j : Fin 2) :
    Finset (MeshIndex J) := nearbyCells R a ∪ nearbyCells R (nextCell J hJ a j)

@[simp] theorem mem_nearbyCells {J R : ℕ} (a b : MeshIndex J) :
    b ∈ nearbyCells R a ↔ periodicIndexDistance a b ≤ R := by
  simp only [nearbyCells, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_nearbyEdgeCells (J : ℕ) (hJ : 0 < J) (R : ℕ)
    (a b : MeshIndex J) (j : Fin 2) :
    b ∈ nearbyEdgeCells J hJ R a j ↔
      periodicIndexDistance a b ≤ R ∨ periodicIndexDistance (nextCell J hJ a j) b ≤ R := by
  simp only [nearbyEdgeCells, Finset.mem_union, mem_nearbyCells]

/-- A signed displacement from the reference cell to a prescribed nearby cell. -/
theorem nearby_displacement {J R : ℕ} {a b : MeshIndex J} (hb : b ∈ nearbyCells R a) :
    ∃ d : Frequency, (∀ k : Fin 2, -(R : ℤ) ≤ d k ∧ d k ≤ R) ∧
      ∀ k : Fin 2, (d k : ZMod J) = indexClass b k - indexClass a k := by
  let d : Frequency := fun k ↦ -centeredIndexOffset a b k
  refine ⟨d, ?_, ?_⟩
  · intro k
    have hn := (periodicIndexDistance_le_iff a b).mp ((mem_nearbyCells a b).mp hb) k
    have ha : |centeredIndexOffset a b k| ≤ (R : ℤ) := by
      simpa only [Int.abs_eq_natAbs] using (show ((centeredIndexOffset a b k).natAbs : ℤ) ≤ R by exact_mod_cast hn)
    obtain ⟨hl, hu⟩ := abs_le.mp ha
    dsimp [d]
    constructor <;> omega
  · intro k
    simp only [d, Int.cast_neg, centeredIndexOffset_cast]
    abel

def integerEdgeStep (j : Fin 2) : Frequency := fun k ↦ if k = j then 1 else 0

theorem nextCell_indexClass (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j k : Fin 2) :
    indexClass (nextCell J hJ a j) k = indexClass a k + (integerEdgeStep j k : ZMod J) := by
  by_cases hk : k = j
  · subst k
    rw [indexClass, nextCell_apply_same]
    by_cases ha : (a j).val + 1 < J
    · simp [successorIndex, ha, indexClass, integerEdgeStep]
    · have he : (a j).val + 1 = J := by omega
      have hz : indexClass a j + (1 : ZMod J) = 0 := by
        rw [indexClass, ← Nat.cast_add_one, he, ZMod.natCast_self]
      simpa only [successorIndex, dite_eq_right ha, Nat.cast_zero, integerEdgeStep,
        ite_true, Int.cast_one] using hz.symm
  · rw [indexClass, nextCell_apply_of_ne J hJ a j k hk]
    simp only [indexClass, integerEdgeStep, hk, ite_false, Int.cast_zero, add_zero]

/-- One common bounding box covers the two neighborhoods, even across wrap. -/
theorem nearby_edge_displacement {J R : ℕ} (hJ : 0 < J) {a b : MeshIndex J} (j : Fin 2)
    (hb : b ∈ nearbyEdgeCells J hJ R a j) :
    ∃ d : Frequency, (∀ k : Fin 2, -(R : ℤ) ≤ d k ∧ d k ≤ (R : ℤ) + 1) ∧
      ∀ k : Fin 2, (d k : ZMod J) = indexClass b k - indexClass a k := by
  rcases (mem_nearbyEdgeCells J hJ R a b j).mp hb with hb | hb
  · obtain ⟨d, hd, hc⟩ := nearby_displacement ((mem_nearbyCells a b).mpr hb)
    exact ⟨d, fun k ↦ ⟨(hd k).1, (hd k).2.trans (by omega)⟩, hc⟩
  · obtain ⟨d, hd, hc⟩ := nearby_displacement ((mem_nearbyCells _ b).mpr hb)
    refine ⟨fun k ↦ d k + integerEdgeStep j k, ?_, ?_⟩
    · intro k
      have hs : 0 ≤ integerEdgeStep j k ∧ integerEdgeStep j k ≤ 1 := by
        by_cases hk : k = j <;> simp [integerEdgeStep, hk]
      constructor <;> linarith [(hd k).1, (hd k).2]
    · intro k
      rw [Int.cast_add, hc, nextCell_indexClass]
      abel

def residueIndex (J : ℕ) (hJ : 0 < J) (z : ℤ) : Fin J :=
  ⟨(z : ZMod J).val, by
    let hJnz : NeZero J := ⟨hJ.ne'⟩
    exact ZMod.val_lt _⟩

theorem residueIndex_cast (J : ℕ) (hJ : 0 < J) (z : ℤ) :
    ((residueIndex J hJ z).val : ZMod J) = (z : ZMod J) := by
  let hJnz : NeZero J := ⟨hJ.ne'⟩
  exact ZMod.natCast_zmod_val _

theorem fin_cast_zmod_injective (J : ℕ) (a b : Fin J)
    (h : (a.val : ZMod J) = (b.val : ZMod J)) : a = b := by
  apply Fin.ext
  have he := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using he

def shiftIndex (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (d : Frequency) : MeshIndex J :=
  fun k ↦ residueIndex J hJ ((a k : ℤ) + d k)

theorem shiftIndex_eq (J : ℕ) (hJ : 0 < J) (a b : MeshIndex J) (d : Frequency)
    (hd : ∀ k : Fin 2, (d k : ZMod J) = indexClass b k - indexClass a k) :
    shiftIndex J hJ a d = b := by
  funext k
  apply fin_cast_zmod_injective
  change ((residueIndex J hJ ((a k : ℤ) + d k)).val : ZMod J) = indexClass b k
  rw [residueIndex_cast, Int.cast_add, Int.cast_natCast, hd]
  change indexClass a k + (indexClass b k - indexClass a k) = indexClass b k
  abel

def indexWindow (R : ℕ) : Finset ℤ := Finset.Icc (-(R : ℤ)) ((R : ℤ) + 1)

theorem card_indexWindow (R : ℕ) : (indexWindow R).card = 2 * R + 2 := by
  rw [indexWindow, Int.card_Icc]
  omega

def pairFrequency (p : ℤ × ℤ) : Frequency := fun k ↦ if k = 0 then p.1 else p.2

theorem pairFrequency_coordinates (d : Frequency) : pairFrequency (d 0, d 1) = d := by
  funext k
  fin_cases k <;> simp [pairFrequency]

theorem nearbyEdgeCells_subset_image (J : ℕ) (hJ : 0 < J) (R : ℕ)
    (a : MeshIndex J) (j : Fin 2) :
    nearbyEdgeCells J hJ R a j ⊆
      ((indexWindow R) ×ˢ (indexWindow R)).image (fun p ↦ shiftIndex J hJ a (pairFrequency p)) := by
  intro b hb
  obtain ⟨d, hd, hc⟩ := nearby_edge_displacement hJ j hb
  apply Finset.mem_image.mpr
  refine ⟨(d 0, d 1), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hd 0), Finset.mem_Icc.mpr (hd 1)⟩
  · rw [pairFrequency_coordinates]
    exact shiftIndex_eq J hJ a b d hc

theorem card_nearbyEdgeCells_le (J : ℕ) (hJ : 0 < J) (R : ℕ)
    (a : MeshIndex J) (j : Fin 2) : (nearbyEdgeCells J hJ R a j).card ≤ (2 * R + 2) ^ 2 := by
  calc
    _ ≤ (((indexWindow R) ×ˢ (indexWindow R)).image
        (fun p ↦ shiftIndex J hJ a (pairFrequency p))).card :=
      Finset.card_le_card (nearbyEdgeCells_subset_image J hJ R a j)
    _ ≤ ((indexWindow R) ×ˢ (indexWindow R)).card := Finset.card_image_le
    _ = _ := by simp only [Finset.card_product, card_indexWindow, pow_two]

theorem card_nearbyCells_le (J : ℕ) (hJ : 0 < J) (R : ℕ) (a : MeshIndex J) :
    (nearbyCells R a).card ≤ (2 * R + 2) ^ 2 := by
  apply (Finset.card_le_card (show nearbyCells R a ⊆ nearbyEdgeCells J hJ R a 0 from
    Finset.subset_union_left)).trans
  exact card_nearbyEdgeCells_le J hJ R a 0

/-- Congruent integer displacements give the actual same torus chart. -/
theorem meshChart_integerDisplacement {J : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (d : Frequency) (hd : ∀ k : Fin 2, (d k : ZMod J) = indexClass b k - indexClass a k)
    (V : PlanarSpace) :
    meshChart J a (frequencyVector d + V) = meshChart J b V := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have h (k : Fin 2) : ∃ m : ℤ, d k = (b k : ℤ) - (a k : ℤ) + (J : ℤ) * m := by
    apply exists_integer_period
    simpa only [Int.cast_sub, Int.cast_natCast, indexClass] using hd k
  choose m hm using h
  have he : meshAffine J a (frequencyVector d + V) = meshAffine J b V + frequencyVector m := by
    ext k
    simp only [meshAffine_apply, PiLp.add_apply, frequencyVector_apply]
    apply (div_eq_iff hJr.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hJr.ne']
    have hr : (d k : ℝ) = (b k : ℝ) - (a k : ℝ) + (J : ℝ) * (m k : ℝ) := by
      exact_mod_cast hm k
    nlinarith
  change torusQuotient (meshAffine J a (frequencyVector d + V)) = torusQuotient (meshAffine J b V)
  rw [he, torusQuotient_add_frequencyVector]

theorem closedUnitSquare_subset_closedEdgeRectangle (j : Fin 2) :
    closedUnitSquare ⊆ closedEdgeRectangle j := by
  intro Z hZ k hk
  have hz := hZ k hk
  by_cases hj : k = j
  · change 0 ≤ Z k ∧ Z k ≤ edgeWidth j k
    rw [edgeWidth, ite_eq_left hj]
    exact ⟨hz.1, hz.2.trans (by norm_num)⟩
  · simpa only [edgeWidth, hj, ite_false] using hz

/-- One pointwise lift works for every target point in the whole closed patch.
The label `b` is retained even when `y` also belongs to another closed cell. -/
theorem exists_compatible_edge_lift {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (j : Fin 2) (hb : b ∈ nearbyEdgeCells J hJ R a j)
    {y : Torus} (hy : y ∈ closure (meshCell J hJ b)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ closedEdgeRectangle j, ∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 2 := by
  rw [closure_meshCell J hJ b] at hy
  obtain ⟨V, hV, rfl⟩ := hy
  obtain ⟨d, hd, hc⟩ := nearby_edge_displacement hJ j hb
  refine ⟨frequencyVector d + V, meshChart_integerDisplacement hJ a b d hc V, ?_⟩
  intro Z hZ k
  have hdl : -(R : ℝ) ≤ (d k : ℝ) := by exact_mod_cast (hd k).1
  have hdu : (d k : ℝ) ≤ (R : ℝ) + 1 := by exact_mod_cast (hd k).2
  have hv := hV k (mem_univ k)
  have hz := hZ k (mem_univ k)
  change 0 ≤ V k ∧ V k ≤ 1 at hv
  change 0 ≤ Z k ∧ Z k ≤ edgeWidth j k at hz
  have hw := edgeWidth_le_two j k
  rw [PiLp.add_apply, frequencyVector_apply, abs_le]
  constructor <;> linarith

theorem exists_compatible_cell_lift {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hb : b ∈ nearbyCells R a) {y : Torus} (hy : y ∈ closure (meshCell J hJ b)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ closedUnitSquare, ∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 2 := by
  have he : b ∈ nearbyEdgeCells J hJ R a 0 := Finset.mem_union_left _ hb
  obtain ⟨Y, hY, hbound⟩ := exists_compatible_edge_lift hJ a b 0 he hy
  exact ⟨Y, hY, fun Z hZ ↦ hbound Z (closedUnitSquare_subset_closedEdgeRectangle 0 hZ)⟩

/-- Coordinate control is converted using the genuine Euclidean norm. -/
theorem euclidean_norm_le_sqrt_two_mul {X : PlanarSpace} {L : ℝ} (hL : 0 ≤ L)
    (hX : ∀ k : Fin 2, |X k| ≤ L) : ‖X‖ ≤ Real.sqrt 2 * L := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hL)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h0 := pow_le_pow_left₀ (abs_nonneg _) (hX 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hX 1) 2
  simp only [sq_abs] at h0 h1
  nlinarith

def nearReferenceRadius (R : ℕ) : ℝ := Real.sqrt 2 * ((R : ℝ) + 2)

theorem norm_sub_le_nearReferenceRadius {R : ℕ} {Z Y : PlanarSpace}
    (h : ∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 2) :
    ‖Z - Y‖ ≤ nearReferenceRadius R := by
  apply euclidean_norm_le_sqrt_two_mul (by positivity)
  simpa only [PiLp.sub_apply] using h

theorem nearReferenceRadius_lt_half {J R : ℕ} (hJ : 8 * (R + 4) ≤ J) :
    nearReferenceRadius R < (J : ℝ) / 2 := by
  have hJr : 8 * ((R : ℝ) + 4) ≤ J := by exact_mod_cast hJ
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hm := mul_lt_mul_of_pos_right hs (show (0 : ℝ) < (R : ℝ) + 2 by positivity)
  unfold nearReferenceRadius
  linarith

theorem meshAffine_sub (J : ℕ) (a : MeshIndex J) (Z Y : PlanarSpace) :
    meshAffine J a Z - meshAffine J a Y = (J : ℝ)⁻¹ • (Z - Y) := by
  rw [meshAffine, meshAffine, ← smul_sub]
  congr 1
  abel

theorem torusDistance_meshChart_eq_scaled_norm {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) {Z Y : PlanarSpace} (hZY : ‖Z - Y‖ < (J : ℝ) / 2) :
    torusEuclideanDist (meshChart J a Z) (meshChart J a Y) = (J : ℝ)⁻¹ * ‖Z - Y‖ := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hn : ‖(J : ℝ)⁻¹ • (Z - Y)‖ = (J : ℝ)⁻¹ * ‖Z - Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJr)]
  have hh : ‖(J : ℝ)⁻¹ • (Z - Y)‖ < (1 / 2 : ℝ) := by
    rw [hn, ← div_eq_inv_mul]
    apply (div_lt_iff₀ hJr).mpr
    linarith
  change torusEuclideanNorm (torusQuotient (meshAffine J a Z) -
    torusQuotient (meshAffine J a Y)) = _
  rw [← torusQuotient_sub, meshAffine_sub, torusEuclideanNorm_quotient_eq_of_norm_lt_half hh, hn]

/-- The source's compatible nearby lifts, including the strict half-period
bound and exact distance formula, uniformly over the entire closed edge patch. -/
theorem exists_nearby_edge_reference_lift {J R : ℕ} (hJ : 0 < J)
    (hmesh : 8 * (R + 4) ≤ J) (a b : MeshIndex J) (j : Fin 2)
    (hb : b ∈ nearbyEdgeCells J hJ R a j) {y : Torus}
    (hy : y ∈ closure (meshCell J hJ b)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ closedEdgeRectangle j,
        (∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 2) ∧
        ‖Z - Y‖ ≤ nearReferenceRadius R ∧
        ‖Z - Y‖ < (J : ℝ) / 2 ∧
        torusEuclideanDist (meshChart J a Z) y = (J : ℝ)⁻¹ * ‖Z - Y‖ := by
  obtain ⟨Y, hY, hbound⟩ := exists_compatible_edge_lift hJ a b j hb hy
  refine ⟨Y, hY, ?_⟩
  intro Z hZ
  have hn := norm_sub_le_nearReferenceRadius (hbound Z hZ)
  have hh := hn.trans_lt (nearReferenceRadius_lt_half hmesh)
  exact ⟨hbound Z hZ, hn, hh, by rw [← hY]; exact torusDistance_meshChart_eq_scaled_norm hJ a hh⟩

theorem exists_nearby_cell_reference_lift {J R : ℕ} (hJ : 0 < J)
    (hmesh : 8 * (R + 4) ≤ J) (a b : MeshIndex J) (hb : b ∈ nearbyCells R a)
    {y : Torus} (hy : y ∈ closure (meshCell J hJ b)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ closedUnitSquare,
        (∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 2) ∧
        ‖Z - Y‖ ≤ nearReferenceRadius R ∧
        ‖Z - Y‖ < (J : ℝ) / 2 ∧
        torusEuclideanDist (meshChart J a Z) y = (J : ℝ)⁻¹ * ‖Z - Y‖ := by
  have he : b ∈ nearbyEdgeCells J hJ R a 0 := Finset.mem_union_left _ hb
  obtain ⟨Y, hY, hbound⟩ := exists_nearby_edge_reference_lift hJ hmesh a b 0 he hy
  exact ⟨Y, hY, fun Z hZ ↦ hbound Z (closedUnitSquare_subset_closedEdgeRectangle 0 hZ)⟩

/-- Failure of the integer-distance cutoff gives a whole extra cell width,
for every integer lattice translate of the pair of prescribed indices. -/
theorem exists_far_lattice_coordinate {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hfar : b ∉ nearbyCells R a) (m : Frequency) :
    ∃ k : Fin 2, R < ((a k : ℤ) - (b k : ℤ) + (J : ℤ) * m k).natAbs := by
  by_contra h
  push Not at h
  apply hfar
  apply (mem_nearbyCells a b).mpr
  apply (periodicIndexDistance_le_iff a b).mpr
  intro k
  exact (centeredIndexOffset_natAbs_le hJ a b m k).trans (h k)

/-- The index gap survives the two arbitrary closed-cell offsets. This
bound is proved for every lattice translate, before selecting a minimizer. -/
theorem far_cell_lift_norm_lower {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hfar : b ∉ nearbyCells R a) {U V : PlanarSpace}
    (hU : U ∈ closedUnitSquare) (hV : V ∈ closedUnitSquare) (m : Frequency) :
    (R : ℝ) / J ≤ ‖meshAffine J a U - meshAffine J b V + frequencyVector m‖ := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  obtain ⟨k, hk⟩ := exists_far_lattice_coordinate hJ a b hfar m
  let n : ℤ := (a k : ℤ) - (b k : ℤ) + (J : ℤ) * m k
  have hn : (R : ℝ) + 1 ≤ |(n : ℝ)| := by
    have hnat : R + 1 ≤ n.natAbs := Nat.succ_le_of_lt hk
    have hreal : ((R + 1 : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hnat
    rw [← real_norm_intCast n, Real.norm_eq_abs] at hreal
    simpa only [Nat.cast_add, Nat.cast_one] using hreal
  have hUV : |U k - V k| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(hU k (mem_univ k)).1, (hU k (mem_univ k)).2,
      (hV k (mem_univ k)).1, (hV k (mem_univ k)).2]
  have htri : |(n : ℝ)| ≤ |(n : ℝ) + (U k - V k)| + |U k - V k| := by
    calc
      _ = |((n : ℝ) + (U k - V k)) - (U k - V k)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hlarge : (R : ℝ) ≤ |(n : ℝ) + (U k - V k)| := by linarith
  let X : PlanarSpace := meshAffine J a U - meshAffine J b V + frequencyVector m
  have hcoord : X k = ((n : ℝ) + (U k - V k)) / J := by
    simp only [X, n, PiLp.add_apply, PiLp.sub_apply, meshAffine_apply, frequencyVector_apply,
      Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    field_simp [hJr.ne']
    ring
  have hc : (R : ℝ) / J ≤ |X k| := by
    rw [hcoord, abs_div, abs_of_pos hJr]
    exact (div_le_div_iff_of_pos_right hJr).mpr hlarge
  exact hc.trans (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le X k)

theorem far_cell_chart_gap {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hfar : b ∉ nearbyCells R a) {U V : PlanarSpace}
    (hU : U ∈ closedUnitSquare) (hV : V ∈ closedUnitSquare) :
    (R : ℝ) / J ≤ torusEuclideanDist (meshChart J a U) (meshChart J b V) := by
  change (R : ℝ) / J ≤ torusEuclideanNorm
    (torusQuotient (meshAffine J a U) - torusQuotient (meshAffine J b V))
  rw [← torusQuotient_sub]
  obtain ⟨m, hm⟩ := (torusEuclideanNorm_quotient_isLeast_lattice
    (meshAffine J a U - meshAffine J b V)).1
  rw [← hm]
  exact far_cell_lift_norm_lower hJ a b hfar hU hV m

/-- Pointwise gap on the full closed cells, retaining both prescribed labels. -/
theorem far_closed_cells_gap {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hfar : b ∉ nearbyCells R a) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ b)) :
    (R : ℝ) / J ≤ torusEuclideanDist x y := by
  rw [closure_meshCell J hJ a] at hx
  rw [closure_meshCell J hJ b] at hy
  obtain ⟨U, hU, rfl⟩ := hx
  obtain ⟨V, hV, rfl⟩ := hy
  exact far_cell_chart_gap hJ a b hfar hU hV

/-- Being far from an adjacent union means being far from both cells. -/
theorem far_closed_edge_gap {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (j : Fin 2) (hfar : b ∉ nearbyEdgeCells J hJ R a j) {x y : Torus}
    (hx : x ∈ closure (edgeCellUnion J hJ a j))
    (hy : y ∈ closure (meshCell J hJ b)) : (R : ℝ) / J ≤ torusEuclideanDist x y := by
  have hfa : b ∉ nearbyCells R a := fun hb ↦ hfar (Finset.mem_union_left _ hb)
  have hfb : b ∉ nearbyCells R (nextCell J hJ a j) := fun hb ↦ hfar (Finset.mem_union_right _ hb)
  rw [edgeCellUnion, closure_union] at hx
  rcases hx with hx | hx
  · exact far_closed_cells_gap hJ a b hfa hx hy
  · exact far_closed_cells_gap hJ (nextCell J hJ a j) b hfb hx hy

theorem far_edge_reference_gap {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (j : Fin 2) (hfar : b ∉ nearbyEdgeCells J hJ R a j) {Z : PlanarSpace}
    (hZ : Z ∈ closedEdgeRectangle j) {y : Torus} (hy : y ∈ closure (meshCell J hJ b)) :
    (R : ℝ) / J ≤ torusEuclideanDist (meshChart J a Z) y := by
  apply far_closed_edge_gap hJ a b j hfar _ hy
  rw [closure_edgeCellUnion J hJ a j]
  exact ⟨Z, hZ, rfl⟩

theorem far_cell_reference_gap {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hfar : b ∉ nearbyCells R a) {Z : PlanarSpace} (hZ : Z ∈ closedUnitSquare)
    {y : Torus} (hy : y ∈ closure (meshCell J hJ b)) :
    (R : ℝ) / J ≤ torusEuclideanDist (meshChart J a Z) y := by
  apply far_closed_cells_gap hJ a b hfar _ hy
  rw [closure_meshCell J hJ a]
  exact ⟨Z, hZ, rfl⟩

end PeriodicAttractiveLogGas.MeshNearbyGeometry
