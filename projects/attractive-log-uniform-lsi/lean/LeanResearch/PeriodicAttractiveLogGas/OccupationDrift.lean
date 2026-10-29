import LeanResearch.PeriodicAttractiveLogGas.OccupationReverseRates
import LeanResearch.PeriodicAttractiveLogGas.OccupationRootBound
import LeanResearch.PeriodicAttractiveLogGas.LabelGroundState
import LeanResearch.PeriodicAttractiveLogGas.BoundaryEdgeSummation

/-! Source eq:occupation-W-bound. All sums use the original outer occupation
rates. Unordered cell edges are enumerated by a rank, not by a support graph. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationDrift
open MeshCells MeshAdjacentCells LabelOccupations LabelRatioTransport
  DiscreteOccupationIdentities ConditionalLawEstimates OccupationReverseRates
  OccupationSecondDifferences LabelGroundState

/-- A rank chooses one orientation of each actual unordered adjacent cell pair. -/
def cellRank {J : ℕ} (a : MeshIndex J) : Fin (Fintype.card (MeshIndex J)) :=
  Fintype.equivFin (MeshIndex J) a

def unorderedSum {J : ℕ} (hJ : 0 < J) (F : MeshIndex J → MeshIndex J → ℝ) : ℝ := by
  classical
  exact ∑ a, ∑ b, if cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b then F a b else 0

def directedSum {J : ℕ} (hJ : 0 < J) (F : MeshIndex J → MeshIndex J → ℝ) : ℝ := by
  classical
  exact ∑ a, ∑ b, if EdgeAdjacent J hJ a b then F a b else 0

theorem directed_eq_twice_unordered {J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (F : MeshIndex J → MeshIndex J → ℝ) (hF : ∀ a b, F a b = F b a) :
    directedSum hJ F = 2 * unorderedSum hJ F := by
  classical
  unfold directedSum
  have hp (a b : MeshIndex J) :
      (if EdgeAdjacent J hJ a b then F a b else 0) =
      (if cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b then F a b else 0) +
      (if cellRank b < cellRank a ∧ EdgeAdjacent J hJ b a then F b a else 0) := by
    by_cases he : EdgeAdjacent J hJ a b
    · rcases lt_trichotomy (cellRank a) (cellRank b) with hr | hr | hr
      · simp only [he, he.symm, hr, not_lt.mpr hr.le, true_and, false_and, ite_true, ite_false, add_zero]
      · have hab : a = b := (Fintype.equivFin (MeshIndex J)).injective hr
        exact False.elim ((he.ne hJ2) hab)
      · simp only [he, he.symm, hr, not_lt.mpr hr.le, true_and, false_and, ite_true, ite_false, zero_add]
        exact hF a b
    · have he' : ¬ EdgeAdjacent J hJ b a := fun h => he h.symm
      simp only [he, he', and_false, ite_false, add_zero]
  calc
    _ = ∑ a, ∑ b,
        ((if cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b then F a b else 0) +
          (if cellRank b < cellRank a ∧ EdgeAdjacent J hJ b a then F b a else 0)) := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      exact hp a b
    _ = unorderedSum hJ F + unorderedSum hJ F := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun a b : MeshIndex J =>
        if cellRank b < cellRank a ∧ EdgeAdjacent J hJ b a then F b a else 0)]
      rfl
    _ = _ := by ring

/-- Exact number of unordered adjacent cell edges on the admitted mesh. -/
theorem unordered_cell_edge_count {J : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J) :
    unorderedSum hJ (fun _ _ => 1) = 2 * (J ^ 2 : ℕ) := by
  classical
  have hc (a : MeshIndex J) :
      (∑ b : MeshIndex J, if EdgeAdjacent J hJ a b then (1 : ℝ) else 0) = 4 := by
    have hh := BoundaryEdgeSummation.card_cellNeighbors hJ hJ3 a
    have hh' := congrArg (fun k : ℕ => (k : ℝ)) hh
    simpa only [BoundaryEdgeSummation.cellNeighbors, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] using hh'
  have hs := directed_eq_twice_unordered hJ (by omega) (fun _ _ => (1 : ℝ)) (fun _ _ => rfl)
  unfold directedSum at hs
  simp_rw [hc] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_meshIndex] at hs
  nlinarith only [hs]

/-- A missing source contributes zero; the moved occupation is constructed
only in the positive-source branch. -/
def directionRate {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N)
    (a b : MeshIndex J) : ℝ :=
  if ha : 1 ≤ m.val a then occupationRate hJ β m (movedState m hm hmargin a b ha) else 0

def directionTerm {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N)
    (a b : MeshIndex J) : ℝ :=
  if ha : 1 ≤ m.val a then
    occupationRate hJ β m (movedState m hm hmargin a b ha) -
      Real.sqrt (occupationRate hJ β m (movedState m hm hmargin a b ha) *
        occupationRate hJ β (movedState m hm hmargin a b ha) m) else 0

/-- Literal source imbalance over each actual unordered cell edge once. -/
def imbalance {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N) : ℝ :=
  unorderedSum hJ (fun a b =>
    (Real.sqrt (directionRate hJ β m hm hmargin a b) -
      Real.sqrt (directionRate hJ β m hm hmargin b a)) ^ 2)


/-- Pairing a nonsymmetric directed quantity adds the two genuine directions. -/
theorem directed_eq_unordered_add {J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (F : MeshIndex J → MeshIndex J → ℝ) :
    directedSum hJ F = unorderedSum hJ (fun a b => F a b + F b a) := by
  classical
  have hswap : directedSum hJ (fun a b => F b a) = directedSum hJ F := by
    unfold directedSum
    rw [Finset.sum_comm (f := fun a b : MeshIndex J => if EdgeAdjacent J hJ a b then F b a else 0)]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    by_cases he : EdgeAdjacent J hJ a b
    · simp only [he, he.symm, ite_true]
    · have he' : ¬ EdgeAdjacent J hJ b a := fun h => he h.symm
      simp only [he, he', ite_false]
  have hadd : directedSum hJ (fun a b => F a b + F b a) =
      directedSum hJ F + directedSum hJ (fun a b => F b a) := by
    unfold directedSum
    have hd (a b : MeshIndex J) :
        (if EdgeAdjacent J hJ a b then F a b + F b a else 0) =
          (if EdgeAdjacent J hJ a b then F a b else 0) +
          (if EdgeAdjacent J hJ a b then F b a else 0) := by
      by_cases he : EdgeAdjacent J hJ a b <;> simp only [he, ite_true, ite_false, add_zero]
    simp_rw [hd]
    simp only [Finset.sum_add_distrib]
  have hh := directed_eq_twice_unordered hJ hJ2 (fun a b => F a b + F b a)
    (fun a b => add_comm _ _)
  rw [hadd, hswap] at hh
  linarith only [hh]

def occupationTerm {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (m m' : OccupationState J N t) : ℝ :=
  occupationRate hJ β m m' - Real.sqrt (occupationRate hJ β m m' * occupationRate hJ β m' m)

/-- Unique source and target cells recover each nonzero outer occupation term. -/
theorem term_eq_sum_permitted {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (m m' : OccupationState J N t) :
    occupationTerm hJ β m m' = by
      classical
      exact ∑ a, ∑ b, if PermittedMove hJ m m' a b then occupationTerm hJ β m m' else 0 := by
  classical
  by_cases he : ∃ a b, PermittedMove hJ m m' a b
  · obtain ⟨a, b, hab⟩ := he
    symm
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp only [ite_eq_left hab]
      · intro c _ hcb
        have hn : ¬ PermittedMove hJ m m' a c := fun h => hcb (hab.unique hJ2 h).2.symm
        simp only [ite_eq_right hn]
      · simp
    · intro c _ hca
      apply Finset.sum_eq_zero
      intro d _
      have hn : ¬ PermittedMove hJ m m' c d := fun h => hca (hab.unique hJ2 h).1.symm
      simp only [ite_eq_right hn]
    · simp
  · have hz := occupationRate_eq_zero hJ β he
    simp only [occupationTerm, hz, zero_mul, Real.sqrt_zero, sub_self]
    symm
    apply Finset.sum_eq_zero; intro a _
    apply Finset.sum_eq_zero; intro b _
    exact ite_eq_right (fun h => he ⟨a, b, h⟩)

/-- For a fixed direction the original outer sum contains exactly its actual move. -/
theorem sum_permitted_direction {J N : ℕ} {t : ℝ} (hJ : 0 < J) (β : ℝ)
    (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (3 * t / 4))
    (hmargin : 4 ≤ t * N) (a b : MeshIndex J) :
    (by classical exact ∑ m', if PermittedMove hJ m m' a b then occupationTerm hJ β m m' else 0) =
    (by classical exact if EdgeAdjacent J hJ a b then directionTerm hJ β m hm hmargin a b else 0) := by
  classical
  by_cases he : EdgeAdjacent J hJ a b
  · by_cases ha : 1 ≤ m.val a
    · let m' := movedState m hm hmargin a b ha
      have hp : PermittedMove hJ m m' a b := ⟨he, ha, rfl⟩
      rw [Finset.sum_eq_single m']
      · simp only [ite_eq_left hp, ite_eq_left he, directionTerm, dite_eq_left ha, occupationTerm]
        rfl
      · intro z _ hzm
        have hn : ¬ PermittedMove hJ m z a b := by
          intro hz
          apply hzm
          exact Subtype.ext hz.2.2.symm
        simp only [ite_eq_right hn]
      · simp
    · have hn (z : OccupationState J N t) : ¬ PermittedMove hJ m z a b := fun h => ha h.2.1
      simp only [ite_eq_right (hn _), Finset.sum_const_zero, ite_eq_left he, directionTerm, dite_eq_right ha]
  · have hn (z : OccupationState J N t) : ¬ PermittedMove hJ m z a b := fun h => he h.1
    simp only [ite_eq_right (hn _), Finset.sum_const_zero, ite_eq_right he]

/-- Genuine reindexing of the original outer occupation sum into unordered cell pairs. -/
theorem occupationW_eq_unordered {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (3 * t / 4))
    (hmargin : 4 ≤ t * N) :
    occupationW hJ β m = unorderedSum hJ (fun a b =>
      directionTerm hJ β m hm hmargin a b + directionTerm hJ β m hm hmargin b a) := by
  classical
  rw [occupationW_eq_rates hJ hJ2 hN hβ hsub]
  change (∑ m', occupationTerm hJ β m m') = _
  have hsum : (∑ m', occupationTerm hJ β m m') =
      ∑ m', ∑ a, ∑ b, if PermittedMove hJ m m' a b then occupationTerm hJ β m m' else 0 := by
    apply Finset.sum_congr rfl; intro m' _
    exact term_eq_sum_permitted hJ hJ2 β m m'
  rw [hsum]
  rw [Finset.sum_comm (f := fun m' a => ∑ b,
    if PermittedMove hJ m m' a b then occupationTerm hJ β m m' else 0)]
  have he : (∑ a, ∑ m', ∑ b, if PermittedMove hJ m m' a b then occupationTerm hJ β m m' else 0) =
      directedSum hJ (directionTerm hJ β m hm hmargin) := by
    unfold directedSum
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm (f := fun m' b => if PermittedMove hJ m m' a b then occupationTerm hJ β m m' else 0)]
    apply Finset.sum_congr rfl; intro b _
    exact sum_permitted_direction hJ β m hm hmargin a b
  rw [he, directed_eq_unordered_add hJ hJ2]


/-- The paired source root estimate when the first departure cell is nonempty. -/
theorem paired_bound_of_positive {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : secondDifferenceThreshold J β₀ ≤ N)
    (hmargin : 4 ≤ t * N) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4))
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) (ha : 1 ≤ m.val a) :
    (Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin a b) -
      Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin b a)) ^ 2 / 2 -
      5 * (1 + secondDifferenceConstant J β₀ / 4) ≤
    directionTerm (mesh_pos hmesh) β m hm hmargin a b +
      directionTerm (mesh_pos hmesh) β m hm hmargin b a := by
  have hN := (secondDifferenceThreshold_bounds hlarge).1
  have hE : 1 ≤ 1 + secondDifferenceConstant J β₀ / 4 := by
    have hc := secondDifferenceConstant_nonneg J (hβ.trans hβ₀)
    linarith
  let mp := movedState m hm hmargin a b ha
  have hp : PermittedMove (mesh_pos hmesh) m mp a b := ⟨hab, ha, rfl⟩
  by_cases hb : 1 ≤ m.val b
  · let mm := movedState m hm hmargin b a hb
    have hrev := reverse_rate_comparison hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hm a b hab ha hb
    have hopp := reverse_rate_comparison hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hm b a hab.symm hb ha
    have hh := OccupationRootBound.occupation_root_bound
      (occupationRate_nonneg (mesh_pos hmesh) β m mp) (occupationRate_nonneg (mesh_pos hmesh) β m mm)
      (occupationRate_nonneg (mesh_pos hmesh) β mp m) (occupationRate_nonneg (mesh_pos hmesh) β mm m)
      hrev hopp
    simp only [directionRate, directionTerm, dite_eq_left ha, dite_eq_left hb]
    change (Real.sqrt (occupationRate (mesh_pos hmesh) β m mp) -
      Real.sqrt (occupationRate (mesh_pos hmesh) β m mm)) ^ 2 / 2 - _ ≤ _
    linarith only [hh]
  · have hb0 : m.val b = 0 := by omega
    have hr := reverse_rate_le_one_of_zero (mesh_pos hmesh) (mesh_two_le hmesh) hN hβ
      (hβ₀.trans_lt hsub) hp hb0
    have hn := occupationRate_nonneg (mesh_pos hmesh) β mp m
    have hf := occupationRate_nonneg (mesh_pos hmesh) β m mp
    -- The last argument is an auxiliary scalar, not a transition from a missing occupation.
    have hh := OccupationRootBound.occupation_root_bound hf (le_refl (0 : ℝ)) hn hf
      (show |occupationRate (mesh_pos hmesh) β mp m - 0| ≤ 1 + secondDifferenceConstant J β₀ / 4 by
        rw [sub_zero, abs_of_nonneg hn]; exact hr.trans hE)
      (show |occupationRate (mesh_pos hmesh) β m mp - occupationRate (mesh_pos hmesh) β m mp| ≤
          1 + secondDifferenceConstant J β₀ / 4 by simpa only [sub_self, abs_zero] using (by linarith : (0 : ℝ) ≤ 1 + secondDifferenceConstant J β₀ / 4))
    simp only [directionRate, directionTerm, dite_eq_left ha, dite_eq_right hb,
      Real.sqrt_zero, sub_zero, add_zero]
    simpa only [add_zero, zero_mul, Real.sqrt_zero, sub_zero] using hh

/-- All count cases, including both empty cells, in the actual unordered-pair estimate. -/
theorem paired_bound {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : secondDifferenceThreshold J β₀ ≤ N)
    (hmargin : 4 ≤ t * N) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4))
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) :
    (Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin a b) -
      Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin b a)) ^ 2 / 2 -
      5 * (1 + secondDifferenceConstant J β₀ / 4) ≤
    directionTerm (mesh_pos hmesh) β m hm hmargin a b +
      directionTerm (mesh_pos hmesh) β m hm hmargin b a := by
  by_cases ha : 1 ≤ m.val a
  · exact paired_bound_of_positive hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hm a b hab ha
  · by_cases hb : 1 ≤ m.val b
    · have hh := paired_bound_of_positive hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hm b a hab.symm hb
      nlinarith only [hh]
    · simp only [directionRate, directionTerm, dite_eq_right ha, dite_eq_right hb,
        Real.sqrt_zero, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_sub, add_zero]
      have hc := secondDifferenceConstant_nonneg J (hβ.trans hβ₀)
      linarith

/-- Finite unordered summation preserves the literal constant and counts each edge once. -/
theorem unordered_half_sub {J : ℕ} (hJ : 0 < J) (F : MeshIndex J → MeshIndex J → ℝ) (C : ℝ) :
    unorderedSum hJ (fun a b => F a b / 2 - C) =
      unorderedSum hJ F / 2 - C * unorderedSum hJ (fun _ _ => 1) := by
  classical
  unfold unorderedSum
  have hp (a b : MeshIndex J) :
      (if cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b then F a b / 2 - C else 0) =
      (if cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b then F a b else 0) / 2 -
        C * (if cellRank a < cellRank b ∧ EdgeAdjacent J hJ a b then 1 else 0) := by
    split <;> simp only [zero_div, mul_one, mul_zero, sub_zero]
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]

/-- Exact source drift bound, with no assumed drift, reindexing or imbalance estimate. -/
theorem occupation_W_bound {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : secondDifferenceThreshold J β₀ ≤ N)
    (hmargin : 4 ≤ t * N) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) :
    imbalance (mesh_pos hmesh) β m hm hmargin / 2 -
      10 * (J ^ 2 : ℕ) * (1 + secondDifferenceConstant J β₀ / 4) ≤
        occupationW (mesh_pos hmesh) β m := by
  classical
  have hN := (secondDifferenceThreshold_bounds hlarge).1
  rw [occupationW_eq_unordered (mesh_pos hmesh) (mesh_two_le hmesh) hN hβ (hβ₀.trans_lt hsub) m hm hmargin]
  have hs : unorderedSum (mesh_pos hmesh) (fun a b =>
      (Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin a b) -
        Real.sqrt (directionRate (mesh_pos hmesh) β m hm hmargin b a)) ^ 2 / 2 -
        5 * (1 + secondDifferenceConstant J β₀ / 4)) ≤
      unorderedSum (mesh_pos hmesh) (fun a b => directionTerm (mesh_pos hmesh) β m hm hmargin a b +
        directionTerm (mesh_pos hmesh) β m hm hmargin b a) := by
    unfold unorderedSum
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    split
    · rename_i h
      exact paired_bound hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hm a b h.2
    · exact le_rfl
  rw [unordered_half_sub, unordered_cell_edge_count (mesh_pos hmesh) (mesh_three_le hmesh)] at hs
  change imbalance (mesh_pos hmesh) β m hm hmargin / 2 -
    5 * (1 + secondDifferenceConstant J β₀ / 4) * (2 * (J ^ 2 : ℕ)) ≤ _ at hs
  convert hs using 1; ring

end PeriodicAttractiveLogGas.OccupationDrift
