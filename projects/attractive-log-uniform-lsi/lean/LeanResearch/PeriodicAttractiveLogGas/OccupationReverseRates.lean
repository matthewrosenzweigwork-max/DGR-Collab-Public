import LeanResearch.PeriodicAttractiveLogGas.OccupationCentralRates
import LeanResearch.PeriodicAttractiveLogGas.CrossingLogistic
import LeanResearch.PeriodicAttractiveLogGas.OccupationSecondDifferences

/-! Actual opposite/reverse occupation rates, source Lemma occupation-reverse.
The scalar comparison and literal occupation margin precede the source
second-difference instantiation. -/

noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationReverseRates

open MeshCells MeshAdjacentCells LabelOccupations LabelRatioTransport
  DiscreteOccupationIdentities ConditionalLawEstimates CrossingLogistic

/-- The existing derivative proof supplies the exact logistic constant. -/
theorem logistic_probability_difference (x y : ℝ) :
    |Real.sigmoid x - Real.sigmoid y| ≤ (1 / 4 : ℝ) * |x - y| := by
  simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    sigmoid_lipschitz.dist_le_mul x y

/-- Changing one particle count and the log odds gives the exact source constant. -/
theorem logistic_count_comparison {n N C x y : ℝ} (hn : 0 ≤ n) (hnN : n ≤ N)
    (hN : 0 < N) (hC : 0 ≤ C) (hxy : |x - y| ≤ C / N) :
    |(n + 1) * Real.sigmoid x - n * Real.sigmoid y| ≤ 1 + C / 4 := by
  have hp := (logistic_probability_difference x y).trans
    (mul_le_mul_of_nonneg_left hxy (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hc : n * ((1 / 4 : ℝ) * (C / N)) ≤ C / 4 := by
    calc
      _ ≤ N * ((1 / 4 : ℝ) * (C / N)) := mul_le_mul_of_nonneg_right hnN (by positivity)
      _ = C / 4 := by field_simp
  calc
    _ = |n * (Real.sigmoid x - Real.sigmoid y) + Real.sigmoid x| := by congr 1; ring
    _ ≤ |n * (Real.sigmoid x - Real.sigmoid y)| + |Real.sigmoid x| := abs_add_le _ _
    _ = n * |Real.sigmoid x - Real.sigmoid y| + Real.sigmoid x := by
      rw [abs_mul, abs_of_nonneg hn, abs_of_nonneg (Real.sigmoid_nonneg x)]
    _ ≤ n * ((1 / 4 : ℝ) * (C / N)) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hp hn) (Real.sigmoid_le_one x)
    _ ≤ 1 + C / 4 := by linarith only [hc]

/-- Literal three-profile comparison, before discharging the log-Q bound. -/
theorem positive_weight_reverse_comparison {A B D n N C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hn : 0 ≤ n) (hnN : n ≤ N) (hN : 0 < N) (hC : 0 ≤ C)
    (hsecond : |Real.log D - Real.log A - Real.log A + Real.log B| ≤ C / N) :
    |(n + 1) * A / (A + B) - n * D / (A + D)| ≤ 1 + C / 4 := by
  have he : (Real.log A - Real.log B) - (Real.log D - Real.log A) =
      -(Real.log D - Real.log A - Real.log A + Real.log B) := by ring
  have hh := logistic_count_comparison hn hnN hN hC
    (show |(Real.log A - Real.log B) - (Real.log D - Real.log A)| ≤ C / N by
      rw [he, abs_neg]; exact hsecond)
  rw [sigmoid_log_sub hA hB, sigmoid_log_sub hD hA] at hh
  simpa only [add_comm D A, mul_div_assoc] using hh

/-- Every actual count is bounded by the original particle total. -/
theorem count_le_total {J N : ℕ} {t : ℝ} (m : OccupationState J N t) (a : MeshIndex J) :
    m.val a ≤ N := by
  have hh := Finset.single_le_sum (fun b (_hb : b ∈ (Finset.univ : Finset (MeshIndex J))) =>
    Nat.zero_le (m.val b)) (Finset.mem_univ a)
  rwa [m.property.1] at hh

/-- Source move margin: one actual move from the three-quarter cap stays in the outer cap. -/
theorem move_margin {J N : ℕ} {t : ℝ} (m : MeshIndex J → ℕ)
    (hm : m ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N)
    (a b : MeshIndex J) (ha : 1 ≤ m a) :
    moveOccupation m a b ∈ cappedOccupations J N t := by
  obtain ⟨η, i, hη, _hia, hmove⟩ := exists_label_move m hm.1 a b ha
  refine ⟨?_, ?_⟩
  · rw [← hmove]
    exact sum_occupation _
  · intro c
    have hh : moveOccupation m a b c ≤ m c + 1 := by
      unfold moveOccupation
      split <;> split <;> omega
    have hh' : (moveOccupation m a b c : ℝ) ≤ (m c : ℝ) + 1 := by exact_mod_cast hh
    have hc := hm.2 c
    nlinarith only [hh', hc, hmargin]

/-- The inner state itself belongs to the outer state space, even with empty cells. -/
theorem inner_cap_outer {J N : ℕ} {t : ℝ} (m : MeshIndex J → ℕ)
    (hm : m ∈ cappedOccupations J N (3 * t / 4)) :
    m ∈ cappedOccupations J N t := by
  refine ⟨hm.1, fun c => ?_⟩
  have hc := hm.2 c
  nlinarith only [hc]

/-- A zero destination count needs no opposite profile or negative occupation. -/
theorem reverse_rate_le_one_of_zero {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) (hb : m.val b = 0) :
    occupationRate hJ β m' m ≤ 1 := by
  rw [occupationRate_reverse hJ hJ2 β h, hb]
  simp only [zero_add, Nat.cast_one, one_mul]
  have hp := qWeight_pos hJ hN hβ hsub m
  have hq := qWeight_pos hJ hN hβ hsub m'
  exact (div_le_one (add_pos hp hq)).mpr (by linarith only [hq])


/-- The actual moved occupation, with outer membership proved from the source margin. -/
def movedState {J N : ℕ} {t : ℝ} (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4)) (hmargin : 4 ≤ t * N)
    (a b : MeshIndex J) (ha : 1 ≤ m.val a) : OccupationState J N t :=
  ⟨moveOccupation m.val a b, move_margin m.val hm hmargin a b ha⟩

/-- The source comparison for the original rates, with the actual second
log-Q difference proved from the physical four-profile theorem. -/
theorem reverse_rate_comparison {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : OccupationSecondDifferences.secondDifferenceThreshold J β₀ ≤ N)
    (hmargin : 4 ≤ t * N) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (3 * t / 4))
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b)
    (ha : 1 ≤ m.val a) (hb : 1 ≤ m.val b) :
    |occupationRate (mesh_pos hmesh) β (movedState m hm hmargin a b ha) m -
      occupationRate (mesh_pos hmesh) β m (movedState m hm hmargin b a hb)| ≤
      1 + OccupationSecondDifferences.secondDifferenceConstant J β₀ / 4 := by
  let mp := movedState m hm hmargin a b ha
  let mm := movedState m hm hmargin b a hb
  have hp : PermittedMove (mesh_pos hmesh) m mp a b := ⟨hab, ha, rfl⟩
  have hm' : PermittedMove (mesh_pos hmesh) m mm b a := ⟨hab.symm, hb, rfl⟩
  have hi := moveOccupation_inverse m.val (hab.ne (mesh_two_le hmesh)) ha
  have hN := (OccupationSecondDifferences.secondDifferenceThreshold_bounds hlarge).1
  have hcenter : moveOccupation (moveOccupation m.val a b) b a ∈ cappedOccupations J N t := by
    rw [hi]; exact m.property
  have hend : moveOccupation (moveOccupation (moveOccupation m.val a b) b a) b a ∈
      cappedOccupations J N t := by
    rw [hi]; exact mm.property
  have hs := OccupationSecondDifferences.occupation_second_differences hβ hβ₀ hsub ht htC hmesh
    hlarge (moveOccupation m.val a b) b a b a hab.symm hab.symm
    mp.property hcenter hcenter hend
  rw [hi] at hs
  have hs' : |Real.log (qWeight (mesh_pos hmesh) β mm) - Real.log (qWeight (mesh_pos hmesh) β m) -
      Real.log (qWeight (mesh_pos hmesh) β m) + Real.log (qWeight (mesh_pos hmesh) β mp)| ≤
      OccupationSecondDifferences.secondDifferenceConstant J β₀ / (N : ℝ) := hs
  have hnr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnb : (m.val b : ℝ) ≤ N := by exact_mod_cast count_le_total m b
  have hh := positive_weight_reverse_comparison
    (qWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) m)
    (qWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) mp)
    (qWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) mm)
    (Nat.cast_nonneg (m.val b)) hnb hnr
    (OccupationSecondDifferences.secondDifferenceConstant_nonneg J (hβ.trans hβ₀)) hs'
  rw [occupationRate_reverse (mesh_pos hmesh) (mesh_two_le hmesh) β hp,
    occupationRate_of_move (mesh_pos hmesh) (mesh_two_le hmesh) β hm']
  simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- Full source inner-domain formulation. The positive and zero destination
branches use only natural occupations; no negative-profile Q is evaluated. -/
theorem source_reverse_rates {J N : ℕ} {t β β₀ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : OccupationSecondDifferences.secondDifferenceThreshold J β₀ ≤ N)
    (hmargin : 4 ≤ t * N) (n : MeshIndex J → ℕ)
    (hn : n ∈ cappedOccupations J N (3 * t / 4))
    (a b : MeshIndex J) (hab : EdgeAdjacent J (mesh_pos hmesh) a b) (ha : 1 ≤ n a) :
    let m : OccupationState J N t := ⟨n, inner_cap_outer n hn⟩
    (n b = 0 → occupationRate (mesh_pos hmesh) β (movedState m hn hmargin a b ha) m ≤ 1) ∧
    (∀ hb : 1 ≤ n b,
      |occupationRate (mesh_pos hmesh) β (movedState m hn hmargin a b ha) m -
        occupationRate (mesh_pos hmesh) β m (movedState m hn hmargin b a hb)| ≤
        1 + OccupationSecondDifferences.secondDifferenceConstant J β₀ / 4) := by
  dsimp only
  let m : OccupationState J N t := ⟨n, inner_cap_outer n hn⟩
  constructor
  · intro hb
    exact reverse_rate_le_one_of_zero (mesh_pos hmesh) (mesh_two_le hmesh)
      (OccupationSecondDifferences.secondDifferenceThreshold_bounds hlarge).1 hβ (hβ₀.trans_lt hsub)
      (show PermittedMove (mesh_pos hmesh) m (movedState m hn hmargin a b ha) a b from ⟨hab, ha, rfl⟩) hb
  · intro hb
    exact reverse_rate_comparison hβ hβ₀ hsub ht htC hmesh hlarge hmargin m hn a b hab ha hb

end PeriodicAttractiveLogGas.OccupationReverseRates
