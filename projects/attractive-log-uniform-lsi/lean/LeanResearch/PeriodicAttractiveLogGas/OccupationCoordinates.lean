import LeanResearch.PeriodicAttractiveLogGas.DiscreteOccupationIdentities

/-! The literal alternating-row mesh ordering and the integer cumulative
occupation coordinates of source 2057 onward. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationCoordinates
open MeshCells MeshAdjacentCells LabelOccupations DiscreteOccupationIdentities LabelRatioTransport

/-- Reverse the second coordinate in odd rows. -/
def snakeColumn {J : ℕ} (r c : Fin J) : Fin J :=
  if r.val % 2 = 0 then c else c.rev

@[simp] theorem snakeColumn_twice {J : ℕ} (r c : Fin J) :
    snakeColumn r (snakeColumn r c) = c := by
  unfold snakeColumn
  split <;> simp_all

/-- The actual mesh cell at row r and traversal-column c. -/
def snakePair {J : ℕ} (r c : Fin J) : MeshIndex J := ![r, snakeColumn r c]

@[simp] theorem snakePair_zero {J : ℕ} (r c : Fin J) : snakePair r c 0 = r := rfl
@[simp] theorem snakePair_one {J : ℕ} (r c : Fin J) :
    snakePair r c 1 = snakeColumn r c := rfl

/-- Every actual mesh cell occurs exactly once in the alternating rows. -/
def snakePairEquiv (J : ℕ) : (Fin J × Fin J) ≃ MeshIndex J where
  toFun p := snakePair p.1 p.2
  invFun a := (a 0, snakeColumn (a 0) (a 1))
  left_inv p := by simp
  right_inv a := by
    funext d
    fin_cases d <;> simp

/-- A nonwrapping coordinate increment is actual periodic mesh adjacency. -/
theorem edgeAdjacent_of_step {J : ℕ} (hJ : 0 < J) {a b : MeshIndex J}
    (d : Fin 2) (hd : (b d).val = (a d).val + 1)
    (ho : ∀ e, e ≠ d → b e = a e) : EdgeAdjacent J hJ a b := by
  refine ⟨d, Or.inl ?_⟩
  funext e
  by_cases he : e = d
  · subst e
    rw [nextCell_apply_same]
    apply Fin.ext
    have hl : (a d).val + 1 < J := by rw [← hd]; exact (b d).isLt
    simpa only [successorIndex, dite_eq_left hl] using hd
  · rw [nextCell_apply_of_ne J hJ a d e he]
    exact ho e he

/-- Consecutive traversal-columns are nearest-neighbor cells, in either row direction. -/
theorem snakePair_horizontal {J : ℕ} (hJ : 0 < J) (r c c' : Fin J)
    (hc : c'.val = c.val + 1) : EdgeAdjacent J hJ (snakePair r c) (snakePair r c') := by
  by_cases hr : r.val % 2 = 0
  · apply edgeAdjacent_of_step hJ (d := 1)
    · simpa only [snakePair_one, snakeColumn, ite_eq_left hr] using hc
    · intro e he
      fin_cases e
      · rfl
      · exact False.elim (he rfl)
  · apply EdgeAdjacent.symm
    apply edgeAdjacent_of_step hJ (d := 1)
    · simp only [snakePair_one, snakeColumn, ite_eq_right hr, Fin.val_rev]
      have hcl := c.isLt
      have hc'l := c'.isLt
      omega
    · intro e he
      fin_cases e
      · rfl
      · exact False.elim (he rfl)

/-- The last cell of a row and the first cell of the next row share a face. -/
theorem snakePair_vertical {J : ℕ} (hJ : 0 < J) (r r' : Fin J)
    (hr : r'.val = r.val + 1) :
    EdgeAdjacent J hJ (snakePair r ⟨J - 1, by omega⟩) (snakePair r' ⟨0, hJ⟩) := by
  apply edgeAdjacent_of_step hJ (d := 0)
  · exact hr
  · intro e he
    fin_cases e
    · exact False.elim (he rfl)
    · change snakeColumn r' ⟨0, hJ⟩ = snakeColumn r ⟨J - 1, by omega⟩
      unfold snakeColumn
      apply Fin.ext
      split <;> split <;> simp only [Fin.val_rev]
      all_goals omega

/-- Literal rank ordering of all J² mesh cells. -/
def squareFinEquiv (J : ℕ) : Fin (J ^ 2) ≃ Fin (J * J) where
  toFun i := ⟨i.val, by simpa only [pow_two] using i.isLt⟩
  invFun i := ⟨i.val, by simpa only [pow_two] using i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

def snakeOrder (J : ℕ) : Fin (J ^ 2) ≃ MeshIndex J :=
  (squareFinEquiv J).trans (finProdFinEquiv.symm.trans (snakePairEquiv J))

@[simp] theorem snakeOrder_pair {J : ℕ} (r c : Fin J) :
    snakeOrder J ⟨c.val + J * r.val, by
      have h := (finProdFinEquiv (r, c)).isLt
      change c.val + J * r.val < J * J at h
      simpa only [pow_two] using h⟩ = snakePair r c := by
  change snakePairEquiv J (finProdFinEquiv.symm (finProdFinEquiv (r, c))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Consecutive ranks use exactly a within-row edge or a row-end edge. -/
theorem snakeOrder_adjacent {J : ℕ} (hJ : 0 < J) (i j : Fin (J ^ 2))
    (hij : j.val = i.val + 1) : EdgeAdjacent J hJ (snakeOrder J i) (snakeOrder J j) := by
  obtain ⟨p, hp⟩ := finProdFinEquiv.surjective
    (⟨i.val, by simpa only [pow_two] using i.isLt⟩ : Fin (J * J))
  obtain ⟨q, hq⟩ := finProdFinEquiv.surjective
    (⟨j.val, by simpa only [pow_two] using j.isLt⟩ : Fin (J * J))
  obtain ⟨r, c⟩ := p
  obtain ⟨r', c'⟩ := q
  have hpi : c.val + J * r.val = i.val := congrArg Fin.val hp
  have hqj : c'.val + J * r'.val = j.val := congrArg Fin.val hq
  have he : c'.val + J * r'.val = c.val + J * r.val + 1 := by omega
  have hcl := c.isLt
  have hc'l := c'.isLt
  have hrr : r.val ≤ r'.val := by
    by_contra hn
    have hm := Nat.mul_le_mul_left J (show r'.val + 1 ≤ r.val by omega)
    nlinarith
  have hrr' : r'.val ≤ r.val + 1 := by
    by_contra hn
    have hm := Nat.mul_le_mul_left J (show r.val + 2 ≤ r'.val by omega)
    nlinarith
  have hi : snakeOrder J i = snakePair r c := by
    have h := snakeOrder_pair r c
    convert h using 1
    apply congrArg (snakeOrder J)
    exact Fin.ext hpi.symm
  have hj : snakeOrder J j = snakePair r' c' := by
    have h := snakeOrder_pair r' c'
    convert h using 1
    apply congrArg (snakeOrder J)
    exact Fin.ext hqj.symm
  rw [hi, hj]
  by_cases hr : r = r'
  · subst r'
    apply snakePair_horizontal hJ
    omega
  · have hr' : r'.val = r.val + 1 := by
      have hn : r.val ≠ r'.val := fun h => hr (Fin.ext h)
      omega
    have hlast : c.val = J - 1 := by rw [hr', Nat.mul_add, Nat.mul_one] at he; omega
    have hzero : c'.val = 0 := by rw [hr', Nat.mul_add, Nat.mul_one] at he; omega
    have ec : c = ⟨J - 1, by omega⟩ := Fin.ext hlast
    have ec' : c' = ⟨0, hJ⟩ := Fin.ext hzero
    simpa only [ec, ec'] using snakePair_vertical hJ r r' hr'

/-- Integer cumSum sum, retaining explicit endpoint coordinates. -/
def cumSum {M : ℕ} (f : Fin M → ℤ) (k : ℕ) : ℤ :=
  ∑ i, if i.val < k then f i else 0

@[simp] theorem prefix_zero {M : ℕ} (f : Fin M → ℤ) : cumSum f 0 = 0 := by
  simp [cumSum]

@[simp] theorem prefix_total {M : ℕ} (f : Fin M → ℤ) : cumSum f M = ∑ i, f i := by
  simp only [cumSum, Fin.isLt, ite_true]

theorem prefix_succ {M : ℕ} (f : Fin M → ℤ) (k : Fin M) :
    cumSum f (k.val + 1) = cumSum f k.val + f k := by
  classical
  have he (i : Fin M) : (if i.val < k.val + 1 then f i else 0) =
      (if i.val < k.val then f i else 0) + (if i = k then f k else 0) := by
    by_cases hik : i = k
    · subst i
      simp
    · have hn : i.val ≠ k.val := fun h => hik (Fin.ext h)
      by_cases hl : i.val < k.val
      · simp only [hl, show i.val < k.val + 1 by omega, ite_true, hik, ite_false, add_zero]
      · simp only [hl, show ¬ i.val < k.val + 1 by omega, ite_false, hik, add_zero]
  simp only [cumSum, he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The exact successive-difference identity. -/
theorem prefix_difference {M : ℕ} (f : Fin M → ℤ) (k : Fin M) :
    cumSum f (k.val + 1) - cumSum f k.val = f k := by
  rw [prefix_succ]
  ring

/-- Telescoping for every integer endpoint sequence. -/
theorem prefix_differences {M : ℕ} (y : Fin (M + 1) → ℤ) (k : ℕ) (hk : k ≤ M) :
    cumSum (fun i : Fin M => y i.succ - y i.castSucc) k = y ⟨k, by omega⟩ - y 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < M := by omega
    rw [prefix_succ _ (⟨k, hkm⟩ : Fin M)]
    rw [ih (by omega)]
    simp only [Fin.succ_mk, Fin.castSucc_mk]
    ring

/-- Cumulative coordinates of the actual occupation vector, including endpoints. -/
def cumulative {J : ℕ} (n : MeshIndex J → ℕ) (k : Fin (J ^ 2 + 1)) : ℤ :=
  cumSum (fun i => (n (snakeOrder J i) : ℤ)) k.val

@[simp] theorem cumulative_zero {J : ℕ} (n : MeshIndex J → ℕ) : cumulative n 0 = 0 :=
  prefix_zero _

theorem cumulative_difference {J : ℕ} (n : MeshIndex J → ℕ) (i : Fin (J ^ 2)) :
    cumulative n i.succ - cumulative n i.castSucc = (n (snakeOrder J i) : ℤ) :=
  prefix_difference _ i

theorem cumulative_total {J N : ℕ} (n : MeshIndex J → ℕ) (hn : ∑ a, n a = N) :
    cumulative n (Fin.last (J ^ 2)) = N := by
  change cumSum (fun i => (n (snakeOrder J i) : ℤ)) (J ^ 2) = N
  rw [prefix_total, (snakeOrder J).sum_comp (fun a => (n a : ℤ))]
  exact_mod_cast hn

theorem cumulative_injective (J : ℕ) : Function.Injective (@cumulative J) := by
  intro n m he
  funext a
  obtain ⟨i, rfl⟩ := (snakeOrder J).surjective a
  have hn := cumulative_difference n i
  have hm := cumulative_difference m i
  rw [he] at hn
  exact_mod_cast hn.symm.trans hm

/-- Exact integer endpoint domain; its free coordinates are the J²−1 interior slots. -/
def ValidCoordinates (J N : ℕ) (t : ℝ) (y : Fin (J ^ 2 + 1) → ℤ) : Prop :=
  y 0 = 0 ∧ y (Fin.last (J ^ 2)) = N ∧
    ∀ i : Fin (J ^ 2), 0 ≤ y i.succ - y i.castSucc ∧
      ((y i.succ - y i.castSucc : ℤ) : ℝ) ≤ t * N

abbrev CoordinateState (J N : ℕ) (t : ℝ) :=
  {y : Fin (J ^ 2 + 1) → ℤ // ValidCoordinates J N t y}

theorem cumulative_valid {J N : ℕ} {t : ℝ} (n : OccupationState J N t) :
    ValidCoordinates J N t (cumulative n.val) := by
  refine ⟨cumulative_zero _, cumulative_total _ n.property.1, ?_⟩
  intro i
  rw [cumulative_difference]
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast n.property.2 (snakeOrder J i)⟩

/-- The original nonnegative occupation counts are successive integer differences. -/
def recover {J : ℕ} (y : Fin (J ^ 2 + 1) → ℤ) (a : MeshIndex J) : ℕ :=
  (y ((snakeOrder J).symm a).succ - y ((snakeOrder J).symm a).castSucc).toNat

@[simp] theorem recover_cumulative {J : ℕ} (n : MeshIndex J → ℕ) :
    recover (cumulative n) = n := by
  funext a
  simp only [recover, cumulative_difference, Equiv.apply_symm_apply, Int.toNat_natCast]

theorem recover_cast {J N : ℕ} {t : ℝ} (y : CoordinateState J N t) (i : Fin (J ^ 2)) :
    (recover y.val (snakeOrder J i) : ℤ) = y.val i.succ - y.val i.castSucc := by
  simp only [recover, Equiv.symm_apply_apply]
  exact Int.toNat_of_nonneg (y.property.2.2 i).1

theorem cumulative_recover {J N : ℕ} {t : ℝ} (y : CoordinateState J N t) :
    cumulative (recover y.val) = y.val := by
  funext k
  unfold cumulative
  simp_rw [recover_cast y]
  rw [prefix_differences _ k.val (by have := k.isLt; omega), y.property.1, sub_zero]

theorem recover_sum {J N : ℕ} {t : ℝ} (y : CoordinateState J N t) :
    (∑ a, recover y.val a) = N := by
  have hh := congrFun (cumulative_recover y) (Fin.last (J ^ 2))
  change cumSum (fun i => (recover y.val (snakeOrder J i) : ℤ)) (J ^ 2) = _ at hh
  rw [prefix_total, (snakeOrder J).sum_comp (fun a => (recover y.val a : ℤ)), y.property.2.1] at hh
  exact_mod_cast hh

theorem recover_capped {J N : ℕ} {t : ℝ} (y : CoordinateState J N t) :
    recover y.val ∈ cappedOccupations J N t := by
  refine ⟨recover_sum y, ?_⟩
  intro a
  obtain ⟨i, rfl⟩ := (snakeOrder J).surjective a
  have hc := (y.property.2.2 i).2
  rw [← recover_cast y i] at hc
  exact_mod_cast hc

/-- Actual capped occupation vectors and the explicit finite integer domain are bijective. -/
def coordinateEquiv (J N : ℕ) (t : ℝ) : OccupationState J N t ≃ CoordinateState J N t where
  toFun n := ⟨cumulative n.val, cumulative_valid n⟩
  invFun y := ⟨recover y.val, recover_capped y⟩
  left_inv n := Subtype.ext (recover_cumulative n.val)
  right_inv y := Subtype.ext (cumulative_recover y)

noncomputable instance (J N : ℕ) (t : ℝ) : Fintype (CoordinateState J N t) :=
  Fintype.ofEquiv (OccupationState J N t) (coordinateEquiv J N t)

/-- Every actual integer coordinate lies between the fixed endpoints. -/
theorem cumulative_bounds {J N : ℕ} (n : MeshIndex J → ℕ) (hn : ∑ a, n a = N)
    (k : Fin (J ^ 2 + 1)) : 0 ≤ cumulative n k ∧ cumulative n k ≤ N := by
  constructor
  · unfold cumulative cumSum
    apply Finset.sum_nonneg
    intro i _
    split <;> positivity
  · have hh : cumulative n k ≤ ∑ i : Fin (J ^ 2), (n (snakeOrder J i) : ℤ) := by
      unfold cumulative cumSum
      apply Finset.sum_le_sum
      intro i _
      split
      · exact le_rfl
      · exact Int.natCast_nonneg _
    rw [(snakeOrder J).sum_comp (fun a => (n a : ℤ))] at hh
    have he : (∑ a, (n a : ℤ)) = N := by exact_mod_cast hn
    rwa [he] at hh

/-- A literal occupation move has the expected integer-valued difference even at zero targets. -/
theorem move_cast {J : ℕ} (n : MeshIndex J → ℕ) (a b c : MeshIndex J)
    (ha : 1 ≤ n a) : (moveOccupation n a b c : ℤ) =
      (n c : ℤ) - (if a = c then 1 else 0) + (if b = c then 1 else 0) := by
  unfold moveOccupation
  by_cases hac : a = c
  · subst c
    by_cases hba : b = a <;> simp only [ite_true, hba, ite_false]
    all_goals omega
  · by_cases hbc : b = c <;> simp only [hac, hbc, ite_false, ite_true, Nat.sub_zero]
    all_goals omega

/-- Prefix change under the actual move n−e_a+e_b. -/
theorem cumulative_move {J : ℕ} (n : MeshIndex J → ℕ) (a b : MeshIndex J)
    (ha : 1 ≤ n a) (k : Fin (J ^ 2 + 1)) :
    cumulative (moveOccupation n a b) k = cumulative n k -
      (if ((snakeOrder J).symm a).val < k.val then 1 else 0) +
      (if ((snakeOrder J).symm b).val < k.val then 1 else 0) := by
  classical
  let ia := (snakeOrder J).symm a
  let ib := (snakeOrder J).symm b
  have he (i : Fin (J ^ 2)) :
      (if i.val < k.val then (moveOccupation n a b (snakeOrder J i) : ℤ) else 0) =
      (if i.val < k.val then (n (snakeOrder J i) : ℤ) else 0) -
        (if i = ia then (if ia.val < k.val then 1 else 0) else 0) +
        (if i = ib then (if ib.val < k.val then 1 else 0) else 0) := by
    rw [move_cast n a b _ ha]
    have hia : a = snakeOrder J i ↔ i = ia := by
      dsimp [ia]
      constructor
      · intro h; rw [h, Equiv.symm_apply_apply]
      · intro h; rw [h, Equiv.apply_symm_apply]
    have hib : b = snakeOrder J i ↔ i = ib := by
      dsimp [ib]
      constructor
      · intro h; rw [h, Equiv.symm_apply_apply]
      · intro h; rw [h, Equiv.apply_symm_apply]
    simp only [hia, hib]
    by_cases hai : i = ia <;> by_cases hbi : i = ib <;>
      by_cases hk : i.val < k.val <;> simp_all
    all_goals simp [not_lt.mpr hk]
  unfold cumulative cumSum
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ia, ib]

/-- Every permitted move changes each integer coordinate by at most one. -/
theorem cumulative_move_abs_le_one {J : ℕ} (n : MeshIndex J → ℕ) (a b : MeshIndex J)
    (ha : 1 ≤ n a) (k : Fin (J ^ 2 + 1)) :
    |cumulative (moveOccupation n a b) k - cumulative n k| ≤ 1 := by
  rw [cumulative_move n a b ha]
  rw [abs_le]
  split <;> split <;> constructor <;> omega

/-- Along a chosen path edge, exactly its intervening coordinate decreases by one. -/
theorem cumulative_path_move {J : ℕ} (n : MeshIndex J → ℕ) (i j : Fin (J ^ 2))
    (hij : j.val = i.val + 1) (ha : 1 ≤ n (snakeOrder J i)) (k : Fin (J ^ 2 + 1)) :
    cumulative (moveOccupation n (snakeOrder J i) (snakeOrder J j)) k =
      cumulative n k - (if k.val = i.val + 1 then 1 else 0) := by
  rw [cumulative_move _ _ _ ha]
  simp only [Equiv.symm_apply_apply]
  split <;> split <;> split <;> omega

/-- The reverse path move increases that one coordinate. -/
theorem cumulative_path_move_reverse {J : ℕ} (n : MeshIndex J → ℕ) (i j : Fin (J ^ 2))
    (hij : j.val = i.val + 1) (hb : 1 ≤ n (snakeOrder J j)) (k : Fin (J ^ 2 + 1)) :
    cumulative (moveOccupation n (snakeOrder J j) (snakeOrder J i)) k =
      cumulative n k + (if k.val = i.val + 1 then 1 else 0) := by
  rw [cumulative_move _ _ _ hb]
  simp only [Equiv.symm_apply_apply]
  split <;> split <;> split <;> omega

/-- Fixed-dimensional sup-norm comparison, stated first coordinatewise. -/
theorem cumulative_difference_bound {J : ℕ} (n m : MeshIndex J → ℕ) {R : ℝ}
    (hR : 0 ≤ R) (h : ∀ a, |(n a : ℝ) - m a| ≤ R) (k : Fin (J ^ 2 + 1)) :
    |((cumulative n k - cumulative m k : ℤ) : ℝ)| ≤ (J ^ 2 : ℕ) * R := by
  have he : ((cumulative n k - cumulative m k : ℤ) : ℝ) =
      ∑ i : Fin (J ^ 2), if i.val < k.val then (n (snakeOrder J i) : ℝ) - m (snakeOrder J i) else 0 := by
    simp only [cumulative, cumSum, Int.cast_sub, Int.cast_sum, Int.cast_ite,
      Int.cast_natCast, Int.cast_zero, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin (J ^ 2), |if i.val < k.val then (n (snakeOrder J i) : ℝ) - m (snakeOrder J i) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin (J ^ 2), R := by
      apply Finset.sum_le_sum
      intro i _
      split
      · exact h _
      · simpa only [abs_zero] using hR
    _ = _ := by simp

/-- Difference reconstruction gives the reverse factor two, uniformly in N. -/
theorem count_difference_bound {J : ℕ} (n m : MeshIndex J → ℕ) {R : ℝ}
    (h : ∀ k, |((cumulative n k - cumulative m k : ℤ) : ℝ)| ≤ R) (a : MeshIndex J) :
    |(n a : ℝ) - m a| ≤ 2 * R := by
  obtain ⟨i, rfl⟩ := (snakeOrder J).surjective a
  have hn := cumulative_difference n i
  have hm := cumulative_difference m i
  have he : (n (snakeOrder J i) : ℝ) - m (snakeOrder J i) =
      ((cumulative n i.succ - cumulative m i.succ : ℤ) : ℝ) -
        ((cumulative n i.castSucc - cumulative m i.castSucc : ℤ) : ℝ) := by
    have hn' : ((cumulative n i.succ : ℤ) : ℝ) - cumulative n i.castSucc = n (snakeOrder J i) := by exact_mod_cast hn
    have hm' : ((cumulative m i.succ : ℤ) : ℝ) - cumulative m i.castSucc = m (snakeOrder J i) := by exact_mod_cast hm
    push_cast
    linarith only [hn', hm']
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [h i.succ, h i.castSucc])

/-- Exactly the D=J²−1 free integer coordinates from the manuscript. -/
abbrev Interior (J : ℕ) := Fin (J ^ 2 - 1) → ℤ

def interior {J : ℕ} (y : Fin (J ^ 2 + 1) → ℤ) : Interior J :=
  fun k => y ⟨k.val + 1, by have := k.isLt; omega⟩

/-- Restore the prescribed endpoint values to the free coordinates. -/
def extend (J N : ℕ) (y : Interior J) (k : Fin (J ^ 2 + 1)) : ℤ :=
  if h0 : k.val = 0 then 0 else
    if h : k.val < J ^ 2 then y ⟨k.val - 1, by have := k.isLt; omega⟩ else N

@[simp] theorem extend_zero {J N : ℕ} (y : Interior J) : extend J N y 0 = 0 := by
  simp [extend]

@[simp] theorem extend_last {J N : ℕ} (hJ : 0 < J) (y : Interior J) :
    extend J N y (Fin.last (J ^ 2)) = N := by
  simp [extend, hJ.ne']

@[simp] theorem interior_extend {J N : ℕ} (y : Interior J) :
    interior (extend J N y) = y := by
  funext i
  have hi := i.isLt
  have hl : i.val + 1 < J ^ 2 := by omega
  simp [interior, extend, hl]

/-- No interior information is lost by adding and removing the endpoints. -/
theorem extend_interior {J N : ℕ} (y : Fin (J ^ 2 + 1) → ℤ)
    (h0 : y 0 = 0) (hN : y (Fin.last (J ^ 2)) = N) :
    extend J N (interior y) = y := by
  funext k
  unfold extend
  split
  · rename_i hk
    have he : k = 0 := Fin.ext hk
    simpa only [he] using h0.symm
  · rename_i hk
    split
    · rename_i hl
      unfold interior
      congr 1
      apply Fin.ext
      simp only
      omega
    · rename_i hl
      have he : k = Fin.last (J ^ 2) := Fin.ext (by have := k.isLt; change k.val = J ^ 2; omega)
      simpa only [he] using hN.symm

abbrev InteriorState (J N : ℕ) (t : ℝ) :=
  {y : Interior J // ValidCoordinates J N t (extend J N y)}

def interiorEquiv (J N : ℕ) (t : ℝ) : CoordinateState J N t ≃ InteriorState J N t where
  toFun y := ⟨interior y.val, by rw [extend_interior _ y.property.1 y.property.2.1]; exact y.property⟩
  invFun y := ⟨extend J N y.val, y.property⟩
  left_inv y := Subtype.ext (extend_interior _ y.property.1 y.property.2.1)
  right_inv y := Subtype.ext (interior_extend y.val)

/-- The actual occupation correspondence in the literal J²−1-dimensional integer space. -/
def occupationInteriorEquiv (J N : ℕ) (t : ℝ) : OccupationState J N t ≃ InteriorState J N t :=
  (coordinateEquiv J N t).trans (interiorEquiv J N t)

noncomputable instance (J N : ℕ) (t : ℝ) : Fintype (InteriorState J N t) :=
  Fintype.ofEquiv (OccupationState J N t) (occupationInteriorEquiv J N t)

/-- Interior closeness extends to the fixed endpoints, which differ by zero. -/
theorem extend_close {J N : ℕ} (y z : Interior J) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ i, |((y i - z i : ℤ) : ℝ)| ≤ R) (k : Fin (J ^ 2 + 1)) :
    |((extend J N y k - extend J N z k : ℤ) : ℝ)| ≤ R := by
  unfold extend
  split
  · simpa using hR
  · split
    · exact h _
    · simpa using hR

/-- Sup-norm forward comparison with a constant depending only on J. -/
theorem cumulative_norm_le {J : ℕ} (n m : MeshIndex J → ℕ) :
    ‖fun k => ((cumulative n k - cumulative m k : ℤ) : ℝ)‖ ≤
      (J ^ 2 : ℕ) * ‖fun a => (n a : ℝ) - m a‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  rw [Real.norm_eq_abs]
  apply cumulative_difference_bound n m (norm_nonneg _)
  intro a
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun a => (n a : ℝ) - m a) a

theorem count_norm_le {J : ℕ} (n m : MeshIndex J → ℕ) :
    ‖fun a => (n a : ℝ) - m a‖ ≤
      2 * ‖fun k => ((cumulative n k - cumulative m k : ℤ) : ℝ)‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  rw [Real.norm_eq_abs]
  apply count_difference_bound n m
  intro k
  simpa only [Real.norm_eq_abs] using
    norm_le_pi_norm (fun k => ((cumulative n k - cumulative m k : ℤ) : ℝ)) k

/-- Counting initial ranks, proved by the same exact prefix increment identity. -/
theorem prefix_ones (M k : ℕ) (hk : k ≤ M) :
    cumSum (fun _ : Fin M => (1 : ℤ)) k = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hl : k < M := by omega
    rw [prefix_succ _ (⟨k, hl⟩ : Fin M), ih (by omega)]
    simp

/-- The actual rounded near-uniform center, with extra particles on initial snake ranks. -/
def rounded (J N : ℕ) (a : MeshIndex J) : ℕ :=
  N / (J ^ 2) + if ((snakeOrder J).symm a).val < N % (J ^ 2) then 1 else 0

theorem rounded_sum {J : ℕ} (hJ : 0 < J) (N : ℕ) : ∑ a, rounded J N a = N := by
  classical
  have hM : 0 < J ^ 2 := pow_pos hJ _
  have hc : (∑ i : Fin (J ^ 2), if i.val < N % (J ^ 2) then (1 : ℕ) else 0) = N % (J ^ 2) := by
    have hh := prefix_ones (J ^ 2) (N % (J ^ 2)) (Nat.mod_lt N hM).le
    change (∑ i : Fin (J ^ 2), if i.val < N % (J ^ 2) then (1 : ℤ) else 0) = (N % (J ^ 2) : ℕ) at hh
    exact_mod_cast hh
  rw [← (snakeOrder J).sum_comp (rounded J N)]
  simp only [rounded, Equiv.symm_apply_apply, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
  exact Nat.div_add_mod N (J ^ 2)

/-- Every rounded count differs from the exact average by at most one. -/
theorem rounded_close {J : ℕ} (hJ : 0 < J) (N : ℕ) (a : MeshIndex J) :
    |(rounded J N a : ℝ) - (N : ℝ) / (J ^ 2 : ℕ)| ≤ 1 := by
  have hM : (0 : ℝ) < (J ^ 2 : ℕ) := by exact_mod_cast pow_pos hJ 2
  have hr : ((N % (J ^ 2) : ℕ) : ℝ) < (J ^ 2 : ℕ) := by exact_mod_cast Nat.mod_lt N (pow_pos hJ 2)
  have hq : ((J ^ 2 : ℕ) : ℝ) * (N / (J ^ 2) : ℕ) + (N % (J ^ 2) : ℕ) = N := by
    exact_mod_cast Nat.div_add_mod N (J ^ 2)
  have hlo : (N / (J ^ 2) : ℕ) ≤ (N : ℝ) / (J ^ 2 : ℕ) := by
    apply (le_div_iff₀ hM).mpr
    have hz : (0 : ℝ) ≤ (N % (J ^ 2) : ℕ) := Nat.cast_nonneg _
    nlinarith only [hq, hz]
  have hhi : (N : ℝ) / (J ^ 2 : ℕ) < (N / (J ^ 2) : ℕ) + 1 := by
    apply (div_lt_iff₀ hM).mpr
    nlinarith only [hq, hr]
  simp only [Nat.cast_pow] at hlo hhi
  unfold rounded
  split <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- Chosen once for each mesh, independently of particle number and inverse temperature. -/
def centralEpsilon (J : ℕ) : ℝ := 1 / (32 * (J ^ 2 : ℕ))

theorem centralEpsilon_pos {J : ℕ} (hJ : 0 < J) : 0 < centralEpsilon J := by
  unfold centralEpsilon
  have hM : (0 : ℝ) < (J ^ 2 : ℕ) := by exact_mod_cast pow_pos hJ 2
  positivity

/-- Successive differences change by at most twice the endpoint sup distance. -/
theorem endpoint_difference_bound {M : ℕ} (y z : Fin (M + 1) → ℤ) {R : ℝ}
    (h : ∀ k, |((y k - z k : ℤ) : ℝ)| ≤ R) (i : Fin M) :
    |((y i.succ - y i.castSucc : ℤ) : ℝ) - ((z i.succ - z i.castSucc : ℤ) : ℝ)| ≤ 2 * R := by
  have he : ((y i.succ - y i.castSucc : ℤ) : ℝ) - ((z i.succ - z i.castSucc : ℤ) : ℝ) =
      ((y i.succ - z i.succ : ℤ) : ℝ) - ((y i.castSucc - z i.castSucc : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [h i.succ, h i.castSucc])

/-- Every integer point of the free-coordinate box is valid when the actual
baseline counts have the displayed margins. This is proved, not a box premise. -/
theorem box_valid_of_margins {J N : ℕ} {t R : ℝ} (hJ : 0 < J)
    (n : MeshIndex J → ℕ) (hn : ∑ a, n a = N) (y : Interior J) (hR : 0 ≤ R)
    (hy : ∀ i, |((y i - interior (cumulative n) i : ℤ) : ℝ)| ≤ R)
    (hl : ∀ a, 2 * R ≤ (n a : ℝ)) (hu : ∀ a, (n a : ℝ) + 2 * R ≤ t * N) :
    ValidCoordinates J N t (extend J N y) := by
  have he := extend_interior (cumulative n) (cumulative_zero n) (cumulative_total n hn)
  have hc (k) := extend_close (N := N) y (interior (cumulative n)) hR hy k
  rw [he] at hc
  refine ⟨extend_zero y, extend_last hJ y, ?_⟩
  intro i
  have hd := endpoint_difference_bound (extend J N y) (cumulative n) hc i
  rw [cumulative_difference] at hd
  have hd' : |((extend J N y i.succ - extend J N y i.castSucc : ℤ) : ℝ) - (n (snakeOrder J i) : ℝ)| ≤ 2 * R := by
    exact_mod_cast hd
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd'
  constructor
  · have hz : (0 : ℝ) ≤ ((extend J N y i.succ - extend J N y i.castSucc : ℤ) : ℝ) := by
      linarith only [hl (snakeOrder J i), hdlo]
    exact_mod_cast hz
  · linarith only [hu (snakeOrder J i), hdhi]

/-- The same reconstruction gives the actual count error on every valid box point. -/
theorem box_count_error {J N : ℕ} {t R : ℝ} (n : MeshIndex J → ℕ)
    (hn : ∑ a, n a = N) (y : Interior J) (hv : ValidCoordinates J N t (extend J N y))
    (hR : 0 ≤ R) (hy : ∀ i, |((y i - interior (cumulative n) i : ℤ) : ℝ)| ≤ R)
    (a : MeshIndex J) : |(recover (extend J N y) a : ℝ) - n a| ≤ 2 * R := by
  have he := extend_interior (cumulative n) (cumulative_zero n) (cumulative_total n hn)
  have hc (k) := extend_close (N := N) y (interior (cumulative n)) hR hy k
  rw [he] at hc
  obtain ⟨i, rfl⟩ := (snakeOrder J).surjective a
  have hd := endpoint_difference_bound (extend J N y) (cumulative n) hc i
  rw [cumulative_difference, ← recover_cast (⟨extend J N y, hv⟩ : CoordinateState J N t) i] at hd
  exact_mod_cast hd

/-- The explicit epsilon and particle threshold give all source central count margins. -/
theorem rounded_central_margins {J N : ℕ} {t : ℝ} (hJ : 0 < J)
    (hN : 8 * J ^ 2 ≤ N) (ht : 1 / (J ^ 2 : ℕ) < t / 8) (a : MeshIndex J) :
    (N : ℝ) / (2 * (J ^ 2 : ℕ)) ≤ (rounded J N a : ℝ) - 2 * (2 * centralEpsilon J * N) ∧
    (rounded J N a : ℝ) + 2 * (2 * centralEpsilon J * N) ≤ (t / 2) * N := by
  have hM : (0 : ℝ) < (J ^ 2 : ℕ) := by exact_mod_cast pow_pos hJ 2
  let u : ℝ := (N : ℝ) / (J ^ 2 : ℕ)
  have hu : 8 ≤ u := by
    apply (le_div_iff₀ hM).mpr
    exact_mod_cast hN
  have hr := abs_le.mp (rounded_close hJ N a)
  have he : 2 * (2 * centralEpsilon J * N) = u / 8 := by
    dsimp [centralEpsilon, u]
    field_simp
    ring
  have hhalf : (N : ℝ) / (2 * (J ^ 2 : ℕ)) = u / 2 := by
    dsimp [u]
    field_simp
  have ht' := mul_le_mul_of_nonneg_right ht.le (show (0 : ℝ) ≤ 4 * N by positivity)
  have ht'' : 4 * u ≤ (t / 2) * N := by
    dsimp only [u]
    convert ht' using 1 <;> ring
  change -1 ≤ (rounded J N a : ℝ) - u ∧ (rounded J N a : ℝ) - u ≤ 1 at hr
  rw [he, hhalf]
  constructor <;> linarith only [hr.1, hr.2, hu, ht'']

/-- The actual complete integer cube around the constructed rounded center lies
in S_(t/2), and every reconstructed count is at least N/(2J²). -/
theorem central_box {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 8 * J ^ 2 ≤ N)
    (ht : 1 / (J ^ 2 : ℕ) < t / 8) (y : Interior J)
    (hy : ∀ i, |((y i - interior (cumulative (rounded J N)) i : ℤ) : ℝ)| ≤
      2 * centralEpsilon J * N) :
    ValidCoordinates J N (t / 2) (extend J N y) ∧
      ∀ a, (N : ℝ) / (2 * (J ^ 2 : ℕ)) ≤ (recover (extend J N y) a : ℝ) := by
  have hε := centralEpsilon_pos hJ
  have hR : 0 ≤ 2 * centralEpsilon J * N := by positivity
  have hn := rounded_sum hJ N
  have hm := rounded_central_margins hJ hN ht
  have hlo (a) : 2 * (2 * centralEpsilon J * N) ≤ (rounded J N a : ℝ) := by
    have hh := (hm a).1
    have hz : (0 : ℝ) ≤ (N : ℝ) / (2 * (J ^ 2 : ℕ)) := by positivity
    linarith only [hh, hz]
  have hv := box_valid_of_margins hJ (rounded J N) hn y hR hy hlo (fun a => (hm a).2)
  refine ⟨hv, ?_⟩
  intro a
  have he := box_count_error (rounded J N) hn y hv hR hy a
  have hh := (hm a).1
  obtain ⟨he0, he1⟩ := abs_le.mp he
  linarith only [he0, hh]

theorem dimension_pos {J : ℕ} (hJ : 2 ≤ J) : 1 ≤ J ^ 2 - 1 := by
  have hh : 4 ≤ J ^ 2 := by nlinarith
  omega

/-- The forward norm bound in the literal free-coordinate space. -/
theorem interior_norm_le {J : ℕ} (n m : MeshIndex J → ℕ) :
    ‖fun i => ((interior (cumulative n) i - interior (cumulative m) i : ℤ) : ℝ)‖ ≤
      (J ^ 2 : ℕ) * ‖fun a => (n a : ℝ) - m a‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  apply cumulative_difference_bound n m (norm_nonneg _)
  intro a
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun a => (n a : ℝ) - m a) a

/-- The inverse norm bound uses the actual shared total mass, hence identical endpoints. -/
theorem count_norm_le_interior {J N : ℕ} (n m : MeshIndex J → ℕ)
    (hn : ∑ a, n a = N) (hm : ∑ a, m a = N) :
    ‖fun a => (n a : ℝ) - m a‖ ≤
      2 * ‖fun i => ((interior (cumulative n) i - interior (cumulative m) i : ℤ) : ℝ)‖ := by
  let R := ‖fun i => ((interior (cumulative n) i - interior (cumulative m) i : ℤ) : ℝ)‖
  have hclose (i) : |((interior (cumulative n) i - interior (cumulative m) i : ℤ) : ℝ)| ≤ R := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm
      (fun i => ((interior (cumulative n) i - interior (cumulative m) i : ℤ) : ℝ)) i
  have hfull (k) := extend_close (N := N) (interior (cumulative n)) (interior (cumulative m))
    (norm_nonneg _) hclose k
  rw [extend_interior _ (cumulative_zero n) (cumulative_total n hn),
    extend_interior _ (cumulative_zero m) (cumulative_total m hm)] at hfull
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  rw [Real.norm_eq_abs]
  exact count_difference_bound n m hfull a

/-- The constructed center is an actual capped occupation, under the original source gates. -/
theorem rounded_capped {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 8 * J ^ 2 ≤ N)
    (ht : 1 / (J ^ 2 : ℕ) < t / 8) : rounded J N ∈ cappedOccupations J N (t / 2) := by
  refine ⟨rounded_sum hJ N, ?_⟩
  intro a
  have hh := (rounded_central_margins hJ hN ht a).2
  have hε := centralEpsilon_pos hJ
  have hz : 0 ≤ 2 * (2 * centralEpsilon J * N) := by positivity
  linarith only [hh, hz]

/-- Actual occupation statement for the full integer cube, including count lower bounds and inverse. -/
theorem central_box_occupation {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 8 * J ^ 2 ≤ N)
    (ht : 1 / (J ^ 2 : ℕ) < t / 8) (y : Interior J)
    (hy : ∀ i, |((y i - interior (cumulative (rounded J N)) i : ℤ) : ℝ)| ≤ 2 * centralEpsilon J * N) :
    recover (extend J N y) ∈ cappedOccupations J N (t / 2) ∧
      interior (cumulative (recover (extend J N y))) = y ∧
      ∀ a, (N : ℝ) / (2 * (J ^ 2 : ℕ)) ≤ (recover (extend J N y) a : ℝ) := by
  have hh := central_box hJ hN ht y hy
  let z : CoordinateState J N (t / 2) := ⟨extend J N y, hh.1⟩
  refine ⟨recover_capped z, ?_, hh.2⟩
  rw [cumulative_recover z]
  exact interior_extend y

/-- Extending a coordinate decrement preserves exactly that one interior displacement. -/
theorem extend_step {J N : ℕ} (y : Interior J) (i : Fin (J ^ 2 - 1)) (k : Fin (J ^ 2 + 1)) :
    extend J N (fun l => y l - if l = i then 1 else 0) k =
      extend J N y k - (if k.val = i.val + 1 then 1 else 0) := by
  have hi := i.isLt
  unfold extend
  split
  · rename_i hk
    have hn : k.val ≠ i.val + 1 := by omega
    simp only [hn, ite_false, sub_zero]
  · rename_i hk
    split
    · rename_i hl
      have he : (⟨k.val - 1, by omega⟩ : Fin (J ^ 2 - 1)) = i ↔ k.val = i.val + 1 := by
        constructor
        · intro he
          have hv := congrArg Fin.val he
          change k.val - 1 = i.val at hv
          omega
        · intro he; apply Fin.ext; simp only; omega
      simp only [he]
    · rename_i hl
      have hn : k.val ≠ i.val + 1 := by omega
      simp only [hn, ite_false, sub_zero]

/-- A genuine free-coordinate neighbor in the occupation domain is an actual
permitted snake-path move. Source positivity is derived from the target counts. -/
theorem interior_neighbor_is_permitted {J N : ℕ} {t : ℝ} (hJ : 0 < J)
    (n m : OccupationState J N t) (i : Fin (J ^ 2 - 1))
    (h : interior (cumulative m.val) = fun l => interior (cumulative n.val) l - if l = i then 1 else 0) :
    PermittedMove hJ n m (snakeOrder J ⟨i.val, by have := i.isLt; omega⟩)
      (snakeOrder J ⟨i.val + 1, by have := i.isLt; omega⟩) := by
  let a : Fin (J ^ 2) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (J ^ 2) := ⟨i.val + 1, by have := i.isLt; omega⟩
  have heN := extend_interior (cumulative n.val) (cumulative_zero _) (cumulative_total _ n.property.1)
  have heM := extend_interior (cumulative m.val) (cumulative_zero _) (cumulative_total _ m.property.1)
  have hfull (k) : cumulative m.val k = cumulative n.val k - (if k.val = i.val + 1 then 1 else 0) := by
    rw [← heM, h, extend_step, heN]
  have hm := cumulative_difference m.val a
  rw [hfull, hfull] at hm
  have hn := cumulative_difference n.val a
  have hprev : a.castSucc.val ≠ i.val + 1 := by dsimp [a]; omega
  have hnext : a.succ.val = i.val + 1 := rfl
  simp only [hprev, hnext, ite_true, ite_false, sub_zero] at hm
  have ha : 1 ≤ n.val (snakeOrder J a) := by omega
  refine ⟨snakeOrder_adjacent hJ a b rfl, ha, ?_⟩
  apply cumulative_injective J
  funext k
  rw [cumulative_path_move _ a b rfl ha, hfull]

end PeriodicAttractiveLogGas.OccupationCoordinates
