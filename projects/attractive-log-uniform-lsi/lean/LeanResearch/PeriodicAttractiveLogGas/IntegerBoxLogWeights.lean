import LeanResearch.PeriodicAttractiveLogGas.FiniteBoxLogSobolev

/-! Literal integer boxes, coordinate paths and normalized log-weight comparison
for source2130–2242. No shell partition or localization theorem is assumed. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.IntegerBoxLogWeights
open FiniteBoxLogSobolev FibreEntropy

/-- Literal closed integer cube, including singleton sides and empty products. -/
def integerBox {D : ℕ} (lower : Fin D → ℤ) (n : ℕ) : Set (Fin D → ℤ) :=
  {z | ∀ i, lower i ≤ z i ∧ z i ≤ lower i + n}

def chart {D n : ℕ} (lower : Fin D → ℤ) (x : Box D n) : Fin D → ℤ :=
  fun i => lower i + (x i).val

theorem chart_mem {D n : ℕ} (lower : Fin D → ℤ) (x : Box D n) :
    chart lower x ∈ integerBox lower n := by
  intro i
  have hi := (x i).isLt
  change lower i ≤ lower i + (x i).val ∧ lower i + (x i).val ≤ lower i + n
  constructor <;> omega

/-- The actual affine chart is onto the whole closed integer cube. -/
def chartEquiv {D n : ℕ} (lower : Fin D → ℤ) : Box D n ≃ ↥(integerBox lower n) where
  toFun x := ⟨chart lower x, chart_mem lower x⟩
  invFun z i := ⟨(z.val i - lower i).toNat, by have hi := z.property i; omega⟩
  left_inv x := by
    funext i
    apply Fin.ext
    simp only [chart, add_sub_cancel_left, Int.toNat_natCast]
  right_inv z := by
    apply Subtype.ext
    funext i
    have hi := z.property i
    change lower i + ((z.val i - lower i).toNat : ℤ) = z.val i
    omega

/-- The literal number of unit coordinate moves needed between two box points. -/
def gridDistance {D n : ℕ} (x y : Box D n) : ℕ :=
  ∑ i, ((y i).val - (x i).val + ((x i).val - (y i).val))

theorem gridDistance_le {D n : ℕ} (x y : Box D n) : gridDistance x y ≤ D * n := by
  have hh (i : Fin D) : (y i).val - (x i).val + ((x i).val - (y i).val) ≤ n := by
    have hx := (x i).isLt
    have hy := (y i).isLt
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simpa only [gridDistance, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hs

theorem gridDistance_eq_zero {D n : ℕ} {x y : Box D n} (h : gridDistance x y = 0) : x = y := by
  funext i
  apply Fin.ext
  have hi := Finset.single_le_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin D))) =>
    Nat.zero_le ((y j).val - (x j).val + ((x j).val - (y j).val))) (Finset.mem_univ i)
  change (y i).val - (x i).val + ((x i).val - (y i).val) ≤ gridDistance x y at hi
  omega

/-- A genuine forward or reverse coordinate edge; no stationary step is included. -/
def UnitStep {D n : ℕ} (x y : Box D n) : Prop :=
  ∃ i : Fin D, (∀ j, j ≠ i → x j = y j) ∧
    ((x i).val + 1 = (y i).val ∨ (y i).val + 1 = (x i).val)

theorem UnitStep.symm {D n : ℕ} {x y : Box D n} (h : UnitStep x y) : UnitStep y x := by
  obtain ⟨i, hi, hs⟩ := h
  exact ⟨i, fun j hj => (hi j hj).symm, hs.symm⟩

theorem distance_update {D n : ℕ} (x y : Box D n) (i : Fin D) (u : Fin (n + 1)) :
    gridDistance (Function.update x i u) y + ((y i).val - (x i).val + ((x i).val - (y i).val)) =
      gridDistance x y + ((y i).val - u.val + (u.val - (y i).val)) := by
  classical
  unfold gridDistance
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ (fun j => (y j).val - (x j).val + ((x j).val - (y j).val)) (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i,
      ((y j).val - (Function.update x i u j).val + ((Function.update x i u j).val - (y j).val))) =
      ∑ j ∈ Finset.univ.erase i, ((y j).val - (x j).val + ((x j).val - (y j).val)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, Function.update_self]
  omega

/-- Construct one coordinate step toward the target, inside the actual box. -/
theorem step_toward {D n : ℕ} (x y : Box D n) (hxy : x ≠ y) :
    ∃ z : Box D n, UnitStep x z ∧ gridDistance z y + 1 = gridDistance x y := by
  classical
  have hi : ∃ i, x i ≠ y i := by
    by_contra hn
    apply hxy
    funext i
    by_contra h
    exact hn ⟨i, h⟩
  obtain ⟨i, hi⟩ := hi
  have hiv : (x i).val ≠ (y i).val := fun h => hi (Fin.ext h)
  by_cases hlt : (x i).val < (y i).val
  · let u : Fin (n + 1) := ⟨(x i).val + 1, by have hy := (y i).isLt; omega⟩
    refine ⟨Function.update x i u, ⟨i, ?_, ?_⟩, ?_⟩
    · intro j hj
      rw [Function.update_of_ne hj]
    · left
      rw [Function.update_self]
    · have hh := distance_update x y i u
      have hd : (y i).val - (x i).val + ((x i).val - (y i).val) =
          ((y i).val - u.val + (u.val - (y i).val)) + 1 := by
        dsimp only [u]
        omega
      omega
  · let u : Fin (n + 1) := ⟨(x i).val - 1, by have hx := (x i).isLt; omega⟩
    refine ⟨Function.update x i u, ⟨i, ?_, ?_⟩, ?_⟩
    · intro j hj
      rw [Function.update_of_ne hj]
    · right
      rw [Function.update_self]
      change (x i).val - 1 + 1 = (x i).val
      omega
    · have hh := distance_update x y i u
      have hd : (y i).val - (x i).val + ((x i).val - (y i).val) =
          ((y i).val - u.val + (u.val - (y i).val)) + 1 := by
        dsimp only [u]
        omega
      omega


/-- Finite coordinate paths are constructed by repeatedly decreasing the actual integer distance. -/
theorem path_of_distance_le {D n : ℕ} (k : ℕ) :
    ∀ x y : Box D n, gridDistance x y ≤ k →
      ∃ l ≤ k, ∃ γ : ℕ → Box D n, γ 0 = x ∧ γ l = y ∧
        ∀ j < l, UnitStep (γ j) (γ (j + 1)) := by
  induction k with
  | zero =>
    intro x y h
    have hxy := gridDistance_eq_zero (Nat.eq_zero_of_le_zero h)
    subst y
    exact ⟨0, le_rfl, fun _ => x, rfl, rfl, fun j hj => by omega⟩
  | succ k ih =>
    intro x y h
    by_cases hxy : x = y
    · subst y
      exact ⟨0, Nat.zero_le _, fun _ => x, rfl, rfl, fun j hj => by omega⟩
    obtain ⟨z, hxz, hd⟩ := step_toward x y hxy
    obtain ⟨l, hl, γ, h0, hend, hs⟩ := ih z y (by omega)
    let δ : ℕ → Box D n := fun j => if j = 0 then x else γ (j - 1)
    refine ⟨l + 1, by omega, δ, ?_, ?_, ?_⟩
    · simp only [δ, ite_true]
    · simpa only [δ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] using hend
    · intro j hj
      by_cases hj0 : j = 0
      · subst j
        simpa only [δ, ite_true, zero_add, Nat.one_ne_zero, ite_false, Nat.sub_self, h0] using hxz
      · have hh := hs (j - 1) (by omega)
        have he : j - 1 + 1 = j := by omega
        simpa only [δ, hj0, ite_false, Nat.add_one_ne_zero, Nat.add_sub_cancel, he] using hh

/-- The full actual path lies in the box and has length at most D*n. -/
theorem coordinate_path {D n : ℕ} (x y : Box D n) :
    ∃ l ≤ D * n, ∃ γ : ℕ → Box D n, γ 0 = x ∧ γ l = y ∧
      ∀ j < l, UnitStep (γ j) (γ (j + 1)) :=
  path_of_distance_le (D * n) x y (gridDistance_le x y)

/-- Physical integer-coordinate interpretation of each unit step. -/
theorem chart_unit_step {D n : ℕ} (lower : Fin D → ℤ) {x y : Box D n} (h : UnitStep x y) :
    ∃ i, (∀ j, j ≠ i → chart lower x j = chart lower y j) ∧
      (chart lower x i + 1 = chart lower y i ∨ chart lower y i + 1 = chart lower x i) := by
  obtain ⟨i, hi, hs⟩ := h
  refine ⟨i, fun j hj => by simp only [chart, hi j hj], ?_⟩
  rcases hs with hs | hs
  · left
    have hh : ((x i).val : ℤ) + 1 = (y i).val := by exact_mod_cast hs
    dsimp only [chart]
    omega
  · right
    have hh : ((y i).val : ℤ) + 1 = (x i).val := by exact_mod_cast hs
    dsimp only [chart]
    omega

/-- Actual closed-cube paths, transported by the explicit affine equivalence. -/
theorem integer_coordinate_path {D n : ℕ} (lower : Fin D → ℤ)
    (x y : ↥(integerBox lower n)) :
    ∃ l ≤ D * n, ∃ γ : ℕ → (Fin D → ℤ), γ 0 = x.val ∧ γ l = y.val ∧
      (∀ j, γ j ∈ integerBox lower n) ∧
      ∀ j < l, ∃ i, (∀ k, k ≠ i → γ j k = γ (j + 1) k) ∧
        (γ j i + 1 = γ (j + 1) i ∨ γ (j + 1) i + 1 = γ j i) := by
  obtain ⟨l, hl, γ, h0, hend, hs⟩ := coordinate_path ((chartEquiv lower).symm x) ((chartEquiv lower).symm y)
  refine ⟨l, hl, fun j => chart lower (γ j), ?_, ?_, fun j => chart_mem lower (γ j), ?_⟩
  · dsimp only
    rw [h0]
    exact congrArg Subtype.val ((chartEquiv lower).apply_symm_apply x)
  · dsimp only
    rw [hend]
    exact congrArg Subtype.val ((chartEquiv lower).apply_symm_apply y)
  · intro j hj
    exact chart_unit_step lower (hs j hj)

/-- Telescoping on a true finite coordinate path. -/
theorem path_oscillation {D n : ℕ} (H : Box D n → ℝ) {L : ℝ}
    (hedge : ∀ x y, UnitStep x y → |H y - H x| ≤ L)
    (γ : ℕ → Box D n) (l : ℕ) (hs : ∀ j < l, UnitStep (γ j) (γ (j + 1))) :
    |H (γ l) - H (γ 0)| ≤ (l : ℝ) * L := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hh := ih (fun j hj => hs j (by omega))
    have hl := hedge _ _ (hs l (by omega))
    have he : H (γ (l + 1)) - H (γ 0) = (H (γ (l + 1)) - H (γ l)) + (H (γ l) - H (γ 0)) := by ring
    rw [he]
    calc
      _ ≤ |H (γ (l + 1)) - H (γ l)| + |H (γ l) - H (γ 0)| := abs_add_le _ _
      _ ≤ L + (l : ℝ) * L := add_le_add hl hh
      _ = _ := by push_cast; ring

/-- Edge bounds imply the full log-weight oscillation, with the true D*n factor. -/
theorem oscillation_of_edge_bound {D n : ℕ} (H : Box D n → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hedge : ∀ x y, UnitStep x y → |H y - H x| ≤ L) (x y : Box D n) :
    |H y - H x| ≤ (D : ℝ) * n * L := by
  obtain ⟨l, hl, γ, h0, hend, hs⟩ := coordinate_path x y
  have hh := path_oscillation H hedge γ l hs
  rw [h0, hend] at hh
  have hlen : (l : ℝ) ≤ (D : ℝ) * n := by exact_mod_cast hl
  exact hh.trans (mul_le_mul_of_nonneg_right hlen hL)

/-- The forward-edge convention of the existing once-counted box energy suffices. -/
theorem unit_bound_of_forward {D n : ℕ} (H : Box D n → ℝ) {L : ℝ}
    (hf : ∀ x : Box D n, ∀ i : Fin D, ∀ hi : (x i).val < n,
      |H (Function.update x i ⟨(x i).val + 1, by omega⟩) - H x| ≤ L)
    (x y : Box D n) (hxy : UnitStep x y) : |H y - H x| ≤ L := by
  classical
  have forward (x y : Box D n) (i : Fin D) (hrest : ∀ j, j ≠ i → x j = y j)
      (hstep : (x i).val + 1 = (y i).val) : |H y - H x| ≤ L := by
    have hi : (x i).val < n := by have hy := (y i).isLt; omega
    have he : Function.update x i ⟨(x i).val + 1, by omega⟩ = y := by
      funext j
      by_cases hj : j = i
      · subst j
        rw [Function.update_self]
        exact Fin.ext hstep
      · rw [Function.update_of_ne hj]
        exact hrest j hj
    simpa only [he] using hf x i hi
  obtain ⟨i, hi, hs⟩ := hxy
  rcases hs with hs | hs
  · exact forward x y i hi hs
  · simpa only [abs_sub_comm] using forward y x i (fun j hj => (hi j hj).symm) hs

theorem oscillation_of_forward_bound {D n : ℕ} (H : Box D n → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x : Box D n, ∀ i : Fin D, ∀ hi : (x i).val < n,
      |H (Function.update x i ⟨(x i).val + 1, by omega⟩) - H x| ≤ L)
    (x y : Box D n) : |H y - H x| ≤ (D : ℝ) * n * L :=
  oscillation_of_edge_bound H hL (unit_bound_of_forward H hf) x y


/-- Positive weights have a genuine nonzero finite normalizing sum, even on a singleton. -/
theorem positive_weight_sum {D n : ℕ} (w : Box D n → ℝ) (hw : ∀ x, 0 < w x) :
    0 < ∑ x, w x :=
  Finset.sum_pos (fun x _ => hw x) Finset.univ_nonempty

/-- The literal normalized box weights, without an assumed probability identity. -/
theorem normalized_weight_sum {D n : ℕ} (w : Box D n → ℝ) (hw : ∀ x, 0 < w x) :
    (∑ x, w x / ∑ y, w y) = 1 := by
  rw [← Finset.sum_div, div_self (positive_weight_sum w hw).ne']

theorem weight_ratio_of_log_bound {D n : ℕ} (w : Box D n → ℝ) (hw : ∀ x, 0 < w x)
    {B : ℝ} (hosc : ∀ x y, |Real.log (w x) - Real.log (w y)| ≤ B) (x y : Box D n) :
    w x ≤ Real.exp B * w y := by
  have hh := Real.exp_le_exp.mpr (abs_le.mp (hosc x y)).2
  rw [Real.exp_sub, Real.exp_log (hw x), Real.exp_log (hw y)] at hh
  exact (div_le_iff₀ (hw y)).mp hh

/-- Both density comparisons follow from actual positive weights and their log oscillation. -/
theorem normalized_density_comparison {D n : ℕ} (w : Box D n → ℝ) (hw : ∀ x, 0 < w x)
    {B : ℝ} (hosc : ∀ x y, |Real.log (w x) - Real.log (w y)| ≤ B) :
    (∀ x, w x / (∑ y, w y) ≤ Real.exp B * uniformWeight D n) ∧
    (∀ x, uniformWeight D n ≤ Real.exp B * (w x / (∑ y, w y))) := by
  let p : Box D n → ℝ := fun x => w x / (∑ y, w y)
  have hp : ∀ x y, p x ≤ Real.exp B * p y := by
    intro x y
    have hh := div_le_div_of_nonneg_right (weight_ratio_of_log_bound w hw hosc x y)
      (positive_weight_sum w hw).le
    simpa only [p, mul_div_assoc] using hh
  have hp1 : (∑ x, p x) = 1 := normalized_weight_sum w hw
  have havg : average D n p = uniformWeight D n := by
    unfold average
    rw [← Finset.mul_sum, hp1, mul_one]
  constructor
  · intro x
    have hh := average_mono D n (fun y => hp x y)
    rw [average_const, average_mul, havg] at hh
    exact hh
  · intro x
    have hh := average_mono D n (fun y => hp y x)
    rw [havg, average_const] at hh
    exact hh

/-- The once-counted physical rate form uses the actual normalized weights.
No separate oscillation or probability conclusion is assumed. -/
theorem normalized_box_entropy_uniform (D n N : ℕ) (hN : 0 < N)
    (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ) (f : Box D n → ℝ)
    (hw : ∀ x, 0 < w x) {L c K : ℝ} (hL : 0 ≤ L) (hc : 0 < c)
    (hside : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ K * N)
    (hlog : ∀ x : Box D n, ∀ i : Fin D, ∀ hi : (x i).val < n,
      |Real.log (w (Function.update x i ⟨(x i).val + 1, by omega⟩)) - Real.log (w x)| ≤ L)
    (hr : ∀ x i, (x i).val < n → c * N ≤ r x i) :
    entropy (finiteMeasure (fun x => w x / ∑ y, w y)) (fun x => f x ^ 2) ≤
      ((Real.exp (2 * ((D : ℝ) * n * L)) * (2 + 1 / Real.exp 1) * K / c *
        weightedEnergy D n (fun x => w x / ∑ y, w y) r f : ℝ) : EReal) := by
  have hosc (x y : Box D n) : |Real.log (w x) - Real.log (w y)| ≤ (D : ℝ) * n * L :=
    oscillation_of_forward_bound (fun x => Real.log (w x)) hL hlog y x
  have hd := normalized_density_comparison w hw hosc
  have hh := weighted_box_entropy_uniform D n N hN (fun x => w x / ∑ y, w y) r f
    (fun x => (div_pos (hw x) (positive_weight_sum w hw)).le) (normalized_weight_sum w hw)
    (Real.exp_pos _).le hc hside hd.1 hd.2 hr
  have he : Real.exp ((D : ℝ) * n * L) ^ 2 = Real.exp (2 * ((D : ℝ) * n * L)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rwa [he] at hh

/-- Source integer-coordinate version on the literal closed cube.
The forward-rate energy is exactly the frozen box form pulled back by chart. -/
theorem normalized_integer_box_entropy (D n N : ℕ) (hN : 0 < N)
    (lower : Fin D → ℤ) (w f : (Fin D → ℤ) → ℝ) (r : (Fin D → ℤ) → Fin D → ℝ)
    (hw : ∀ z ∈ integerBox lower n, 0 < w z) {L c K : ℝ} (hL : 0 ≤ L) (hc : 0 < c)
    (hside : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ K * N)
    (hlog : ∀ x : Box D n, ∀ i : Fin D, ∀ hi : (x i).val < n,
      |Real.log (w (chart lower (Function.update x i ⟨(x i).val + 1, by omega⟩))) -
        Real.log (w (chart lower x))| ≤ L)
    (hr : ∀ x : Box D n, ∀ i, (x i).val < n → c * N ≤ r (chart lower x) i) :
    entropy (finiteMeasure (fun x : Box D n => w (chart lower x) / ∑ y : Box D n, w (chart lower y)))
      (fun x => f (chart lower x) ^ 2) ≤
      ((Real.exp (2 * ((D : ℝ) * n * L)) * (2 + 1 / Real.exp 1) * K / c *
        weightedEnergy D n (fun x => w (chart lower x) / ∑ y : Box D n, w (chart lower y))
          (fun x i => r (chart lower x) i) (fun x => f (chart lower x)) : ℝ) : EReal) :=
  normalized_box_entropy_uniform D n N hN (fun x => w (chart lower x))
    (fun x i => r (chart lower x) i) (fun x => f (chart lower x))
    (fun x => hw _ (chart_mem lower x)) hL hc hside hlog hr


/-- The literal source side length 2*ceil(sqrt(N)/u)-1 has bounded square.
The number of edges is one smaller; retaining that subtraction gives a uniform oscillation bound. -/
theorem ceiling_box_bounds {n N : ℕ} (hN : 1 ≤ N) {u : ℝ} (hu : 1 ≤ u)
    (hn : n = 2 * ⌈Real.sqrt (N : ℝ) / u⌉₊ - 2) :
    ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * N ∧
      ∀ C : ℝ, 0 ≤ C → (n : ℝ) * (C * (1 + u) / Real.sqrt (N : ℝ)) ≤ 4 * C := by
  have hup : 0 < u := by linarith
  have hS : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  have hSp : 0 < Real.sqrt (N : ℝ) := by linarith
  have hc := Nat.ceil_lt_add_one (div_nonneg hSp.le hup.le)
  have hcpos : 0 < ⌈Real.sqrt (N : ℝ) / u⌉₊ := Nat.ceil_pos.mpr (div_pos hSp hup)
  have hnreal : (n : ℝ) + 2 = 2 * (⌈Real.sqrt (N : ℝ) / u⌉₊ : ℝ) := by
    have hh : n + 2 = 2 * ⌈Real.sqrt (N : ℝ) / u⌉₊ := by omega
    exact_mod_cast hh
  have hnle : (n : ℝ) ≤ 2 * (Real.sqrt (N : ℝ) / u) := by linarith
  have hdiv : Real.sqrt (N : ℝ) / u ≤ Real.sqrt (N : ℝ) :=
    (div_le_iff₀ hup).mpr (by nlinarith [mul_nonneg hSp.le (sub_nonneg.mpr hu)])
  constructor
  · have hlen : (n : ℝ) + 1 ≤ 3 * Real.sqrt (N : ℝ) := by linarith
    have hh := mul_self_le_mul_self (show 0 ≤ (n : ℝ) + 1 by positivity) hlen
    have hs := Real.sq_sqrt (Nat.cast_nonneg N)
    push_cast
    nlinarith only [hh, hs]
  · intro C hC
    have hfrac : (1 + u) / u ≤ 2 := (div_le_iff₀ hup).mpr (by linarith)
    calc
      _ ≤ (2 * (Real.sqrt (N : ℝ) / u)) * (C * (1 + u) / Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hnle (by positivity)
      _ = (2 * C) * ((1 + u) / u) := by field_simp
      _ ≤ (2 * C) * 2 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 4 * C := by ring

/-- Uniform conditional entropy bound at the actual source ceiling scale.
The shell radius/containment argument must separately supply the displayed local log increment.
The conclusion has no N- or scale-dependent coefficient. -/
theorem ceiling_scale_box_entropy (D n N : ℕ) (hN : 1 ≤ N) {u C c : ℝ}
    (hu : 1 ≤ u) (hC : 0 ≤ C) (hc : 0 < c)
    (hn : n = 2 * ⌈Real.sqrt (N : ℝ) / u⌉₊ - 2)
    (w : Box D n → ℝ) (r : Box D n → Fin D → ℝ) (f : Box D n → ℝ)
    (hw : ∀ x, 0 < w x)
    (hlog : ∀ x : Box D n, ∀ i : Fin D, ∀ hi : (x i).val < n,
      |Real.log (w (Function.update x i ⟨(x i).val + 1, by omega⟩)) - Real.log (w x)| ≤
        C * (1 + u) / Real.sqrt (N : ℝ))
    (hr : ∀ x i, (x i).val < n → c * N ≤ r x i) :
    entropy (finiteMeasure (fun x => w x / ∑ y, w y)) (fun x => f x ^ 2) ≤
      ((Real.exp (8 * D * C) * (2 + 1 / Real.exp 1) * 9 / c *
        weightedEnergy D n (fun x => w x / ∑ y, w y) r f : ℝ) : EReal) := by
  have hb := ceiling_box_bounds hN hu hn
  have hL : 0 ≤ C * (1 + u) / Real.sqrt (N : ℝ) := by positivity
  have hosc (x y : Box D n) : |Real.log (w x) - Real.log (w y)| ≤ 4 * D * C := by
    calc
      _ ≤ (D : ℝ) * n * (C * (1 + u) / Real.sqrt (N : ℝ)) :=
        oscillation_of_forward_bound (fun x => Real.log (w x)) hL hlog y x
      _ = (D : ℝ) * ((n : ℝ) * (C * (1 + u) / Real.sqrt (N : ℝ))) := by ring
      _ ≤ (D : ℝ) * (4 * C) := mul_le_mul_of_nonneg_left (hb.2 C hC) (Nat.cast_nonneg D)
      _ = _ := by ring
  have hd := normalized_density_comparison w hw hosc
  have hh := weighted_box_entropy_uniform D n N (by omega) (fun x => w x / ∑ y, w y) r f
    (fun x => (div_pos (hw x) (positive_weight_sum w hw)).le) (normalized_weight_sum w hw)
    (Real.exp_pos _).le hc hb.1 hd.1 hd.2 hr
  have he : Real.exp (4 * (D : ℝ) * C) ^ 2 = Real.exp (8 * D * C) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rwa [he] at hh

end PeriodicAttractiveLogGas.IntegerBoxLogWeights
