import LeanResearch.PeriodicAttractiveLogGas.ProductTentPartition
import LeanResearch.PeriodicAttractiveLogGas.FiniteSquaredPartition
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The actual truncated dyadic shell partition in source2160–2175.
The shell variable is log base2 of max(radius,1). -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.DyadicShellPartition
open ProductTentPartition

/-- The source's clipped positive part. -/
def ramp (x : ℝ) : ℝ := min 1 (max x 0)

theorem ramp_nonneg (x : ℝ) : 0 ≤ ramp x :=
  le_min (by norm_num) (le_max_right _ _)

theorem ramp_le_one (x : ℝ) : ramp x ≤ 1 := min_le_left _ _

theorem ramp_eq_zero {x : ℝ} (hx : x ≤ 0) : ramp x = 0 := by
  simp [ramp, max_eq_right hx]

theorem ramp_eq_one {x : ℝ} (hx : 1 ≤ x) : ramp x = 1 := by
  rw [ramp, max_eq_left (by linarith), min_eq_left hx]

theorem ramp_eq_self {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : ramp x = x := by
  rw [ramp, max_eq_left hx, min_eq_right hx1]

theorem ramp_ne_zero_iff (x : ℝ) : ramp x ≠ 0 ↔ 0 < x := by
  constructor
  · intro h
    by_contra hx
    exact h (ramp_eq_zero (by linarith))
  · intro hx hz
    have hp : 0 < ramp x := lt_min (by norm_num) (lt_max_of_lt_left hx)
    linarith

/-- Exact finite-difference identity used to telescope all shells. -/
theorem hat_add_ramp (x : ℝ) : hat x + ramp x = ramp (x + 1) := by
  by_cases hx : x ≤ -1
  · rw [ramp_eq_zero (by linarith), ramp_eq_zero (by linarith)]
    simp only [hat, abs_of_nonpos (by linarith : x ≤ 0)]
    rw [max_eq_right (by linarith)]
    ring
  by_cases hx0 : x ≤ 0
  · rw [ramp_eq_zero hx0, ramp_eq_self (by linarith) (by linarith)]
    rw [hat, abs_of_nonpos hx0, max_eq_left (by linarith)]
    ring
  by_cases hx1 : x ≤ 1
  · rw [ramp_eq_self (by linarith) hx1, ramp_eq_one (by linarith)]
    rw [hat, abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    ring
  · rw [ramp_eq_one (by linarith), ramp_eq_one (by linarith)]
    rw [hat, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
    ring

theorem max_zero_change (x y : ℝ) : |max x 0 - max y 0| ≤ |x - y| := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy, sub_self, abs_zero]
    exact abs_nonneg _
  · rw [max_eq_right hx, max_eq_left hy, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_right hy, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_left hy]

theorem min_one_change (x y : ℝ) : |min 1 x - min 1 y| ≤ |x - y| := by
  rcases le_total x 1 with hx | hx <;> rcases le_total y 1 with hy | hy
  · rw [min_eq_right hx, min_eq_right hy]
  · rw [min_eq_right hx, min_eq_left hy, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_left hx, min_eq_right hy, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_left hx, min_eq_left hy, sub_self, abs_zero]
    exact abs_nonneg _

theorem ramp_change (x y : ℝ) : |ramp x - ramp y| ≤ |x - y| :=
  (min_one_change (max x 0) (max y 0)).trans (max_zero_change x y)

/-- All finite shells and the literal final singleton coefficient sum to one. -/
theorem shells_sum (J : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range (J + 1), hat (t - j)) + ramp (t - J) = 1 := by
  induction J with
  | zero =>
    simpa only [Nat.zero_add, Nat.cast_zero, sub_zero, Finset.sum_range_one] using
      (hat_add_ramp t).trans (ramp_eq_one (by linarith))
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hh := hat_add_ramp (t - ((J + 1 : ℕ) : ℝ))
    have he : t - ((J + 1 : ℕ) : ℝ) + 1 = t - (J : ℝ) := by push_cast; ring
    rw [he] at hh
    linarith

/-- A nonzero shell uses the actual floor or its successor. -/
theorem shell_only_two {t : ℝ} (ht : 0 ≤ t) (j : ℕ) (hj : hat (t - j) ≠ 0) :
    j = ⌊t⌋₊ ∨ j = ⌊t⌋₊ + 1 := by
  have hh := abs_lt.mp ((hat_ne_zero_iff _).mp hj)
  have hfloor := Nat.floor_le ht
  have hfloor' := Nat.lt_floor_add_one t
  have hlo : ⌊t⌋₊ ≤ j := by
    by_contra hn
    have hr : (j : ℝ) + 1 ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast (show j + 1 ≤ ⌊t⌋₊ by omega)
    linarith
  have hhi : j ≤ ⌊t⌋₊ + 1 := by
    by_contra hn
    have hr : (⌊t⌋₊ : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast (show ⌊t⌋₊ + 2 ≤ j by omega)
    linarith
  omega

def activeShells (J : ℕ) (t : ℝ) : Finset (Fin (J + 1)) := by
  classical
  exact Finset.univ.filter (fun j => hat (t - j.val) ≠ 0)

theorem activeShells_card_le (J : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (activeShells J t).card ≤ 2 := by
  classical
  let T := activeShells J t
  have hs (j : ↥T) : j.val.val = ⌊t⌋₊ ∨ j.val.val = ⌊t⌋₊ + 1 :=
    shell_only_two ht j.val.val (Finset.mem_filter.mp j.property).2
  let code : ↥T → Bool := fun j => if j.val.val = ⌊t⌋₊ then true else false
  have hinj : Function.Injective code := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    by_cases ha : a.val.val = ⌊t⌋₊ <;> by_cases hb : b.val.val = ⌊t⌋₊
    · exact ha.trans hb.symm
    · simp [code, ha, hb] at hab
    · simp [code, ha, hb] at hab
    · exact ((hs a).resolve_left ha).trans ((hs b).resolve_left hb).symm
  have hh := Fintype.card_le_of_injective code hinj
  simpa only [T, Fintype.card_coe, Fintype.card_bool] using hh

/-- The exact logarithmic shell variable in the manuscript. -/
def tau (r : ℝ) : ℝ := Real.logb 2 (max r 1)

def shell (j : ℕ) (r : ℝ) : ℝ := hat (tau r - j)

def tail (J : ℕ) (r : ℝ) : ℝ := ramp (tau r - J)

theorem tau_nonneg (r : ℝ) : 0 ≤ tau r :=
  Real.logb_nonneg (by norm_num) (le_max_right _ _)

theorem shell_nonneg (j : ℕ) (r : ℝ) : 0 ≤ shell j r := hat_nonneg _
theorem shell_le_one (j : ℕ) (r : ℝ) : shell j r ≤ 1 := hat_le_one _
theorem tail_nonneg (J : ℕ) (r : ℝ) : 0 ≤ tail J r := ramp_nonneg _
theorem tail_le_one (J : ℕ) (r : ℝ) : tail J r ≤ 1 := ramp_le_one _

theorem dyadic_sum (J : ℕ) (r : ℝ) :
    (∑ j ∈ Finset.range (J + 1), shell j r) + tail J r = 1 :=
  shells_sum J (tau_nonneg r)

/-- An active finite shell has the actual source upper radius. -/
theorem shell_radius_upper {j : ℕ} {r : ℝ} (h : shell j r ≠ 0) :
    r < (2 : ℝ) ^ (j + 1) := by
  have ht : tau r < ((j + 1 : ℕ) : ℝ) := by
    have hh := abs_lt.mp ((hat_ne_zero_iff _).mp h)
    push_cast
    linarith
  have hh := (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := max r 1)
    (y := ((j + 1 : ℕ) : ℝ)) (by norm_num) (by positivity)).mp ht
  rw [Real.rpow_natCast] at hh
  exact (le_max_left _ _).trans_lt hh

theorem tail_radius_lower {J : ℕ} {r : ℝ} (h : tail J r ≠ 0) :
    (2 : ℝ) ^ J < r := by
  have ht : (J : ℝ) < tau r := by
    have hh := (ramp_ne_zero_iff _).mp h
    linarith
  have hh := (Real.lt_logb_iff_rpow_lt (b := (2 : ℝ)) (x := (J : ℝ))
    (y := max r 1) (by norm_num) (by positivity)).mp ht
  rw [Real.rpow_natCast] at hh
  have hpow : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
  rcases lt_max_iff.mp hh with hr | hr
  · exact hr
  · linarith

theorem shell_scale_bound {j : ℕ} {r : ℝ} (h : shell j r ≠ 0) :
    (2 : ℝ) ^ j < 2 * max r 1 := by
  have ht : (j : ℝ) < tau r + 1 := by
    have hh := abs_lt.mp ((hat_ne_zero_iff _).mp h)
    linarith
  have hl : Real.logb 2 (2 * max r 1) = tau r + 1 := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
    unfold tau
    ring
  rw [← hl] at ht
  have hh := (Real.lt_logb_iff_rpow_lt (b := (2 : ℝ)) (x := (j : ℝ))
    (y := 2 * max r 1) (by norm_num) (by positivity)).mp ht
  simpa only [Real.rpow_natCast] using hh


theorem max_one_change (x y : ℝ) : |max x 1 - max y 1| ≤ |x - y| := by
  rcases le_total x 1 with hx | hx <;> rcases le_total y 1 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy, sub_self, abs_zero]
    exact abs_nonneg _
  · rw [max_eq_right hx, max_eq_left hy, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_right hy, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_left hy]

/-- Quantitative logarithm estimate derived from log(u) <= u-1. -/
theorem log_difference_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have hap : 0 < a := hm.trans_le ha
  have hbp : 0 < b := hm.trans_le hb
  have bound (x y : ℝ) (hx : 0 < x) (hy : m ≤ y) :
      Real.log x - Real.log y ≤ |x - y| / m := by
    have hyp : 0 < y := hm.trans_le hy
    have hh := Real.log_le_sub_one_of_pos (div_pos hx hyp)
    rw [Real.log_div hx.ne' hyp.ne'] at hh
    have he : x / y - 1 = (x - y) / y := by field_simp
    rw [he] at hh
    exact hh.trans ((div_le_div_of_nonneg_right (le_abs_self _) hyp.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hm hy))
  rw [abs_le]
  constructor
  · have hh := bound b a hbp ha
    rw [abs_sub_comm b a] at hh
    linarith
  · exact bound a b hap hb

/-- The one-step shell modulus retains the decaying radial denominator. -/
theorem tau_change {r s : ℝ} (hr : 0 ≤ r) (hrs : |r - s| ≤ 1) :
    |tau r - tau s| ≤ 4 * |r - s| / ((1 + r) * Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm : 0 < (1 + r) / 4 := by positivity
  have hA : (1 + r) / 4 ≤ max r 1 := by
    have h1 := le_max_right r (1 : ℝ)
    have h2 := le_max_left r (1 : ℝ)
    linarith
  have hB : (1 + r) / 4 ≤ max s 1 := by
    have h1 := le_max_right s (1 : ℝ)
    have h2 := le_max_left s (1 : ℝ)
    have hh := (abs_le.mp hrs).2
    linarith
  have hh := log_difference_le hm hA hB
  have hdiff := max_one_change r s
  have hbound := hh.trans (div_le_div_of_nonneg_right hdiff hm.le)
  change |Real.log (max r 1) / Real.log 2 - Real.log (max s 1) / Real.log 2| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hlog]
  calc
    _ ≤ (|r - s| / ((1 + r) / 4)) / Real.log 2 :=
      div_le_div_of_nonneg_right hbound hlog.le
    _ = _ := by field_simp

theorem shell_change {r s : ℝ} (hr : 0 ≤ r) (hrs : |r - s| ≤ 1) (j : ℕ) :
    |shell j r - shell j s| ≤ 4 * |r - s| / ((1 + r) * Real.log 2) := by
  have hh := hat_lipschitz (tau r - j) (tau s - j)
  have he : (tau r - j) - (tau s - j) = tau r - tau s := by ring
  rw [he] at hh
  exact hh.trans (tau_change hr hrs)

theorem tail_change {r s : ℝ} (hr : 0 ≤ r) (hrs : |r - s| ≤ 1) (J : ℕ) :
    |tail J r - tail J s| ≤ 4 * |r - s| / ((1 + r) * Real.log 2) := by
  have hh := ramp_change (tau r - J) (tau s - J)
  have he : (tau r - J) - (tau s - J) = tau r - tau s := by ring
  rw [he] at hh
  exact hh.trans (tau_change hr hrs)

/-- Neighbor activity bounds the genuine dyadic scale at the starting point. -/
theorem shell_scale_neighbor {r s : ℝ} (hr : 0 ≤ r) (hrs : |r - s| ≤ 1)
    {j : ℕ} (h : shell j r ≠ 0 ∨ shell j s ≠ 0) :
    (2 : ℝ) ^ j ≤ 4 * (1 + r) := by
  rcases h with h | h
  · have hh := shell_scale_bound h
    have hm : max r 1 ≤ 1 + r := max_le (by linarith) (by linarith)
    linarith
  · have hh := shell_scale_bound h
    have hs := (abs_le.mp hrs).1
    have hm : max s 1 ≤ 2 * (1 + r) := max_le (by linarith) (by linarith)
    linarith


/-- The largest allowed nonnegative dyadic shell, expressed by its exact floor. -/
def cutoff (ε : ℝ) (N : ℕ) : ℕ :=
  ⌊Real.logb 2 (ε * Real.sqrt (N : ℝ) / 8)⌋₊

theorem cutoff_bounds {ε : ℝ} {N : ℕ} (hlarge : 8 ≤ ε * Real.sqrt (N : ℝ)) :
    (2 : ℝ) ^ (cutoff ε N + 3) ≤ ε * Real.sqrt (N : ℝ) ∧
      ε * Real.sqrt (N : ℝ) < (2 : ℝ) ^ (cutoff ε N + 4) := by
  have hx : (1 : ℝ) ≤ ε * Real.sqrt (N : ℝ) / 8 := by linarith
  have hxp : (0 : ℝ) < ε * Real.sqrt (N : ℝ) / 8 := by linarith
  have ht := Real.logb_nonneg (b := (2 : ℝ)) (by norm_num) hx
  have hlo := (Real.le_logb_iff_rpow_le (b := (2 : ℝ))
    (x := (cutoff ε N : ℝ)) (by norm_num) hxp).mp (Nat.floor_le ht)
  have hup := (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ))
    (y := ((cutoff ε N : ℝ) + 1)) (by norm_num) hxp).mp
      (Nat.lt_floor_add_one (Real.logb 2 (ε * Real.sqrt (N : ℝ) / 8)))
  rw [Real.rpow_natCast] at hlo
  have he : (cutoff ε N : ℝ) + 1 = ((cutoff ε N + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast, pow_succ] at hup
  constructor
  · rw [pow_add]
    norm_num
    linarith
  · rw [pow_add]
    norm_num
    linarith

theorem cutoff_maximal {ε : ℝ} {N k : ℕ} (hlarge : 8 ≤ ε * Real.sqrt (N : ℝ))
    (hk : (2 : ℝ) ^ (k + 3) ≤ ε * Real.sqrt (N : ℝ)) : k ≤ cutoff ε N := by
  have hh := (cutoff_bounds hlarge).2
  by_contra hn
  have hkn : cutoff ε N + 4 ≤ k + 3 := by omega
  have hp : (2 : ℝ) ^ (cutoff ε N + 4) ≤ 2 ^ (k + 3) :=
    pow_le_pow_right₀ (by norm_num) hkn
  linarith

theorem tail_cutoff_radius {ε r : ℝ} {N : ℕ} (hlarge : 8 ≤ ε * Real.sqrt (N : ℝ))
    (h : tail (cutoff ε N) r ≠ 0) :
    ε * Real.sqrt (N : ℝ) / 16 < r := by
  have hh := (cutoff_bounds hlarge).2
  rw [pow_add] at hh
  norm_num at hh
  have hr := tail_radius_lower h
  linarith

def scale (N j : ℕ) : ℕ := ⌈Real.sqrt (N : ℝ) / (2 : ℝ) ^ j⌉₊

theorem scale_pos {N : ℕ} (hN : 0 < N) (j : ℕ) : 0 < scale N j :=
  Nat.ceil_pos.mpr (div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hN)) (by positivity))

theorem scale_inverse_bound {N : ℕ} (hN : 0 < N) (j : ℕ) :
    1 / (scale N j : ℝ) ≤ (2 : ℝ) ^ j / Real.sqrt (N : ℝ) := by
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hs : (0 : ℝ) < scale N j := by exact_mod_cast scale_pos hN j
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hc : Real.sqrt (N : ℝ) / (2 : ℝ) ^ j ≤ (scale N j : ℝ) := Nat.le_ceil _
  have hh := (div_le_iff₀ hp).mp hc
  apply (div_le_div_iff₀ hs hS).mpr
  nlinarith only [hh]

/-- Literal coordinate sup radius, normalized by sqrt of the particle number. -/
def radius {D : ℕ} (N : ℕ) (center y : Fin D → ℤ) : ℝ :=
  ‖fun i => ((y i - center i : ℤ) : ℝ)‖ / Real.sqrt (N : ℝ)

theorem radius_nonneg {D : ℕ} (N : ℕ) (center y : Fin D → ℤ) : 0 ≤ radius N center y :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem coordinate_le_radius {D N : ℕ} (hN : 0 < N) (center y : Fin D → ℤ) (i : Fin D) :
    |((y i - center i : ℤ) : ℝ)| ≤ radius N center y * Real.sqrt (N : ℝ) := by
  have hS : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  rw [radius, div_mul_cancel₀ _ hS]
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => ((y i - center i : ℤ) : ℝ)) i

theorem radius_neighbor_change {D N : ℕ} (hN : 0 < N)
    (center y z : Fin D → ℤ) (hyz : ∀ i, |y i - z i| ≤ 1) :
    |radius N center y - radius N center z| ≤ 1 / Real.sqrt (N : ℝ) := by
  have hS : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  let a : Fin D → ℝ := fun i => ((y i - center i : ℤ) : ℝ)
  let b : Fin D → ℝ := fun i => ((z i - center i : ℤ) : ℝ)
  have hb : ‖a - b‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    change |((y i - center i : ℤ) : ℝ) - ((z i - center i : ℤ) : ℝ)| ≤ 1
    have he : ((y i - center i : ℤ) : ℝ) - ((z i - center i : ℤ) : ℝ) = ((y i - z i : ℤ) : ℝ) := by push_cast; ring
    rw [he]
    exact_mod_cast hyz i
  change |‖a‖ / Real.sqrt (N : ℝ) - ‖b‖ / Real.sqrt (N : ℝ)| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hS]
  exact div_le_div_of_nonneg_right ((abs_norm_sub_norm_le a b).trans hb) hS.le

theorem radius_neighbor_small {D N : ℕ} (hN : 0 < N)
    (center y z : Fin D → ℤ) (hyz : ∀ i, |y i - z i| ≤ 1) :
    |radius N center y - radius N center z| ≤ 1 := by
  have hh := radius_neighbor_change hN center y z hyz
  have hS : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  exact hh.trans ((one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS).trans_eq (by norm_num))

end PeriodicAttractiveLogGas.DyadicShellPartition
