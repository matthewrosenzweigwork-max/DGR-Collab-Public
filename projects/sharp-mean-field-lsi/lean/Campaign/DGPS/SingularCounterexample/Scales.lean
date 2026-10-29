import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Elementary scale definitions for the singular counterexample.

The geometric and asymptotic scale estimates are kept in this file so the
barrier and particle-test modules can use the same constants.
-/

open Filter Topology

namespace DGPS.SingularCounterexample

/-- The shifted index used to keep all factorial estimates away from zero. -/
def shiftedIndex (n : ℕ) : ℕ := n + 4

/-- Separation between the center and the two satellite Poisson peaks. -/
noncomputable def separation (n : ℕ) : ℝ := ((10 : ℝ) ^ shiftedIndex n)⁻¹

/-- Amplitude of the `n`-th barrier block. -/
noncomputable def height (n : ℕ) : ℝ := ((shiftedIndex n).factorial : ℝ) ^ 2

/-- Width of the `n`-th Poisson peak. -/
noncomputable def width (n : ℕ) : ℝ := ((10 : ℝ) ^ (shiftedIndex n).factorial)⁻¹

/-- Radius of the `n`-th Poisson peak. -/
noncomputable def radius (n : ℕ) : ℝ := 1 - width n

theorem shiftedIndex_ge_four (n : ℕ) : 4 ≤ shiftedIndex n := by
  simp [shiftedIndex]

theorem shiftedIndex_monotone {n m : ℕ} (hnm : n ≤ m) :
    shiftedIndex n ≤ shiftedIndex m := by
  simpa [shiftedIndex] using Nat.add_le_add_right hnm 4

theorem shiftedIndex_tendsto_atTop : Tendsto shiftedIndex atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop b] with n hn
  exact hn.trans (by simp [shiftedIndex])

theorem separation_pos (n : ℕ) : 0 < separation n := by
  simp only [separation]
  positivity

theorem separation_le_ten_neg_four (n : ℕ) :
    separation n ≤ (10 : ℝ) ^ (-(4 : ℝ)) := by
  have hpow : (10 : ℝ) ^ (4 : ℕ) ≤ (10 : ℝ) ^ (shiftedIndex n) := by
    gcongr
    · norm_num
    · exact shiftedIndex_ge_four n
  have hinv : ((10 : ℝ) ^ shiftedIndex n)⁻¹ ≤ ((10 : ℝ) ^ (4 : ℕ))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  simpa [separation, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10), Real.rpow_natCast] using hinv

theorem separation_succ_lt (n : ℕ) : separation (n + 1) < separation n := by
  have he : shiftedIndex (n + 1) = shiftedIndex n + 1 := by simp [shiftedIndex, Nat.add_assoc]
  have hpow : (10 : ℝ) ^ shiftedIndex n < (10 : ℝ) ^ shiftedIndex (n + 1) := by
    rw [he, pow_succ]
    have hp : 0 < (10 : ℝ) ^ shiftedIndex n := by positivity
    nlinarith
  exact (inv_lt_inv₀ (by positivity) (by positivity)).2 hpow

theorem separation_tendsto_zero : Tendsto separation atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (10 : ℝ) ^ shiftedIndex n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 10)).comp
      shiftedIndex_tendsto_atTop
  change Tendsto (fun n : ℕ => ((10 : ℝ) ^ shiftedIndex n)⁻¹) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp hpow

theorem height_pos (n : ℕ) : 0 < height n := by
  simp only [height]
  positivity

theorem width_pos (n : ℕ) : 0 < width n := by
  simp only [width]
  positivity

theorem height_tendsto_atTop : Tendsto height atTop atTop := by
  have hidx : Tendsto (fun n : ℕ => (shiftedIndex n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp shiftedIndex_tendsto_atTop
  refine tendsto_atTop_mono' atTop ?_ hidx
  filter_upwards [] with n
  change (shiftedIndex n : ℝ) ≤ ((shiftedIndex n).factorial : ℝ) ^ 2
  have hle : shiftedIndex n ≤ (shiftedIndex n).factorial := Nat.self_le_factorial _
  have hle' : (shiftedIndex n : ℝ) ≤ ((shiftedIndex n).factorial : ℝ) := by exact_mod_cast hle
  have hpos : (1 : ℝ) ≤ ((shiftedIndex n).factorial : ℝ) := by
    have h := Nat.factorial_pos (shiftedIndex n)
    exact_mod_cast (Nat.succ_le_iff.mpr h)
  nlinarith

theorem height_succ_ge_twenty_five (n : ℕ) : 25 * height n ≤ height (n + 1) := by
  simp only [height]
  rw [show shiftedIndex (n + 1) = shiftedIndex n + 1 by simp [shiftedIndex, Nat.add_assoc]]
  rw [Nat.factorial_succ]
  push_cast
  have hm : (5 : ℝ) ≤ (shiftedIndex n : ℝ) + 1 := by
    have hi := shiftedIndex_ge_four n
    exact_mod_cast (show 5 ≤ shiftedIndex n + 1 by omega)
  have hmSq : (25 : ℝ) ≤ ((shiftedIndex n : ℝ) + 1) ^ 2 := by nlinarith
  have hf : 0 ≤ ((shiftedIndex n).factorial : ℝ) ^ 2 := sq_nonneg _
  calc
    25 * ((shiftedIndex n).factorial : ℝ) ^ 2
        ≤ ((shiftedIndex n : ℝ) + 1) ^ 2 * ((shiftedIndex n).factorial : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hmSq hf
    _ = (((shiftedIndex n : ℝ) + 1) * ((shiftedIndex n).factorial : ℝ)) ^ 2 := by ring

noncomputable def previousHeightSum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, height j

theorem previousHeightSum_nonneg (n : ℕ) : 0 ≤ previousHeightSum n := by
  unfold previousHeightSum
  exact Finset.sum_nonneg fun j hj => (height_pos j).le

theorem previousHeightSum_succ (n : ℕ) :
    previousHeightSum (n + 1) = previousHeightSum n + height n := by
  simp [previousHeightSum, Finset.sum_range_succ]

theorem previousHeightSum_le (n : ℕ) :
    previousHeightSum (n + 1) ≤ (25 / 24 : ℝ) * height n := by
  induction n with
  | zero =>
      simp [previousHeightSum]
      nlinarith [height_pos 0]
  | succ n ih =>
      rw [previousHeightSum_succ]
      have hgrow := height_succ_ge_twenty_five n
      calc
        previousHeightSum (n + 1) + height (n + 1)
            ≤ (25 / 24 : ℝ) * height n + height (n + 1) :=
              add_le_add_left ih (height (n + 1))
        _ ≤ (25 / 24 : ℝ) * height (n + 1) := by nlinarith

private theorem twice_succ_sq_le_ten_pow (m : ℕ) (hm : 4 ≤ m) :
    2 * (m + 1) ^ 2 ≤ 10 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
      have hsmallR : 2 * ((m : ℝ) + 2) ^ 2 ≤ 10 * (2 * ((m : ℝ) + 1) ^ 2) := by
        nlinarith
      have hsmall : 2 * (m + 2) ^ 2 ≤ 10 * (2 * (m + 1) ^ 2) := by exact_mod_cast hsmallR
      calc
        2 * (m + 2) ^ 2 ≤ 10 * (2 * (m + 1) ^ 2) := hsmall
        _ ≤ 10 * 10 ^ m := Nat.mul_le_mul_left 10 ih
        _ = 10 ^ (m + 1) := by rw [pow_succ]; ring

theorem height_succ_eq (n : ℕ) :
    height (n + 1) = height n * ((shiftedIndex n : ℝ) + 1) ^ 2 := by
  simp only [height]
  rw [show shiftedIndex (n + 1) = shiftedIndex n + 1 by simp [shiftedIndex, Nat.add_assoc]]
  rw [Nat.factorial_succ]
  push_cast
  ring

theorem previousHeightSum_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => previousHeightSum n / height n) atTop (𝓝 0) := by
  have hidx : Tendsto (fun n : ℕ => (shiftedIndex n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp shiftedIndex_tendsto_atTop
  have hidx' : Tendsto (fun n : ℕ => (shiftedIndex n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hidx
  have hsquare : Tendsto (fun n : ℕ => ((shiftedIndex n : ℝ) + 1) ^ 2)
      atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hidx'
    filter_upwards [hidx'.eventually_ge_atTop 1] with n hn
    nlinarith [sq_nonneg ((shiftedIndex n : ℝ) + 1 - 1)]
  have hupper : Tendsto
      (fun n : ℕ => (25 / 24 : ℝ) / ((shiftedIndex n : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsquare)
  have hbound : ∀ n : ℕ,
      previousHeightSum (n + 1) / height (n + 1) ≤
        (25 / 24 : ℝ) / ((shiftedIndex n : ℝ) + 1) ^ 2 := by
    intro n
    rw [div_le_iff₀ (height_pos (n + 1)), height_succ_eq]
    calc
      previousHeightSum (n + 1) ≤ (25 / 24 : ℝ) * height n := previousHeightSum_le n
      _ = ((25 / 24 : ℝ) / ((shiftedIndex n : ℝ) + 1) ^ 2) *
          (height n * ((shiftedIndex n : ℝ) + 1) ^ 2) := by field_simp
  have hshift : Tendsto (fun n : ℕ => previousHeightSum (n + 1) / height (n + 1))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => div_nonneg (previousHeightSum_nonneg _) (height_pos _).le) hbound
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hEv := Metric.tendsto_nhds.1 hshift ε hε
  rw [eventually_atTop] at hEv
  obtain ⟨N, hN⟩ := hEv
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hN' : N ≤ n - 1 := by omega
  have h := hN (n - 1) hN'
  have he : (n - 1) + 1 = n := by omega
  simpa [he] using h

theorem width_succ_eq (n : ℕ) :
    width (n + 1) = width n *
      ((10 : ℝ) ^ (shiftedIndex n * (shiftedIndex n).factorial))⁻¹ := by
  simp only [width]
  rw [show shiftedIndex (n + 1) = shiftedIndex n + 1 by simp [shiftedIndex, Nat.add_assoc]]
  rw [Nat.factorial_succ]
  rw [show (shiftedIndex n + 1) * (shiftedIndex n).factorial =
      (shiftedIndex n).factorial + shiftedIndex n * (shiftedIndex n).factorial by ring]
  rw [pow_add, mul_inv]

theorem height_width_succ_le_half (n : ℕ) :
    height (n + 1) * width (n + 1) ≤ (1 / 2 : ℝ) * (height n * width n) := by
  let m := shiftedIndex n
  have hm : 4 ≤ m := shiftedIndex_ge_four n
  have hfact : 1 ≤ m.factorial := by
    exact Nat.succ_le_iff.mpr (Nat.factorial_pos m)
  have hexp : m ≤ m * m.factorial := by
    calc
      m = m * 1 := by omega
      _ ≤ m * m.factorial := Nat.mul_le_mul_left m hfact
  have hpowNat : 2 * (m + 1) ^ 2 ≤ 10 ^ m := twice_succ_sq_le_ten_pow m hm
  have hpowReal : (2 : ℝ) * ((m : ℝ) + 1) ^ 2 ≤ (10 : ℝ) ^ (m * m.factorial) := by
    calc
      (2 : ℝ) * ((m : ℝ) + 1) ^ 2 ≤ (10 : ℝ) ^ m := by exact_mod_cast hpowNat
      _ ≤ (10 : ℝ) ^ (m * m.factorial) := by
        gcongr
        · norm_num
  have hratio : ((m : ℝ) + 1) ^ 2 / (10 : ℝ) ^ (m * m.factorial) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [height_succ_eq, width_succ_eq]
  have hterm : 0 ≤ height n * width n := mul_nonneg (height_pos n).le (width_pos n).le
  calc
    height n * ((m : ℝ) + 1) ^ 2 *
        (width n * ((10 : ℝ) ^ (m * m.factorial))⁻¹)
        = height n * width n * (((m : ℝ) + 1) ^ 2 / (10 : ℝ) ^ (m * m.factorial)) := by ring
    _ ≤ (height n * width n) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hratio hterm
    _ = (1 / 2 : ℝ) * (height n * width n) := by ring

theorem height_width_summable : Summable (fun n : ℕ => height n * width n) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [] with n
  have h := height_width_succ_le_half n
  have h₁ : 0 ≤ height n * width n := mul_nonneg (height_pos n).le (width_pos n).le
  have h₂ : 0 ≤ height (n + 1) * width (n + 1) :=
    mul_nonneg (height_pos _).le (width_pos _).le
  simpa [Real.norm_eq_abs, abs_of_pos, height_pos, width_pos] using h

private theorem one_le_ten_pow : ∀ k : ℕ, (1 : ℝ) ≤ (10 : ℝ) ^ k
  | 0 => by norm_num
  | k + 1 => by
      rw [pow_succ]
      have hk := one_le_ten_pow k
      have h10 : (1 : ℝ) ≤ 10 := by norm_num
      calc
        1 = 1 * 1 := by ring
        _ ≤ 10 * (10 : ℝ) ^ k :=
          mul_le_mul h10 hk (by norm_num) (by positivity)
        _ = (10 : ℝ) ^ k * 10 := by ring

theorem height_width_sq_summable :
    Summable (fun n : ℕ => height n * width n ^ 2) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (height_pos n).le (sq_nonneg _)
  · intro n
    have hw0 := (width_pos n).le
    have hw1 : width n ≤ 1 := by
      rw [width]
      apply inv_le_one_of_one_le₀
      exact one_le_ten_pow _
    have hsq : width n ^ 2 ≤ width n := by
      have hp := mul_nonneg hw0 (sub_nonneg.mpr hw1)
      nlinarith
    exact mul_le_mul_of_nonneg_left hsq (height_pos n).le
  · exact height_width_summable

theorem inverse_width_separation_exp_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (width n)⁻¹ * Real.exp (-c * height n) * (separation n)⁻¹)
      atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun n => ((shiftedIndex n).factorial : ℝ)
  have hfact : Tendsto x atTop atTop := by
    dsimp [x]
    exact (tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop).comp
      shiftedIndex_tendsto_atTop
  have hsquare : Tendsto (fun n => x n ^ 2) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hfact
    filter_upwards [hfact.eventually_ge_atTop 1] with n hn
    nlinarith [sq_nonneg (x n - 1)]
  have hdecay : Tendsto (fun n => Real.exp (-(c / 2) * x n ^ 2)) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n => (-(c / 2)) * x n ^ 2) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by linarith : -(c / 2) < 0)).mpr hsquare
    exact Real.tendsto_exp_atBot.comp hneg
  have hbound : ∀ᶠ n in atTop,
      (width n)⁻¹ * Real.exp (-c * height n) * (separation n)⁻¹ ≤
        Real.exp (-(c / 2) * x n ^ 2) := by
    filter_upwards [hfact.eventually_ge_atTop (40 / c)] with n hn
    have hxpos : 0 ≤ x n := by positivity
    have hindex : (shiftedIndex n : ℝ) ≤ x n := by
      dsimp [x]
      exact_mod_cast (Nat.self_le_factorial (shiftedIndex n))
    have hsum : x n + (shiftedIndex n : ℝ) ≤ 2 * x n := by linarith
    have hlog0 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
    have hlogle : Real.log 10 ≤ 10 := Real.log_le_self (by norm_num)
    have hnum : (x n + (shiftedIndex n : ℝ)) * Real.log 10 ≤ 20 * x n := by
      calc
        _ ≤ (2 * x n) * Real.log 10 := mul_le_mul_of_nonneg_right hsum hlog0
        _ ≤ (2 * x n) * 10 := mul_le_mul_of_nonneg_left hlogle (by positivity)
        _ = 20 * x n := by ring
    have hcx : 40 ≤ c * x n := by
      have h := (div_le_iff₀ hc).1 hn
      nlinarith [mul_comm c (x n)]
    have hquad : 20 * x n ≤ (c / 2) * x n ^ 2 := by
      calc
        20 * x n = 40 * (x n / 2) := by ring
        _ ≤ (c * x n) * (x n / 2) :=
          mul_le_mul_of_nonneg_right hcx (by positivity)
        _ = (c / 2) * x n ^ 2 := by ring
    have hpow : (width n)⁻¹ * (separation n)⁻¹ =
        (10 : ℝ) ^ ((shiftedIndex n).factorial + shiftedIndex n) := by
      rw [width, separation, inv_inv, inv_inv, ← pow_add]
    have hexp : (10 : ℝ) ^ ((shiftedIndex n).factorial + shiftedIndex n) =
        Real.exp ((x n + (shiftedIndex n : ℝ)) * Real.log 10) := by
      have h := Real.exp_nat_mul (Real.log 10)
        ((shiftedIndex n).factorial + shiftedIndex n)
      have h10 : Real.exp (Real.log 10) = 10 := Real.exp_log (by norm_num)
      rw [h10] at h
      rw [← h]
      congr 1
      dsimp [x]
      push_cast
      ring
    have hterm : (width n)⁻¹ * Real.exp (-c * height n) * (separation n)⁻¹ =
        Real.exp ((x n + (shiftedIndex n : ℝ)) * Real.log 10 - c * x n ^ 2) := by
      rw [show (width n)⁻¹ * Real.exp (-c * height n) * (separation n)⁻¹ =
        ((width n)⁻¹ * (separation n)⁻¹) * Real.exp (-c * height n) by ring]
      rw [hpow, hexp, height]
      dsimp [x]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hterm]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay
    (Filter.Eventually.of_forall fun n => by
      simp only [width, separation]
      positivity) hbound

theorem inverse_scales_exp_previous_sum_tendsto_zero {c C : ℝ}
    (hc : 0 < c) (_hC : 0 ≤ C) :
    Tendsto
      (fun n : ℕ => (width n)⁻¹ * (separation n)⁻¹ *
        Real.exp (-c * height n + C * previousHeightSum n))
      atTop (𝓝 0) := by
  have hratio : Tendsto
      (fun n : ℕ => C * (previousHeightSum n / height n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul previousHeightSum_ratio_tendsto_zero
  have habsorb : ∀ᶠ n in atTop,
      C * (previousHeightSum n / height n) ≤ c / 2 := by
    have hEventually : ∀ᶠ n in atTop,
        C * (previousHeightSum n / height n) < c / 2 :=
      hratio.eventually (Iio_mem_nhds (by positivity))
    filter_upwards [hEventually] with n hn
    exact hn.le
  have hbound : ∀ᶠ n in atTop,
      (width n)⁻¹ * (separation n)⁻¹ *
          Real.exp (-c * height n + C * previousHeightSum n) ≤
        (width n)⁻¹ * (separation n)⁻¹ *
          Real.exp (-(c / 2) * height n) := by
    filter_upwards [habsorb] with n hn
    have hheight : 0 < height n := height_pos n
    have hsumAbsorb : C * previousHeightSum n ≤ (c / 2) * height n := by
      have hn' : C * previousHeightSum n / height n ≤ c / 2 := by
        simpa [mul_div_assoc] using hn
      exact (div_le_iff₀ hheight).1 hn'
    have hexp : -c * height n + C * previousHeightSum n ≤
        -(c / 2) * height n := by nlinarith
    have hscale : 0 ≤ (width n)⁻¹ * (separation n)⁻¹ :=
      mul_nonneg (inv_nonneg.mpr (width_pos n).le)
        (inv_nonneg.mpr (separation_pos n).le)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hscale
  have hnonneg : ∀ n : ℕ,
      0 ≤ (width n)⁻¹ * (separation n)⁻¹ *
        Real.exp (-c * height n + C * previousHeightSum n) := by
    intro n
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (width_pos n).le)
        (inv_nonneg.mpr (separation_pos n).le))
      (Real.exp_pos _).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        inverse_width_separation_exp_tendsto_zero (c := c / 2) (by positivity))
    (Filter.Eventually.of_forall hnonneg) hbound

theorem height_width_rpow_summable {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => height n * width n ^ α) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  have hindex : Tendsto (fun n : ℕ => (shiftedIndex n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp shiftedIndex_tendsto_atTop
  filter_upwards [hindex.eventually_ge_atTop (1 / α)] with n hn
  let m := shiftedIndex n
  have hm : 4 ≤ m := shiftedIndex_ge_four n
  have hmcast : 0 < (m : ℝ) := by positivity
  have hαm : 1 ≤ α * (m : ℝ) := by
    have h := (div_le_iff₀ hα).1 hn
    nlinarith
  have hfact : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos m))
  have hmfac : (m : ℝ) ≤ (m : ℝ) * (m.factorial : ℝ) := by nlinarith
  have hfactalpha : (m.factorial : ℝ) ≤
      (α * (m : ℝ)) * (m.factorial : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hαm (by positivity : 0 ≤ (m.factorial : ℝ))
  have hexponent : (m : ℝ) ≤ ((m * m.factorial : ℕ) : ℝ) * α := by
    rw [Nat.cast_mul]
    calc
      (m : ℝ) ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial m
      _ ≤ (α * (m : ℝ)) * (m.factorial : ℝ) := hfactalpha
      _ = ((m : ℝ) * (m.factorial : ℝ)) * α := by ring
  have hqpow : ((10 : ℝ) ^ (m * m.factorial)) ^ α =
      (10 : ℝ) ^ (((m * m.factorial : ℕ) : ℝ) * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hqbound : 2 * ((m : ℝ) + 1) ^ 2 ≤ ((10 : ℝ) ^ (m * m.factorial)) ^ α := by
    have hpolyNat := twice_succ_sq_le_ten_pow m hm
    have hpoly : 2 * ((m : ℝ) + 1) ^ 2 ≤ (10 : ℝ) ^ (m : ℝ) := by
      exact_mod_cast hpolyNat
    rw [hqpow]
    exact hpoly.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent)
  have hratio : ((m : ℝ) + 1) ^ 2 /
      ((10 : ℝ) ^ (m * m.factorial)) ^ α ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hrec : width (n + 1) ^ α = width n ^ α *
      (((10 : ℝ) ^ (m * m.factorial)) ^ α)⁻¹ := by
    rw [width_succ_eq, Real.mul_rpow (width_pos n).le (inv_nonneg.mpr (by positivity))]
    rw [Real.inv_rpow (by positivity)]
  have hstep := height_succ_eq n
  have hterm : 0 ≤ height n * width n ^ α :=
    mul_nonneg (height_pos n).le (Real.rpow_nonneg (width_pos n).le _)
  have hnext : 0 ≤ height (n + 1) * width (n + 1) ^ α :=
      mul_nonneg (height_pos _).le (Real.rpow_nonneg (width_pos _).le _)
  have hvalue : height (n + 1) * width (n + 1) ^ α ≤
      (1 / 2 : ℝ) * (height n * width n ^ α) := by
    rw [hstep, hrec]
    calc
      height n * ((m : ℝ) + 1) ^ 2 *
          (width n ^ α * (((10 : ℝ) ^ (m * m.factorial)) ^ α)⁻¹)
          = (height n * width n ^ α) *
              (((m : ℝ) + 1) ^ 2 /
                ((10 : ℝ) ^ (m * m.factorial)) ^ α) := by ring
      _ ≤ (height n * width n ^ α) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio hterm
      _ = (1 / 2 : ℝ) * (height n * width n ^ α) := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg hnext, Real.norm_eq_abs, abs_of_nonneg hterm]
  exact hvalue

theorem height_width_rpow_tail_tendsto_zero {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun N : ℕ => ∑' n : ℕ, height (n + N) * width (n + N) ^ α)
      atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun n => height n * width n ^ α
  have hf : Summable f := height_width_rpow_summable hα
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n)
      atTop (𝓝 (∑' n : ℕ, f n)) := hf.tendsto_sum_tsum_nat
  have htail : Tendsto (fun N : ℕ => (∑' n : ℕ, f n) -
      ∑ n ∈ Finset.range N, f n) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (∑' n : ℕ, f n)) atTop
        (𝓝 (∑' n : ℕ, f n)) := tendsto_const_nhds
    simpa using hconst.sub hpartial
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N, f n) + (∑' n : ℕ, f (n + N)) = ∑' n : ℕ, f n :=
    hf.sum_add_tsum_nat_add N
  have htailEq (N : ℕ) :
      (∑' n : ℕ, f (n + N)) = (∑' n : ℕ, f n) - ∑ n ∈ Finset.range N, f n := by
    linarith [hsum N]
  simpa only [f, htailEq] using htail

theorem width_le_ten_neg_twenty_four (n : ℕ) :
    width n ≤ (10 : ℝ) ^ (-(24 : ℝ)) := by
  have hm : 24 ≤ (shiftedIndex n).factorial := by
    have hi := shiftedIndex_ge_four n
    calc
      24 = Nat.factorial 4 := by norm_num
      _ ≤ Nat.factorial (shiftedIndex n) := Nat.factorial_le hi
  have hpow : (10 : ℝ) ^ (24 : ℕ) ≤ (10 : ℝ) ^ (shiftedIndex n).factorial := by
    gcongr
    · norm_num
  have hinv : ((10 : ℝ) ^ (shiftedIndex n).factorial)⁻¹ ≤ ((10 : ℝ) ^ (24 : ℕ))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  simpa [width, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10), Real.rpow_natCast] using hinv

private theorem index_add_two_le_factorial (m : ℕ) (hm : 4 ≤ m) :
    m + 2 ≤ m.factorial := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [Nat.factorial_succ]
      have hprod : (m + 1) * (m + 2) ≤ (m + 1) * m.factorial :=
        Nat.mul_le_mul_left _ ih
      have hsmall : m + 3 ≤ (m + 1) * (m + 2) := by nlinarith
      exact le_trans hsmall hprod

theorem width_le_separation_div_hundred (n : ℕ) :
    width n ≤ separation n / 100 := by
  have hm : shiftedIndex n + 2 ≤ (shiftedIndex n).factorial :=
    index_add_two_le_factorial (shiftedIndex n) (shiftedIndex_ge_four n)
  have hpow : (10 : ℝ) ^ (shiftedIndex n + 2) ≤ (10 : ℝ) ^ (shiftedIndex n).factorial := by
    gcongr
    · norm_num
  have hinv : ((10 : ℝ) ^ (shiftedIndex n).factorial)⁻¹ ≤
      ((10 : ℝ) ^ (shiftedIndex n + 2))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hscale : ((10 : ℝ) ^ (shiftedIndex n + 2))⁻¹ = separation n / 100 := by
    simp [separation, pow_add]
    ring
  simpa [width, hscale] using hinv

theorem width_tendsto_zero : Tendsto width atTop (𝓝 0) := by
  have hupper : ∀ n : ℕ, width n ≤ separation n := by
    intro n
    have h := width_le_separation_div_hundred n
    have hs := (separation_pos n).le
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    separation_tendsto_zero (fun n => (width_pos n).le)
    hupper

theorem radius_tendsto_one : Tendsto radius atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - width n) atTop (𝓝 1)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using hconst.sub width_tendsto_zero

theorem radius_lt_one (n : ℕ) : radius n < 1 := by
  simp only [radius]
  linarith [width_pos n]

theorem radius_ge_half (n : ℕ) : (1 / 2 : ℝ) ≤ radius n := by
  rw [radius]
  have hw := width_le_ten_neg_twenty_four n
  have hw' : width n ≤ 1 / 2 := le_trans hw (by norm_num)
  linarith

end DGPS.SingularCounterexample
