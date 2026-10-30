import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMoments
import DGPS.Frontier.STR029.T44

/-! A genuine uniform exponential remainder on the same retained ordinary branch.
The existing scalar Taylor theorem is applied to the actual exponent; the unknown
cubic chart remainder is retained linearly, rather than assigned a formal coefficient. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem exp_linear_perturbation (x r : ℝ) (hx : |x| ≤ 1) (hr : |r| ≤ 1) :
    |Real.exp (x + r) - Real.exp x - r| ≤ 3 * r ^ 2 + 2 * |x| * |r| := by
  have hx1 := Real.exp_bound hx (n := 1) (by norm_num)
  have hr2 := Real.exp_bound hr (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, sq_abs] at hx1 hr2
  have hexp : |Real.exp x| ≤ 3 := by
    rw [abs_of_pos (Real.exp_pos x)]
    nlinarith [(abs_le.mp hx1).2]
  have htail : |Real.exp r - (1 + r)| ≤ r ^ 2 := by
    nlinarith [sq_nonneg r]
  have he : Real.exp (x + r) - Real.exp x - r =
      Real.exp x * (Real.exp r - (1 + r)) + r * (Real.exp x - 1) := by
    rw [Real.exp_add]
    ring
  rw [he]
  calc
    _ ≤ |Real.exp x * (Real.exp r - (1 + r))| + |r * (Real.exp x - 1)| := abs_add_le _ _
    _ = |Real.exp x| * |Real.exp r - (1 + r)| + |r| * |Real.exp x - 1| := by rw [abs_mul, abs_mul]
    _ ≤ 3 * r ^ 2 + |r| * (2 * |x|) := by
      gcongr
      simpa only [mul_comm] using hx1
    _ = _ := by ring

private theorem exp_twoJet_cubic_error (h a b : ℝ)
    (hh : 0 < h) (hh12 : h ≤ 1 / 12) (ha : |a| ≤ 3) (hb : |b| ≤ 3) :
    |Real.exp (h * a + h ^ 2 * b) -
      (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6))| ≤ 451 * h ^ 4 := by
  have hh1 : |h| ≤ 1 := by rw [abs_of_pos hh]; linarith
  have hNh : 3 * |h| ≤ (1 / 4 : ℝ) := by rw [abs_of_pos hh]; linarith
  have he := exp_scalar_STR02944 hh1 hNh ha hb
  norm_num only [show (3 : ℝ) ^ 3 + 3 ^ 4 + 3 ^ 5 = 351 by norm_num] at he
  have h1 : |b ^ 2| ≤ 9 := by
    have ht := mono_bound_STR02944 hh1 ha hb 0 0 2
    norm_num at ht ⊢
    exact ht
  have h2 : |a ^ 2 * b| ≤ 27 := by
    have ht := mono_bound_STR02944 hh1 ha hb 0 2 1
    norm_num at ht ⊢
    exact ht
  have h3 : |a ^ 4| ≤ 81 := by
    have ht := mono_bound_STR02944 hh1 ha hb 0 4 0
    norm_num at ht ⊢
    exact ht
  have hcoef : |b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24| ≤ (100 : ℝ) := by
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> linarith
  have hfour : |h ^ 4 * (b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24)| ≤ 100 * h ^ 4 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hh.le 4)]
    nlinarith [mul_le_mul_of_nonneg_left hcoef (pow_nonneg hh.le 4)]
  have hp : h ^ 5 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le (by linarith) (by norm_num)
  have he' : |Real.exp (h * a + h ^ 2 * b) -
      (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) +
        h ^ 4 * (b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24))| ≤ 351 * h ^ 4 := by
    rw [abs_of_pos hh] at he
    exact he.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
  have ht := abs_sub_le (Real.exp (h * a + h ^ 2 * b))
    (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) +
      h ^ 4 * (b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24))
    (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6))
  have hc : |(1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) +
      h ^ 4 * (b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24)) -
      (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6))| ≤ 100 * h ^ 4 := by
    convert hfour using 1 <;> ring
  linarith

/-- Uniform cubic exponential expansion on the SAME actual branch. The actual
unknown logarithmic remainder occurs linearly on the right; it is never replaced
by a presumed cubic jet. Constants and the interval are fixed before h and t. -/
theorem ordinaryRoot_evenBranch_exponential_expansion (D : OrdinaryRootGraphData) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ → ∀ t : ℝ,
        let u := chartU_STR02924 D.ψ h (D.Z 0 h)
        let a := Real.cos (3 * t) + 2 * Real.cos t
        let b := (2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)
        let r := u t - 2 * h * Real.cos t - h ^ 2 * b
        |Real.exp (h * Real.cos (3 * t) + u t) -
          (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) + r)| ≤
          K * h ^ 4 := by
  obtain ⟨C, hC, hrem⟩ := ordinaryRoot_evenBranch_C1_expansion D
  let δ := min D.radius (min (1 / 12) (C + 1)⁻¹)
  let K := 451 + 3 * C ^ 2 + 12 * C
  have hδ : 0 < δ := lt_min D.radius_pos (lt_min (by norm_num) (by positivity))
  refine ⟨K, δ, by dsimp [K]; positivity, hδ, min_le_left _ _, fun h hh hhd t => ?_⟩
  have hhr : |h| ≤ D.radius := by
    rw [abs_of_pos hh]
    exact (hhd.trans_le (min_le_left _ _)).le
  have hh12 : h ≤ (1 / 12 : ℝ) := (hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hh1 : h ≤ 1 := by linarith
  have hhC : h ≤ (C + 1)⁻¹ := (hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hCh : C * h ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hhC (by positivity : 0 ≤ C + 1)
    rw [mul_inv_cancel₀ (by positivity : C + 1 ≠ 0)] at hm
    nlinarith
  let u := chartU_STR02924 D.ψ h (D.Z 0 h)
  let a := Real.cos (3 * t) + 2 * Real.cos t
  let b := (2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)
  let r := u t - 2 * h * Real.cos t - h ^ 2 * b
  let x := h * a + h ^ 2 * b
  have ha : |a| ≤ 3 := by
    have ht := abs_add_le (Real.cos (3 * t)) (2 * Real.cos t)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    dsimp [a]
    nlinarith [Real.abs_cos_le_one (3 * t), Real.abs_cos_le_one t]
  have hb : |b| ≤ 3 := by
    have ht : |(2 / 3 : ℝ) * Real.cos (2 * t) - (1 / 5 : ℝ) * Real.cos (4 * t)| ≤
        |(2 / 3 : ℝ) * Real.cos (2 * t)| + |(1 / 5 : ℝ) * Real.cos (4 * t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((2 / 3 : ℝ) * Real.cos (2 * t)) (-((1 / 5 : ℝ) * Real.cos (4 * t)))
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at ht
    dsimp [b]
    nlinarith [Real.abs_cos_le_one (2 * t), Real.abs_cos_le_one (4 * t)]
  have hr : |r| ≤ C * h ^ 3 := by
    simpa only [abs_of_pos hh] using (hrem h hhr t).1
  have hp3 : h ^ 3 ≤ h := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one hh.le hh1 (by norm_num : (1 : ℕ) ≤ 3))
  have hr1 : |r| ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hp3 hC]
  have hh2 : h ^ 2 ≤ h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have hx : |x| ≤ 6 * h := by
    have ht := abs_add_le (h * a) (h ^ 2 * b)
    rw [abs_mul, abs_of_pos hh, abs_mul, abs_of_nonneg (sq_nonneg h)] at ht
    dsimp [x]
    nlinarith [mul_le_mul_of_nonneg_left ha hh.le, mul_le_mul_of_nonneg_left hb (sq_nonneg h)]
  have hx1 : |x| ≤ 1 := by linarith
  have hpert := exp_linear_perturbation x r hx1 hr1
  have hp6 : h ^ 6 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hr2 : r ^ 2 ≤ C ^ 2 * h ^ 4 := by
    have hs := pow_le_pow_left₀ (abs_nonneg r) hr 2
    rw [sq_abs] at hs
    nlinarith [mul_le_mul_of_nonneg_left hp6 (sq_nonneg C)]
  have hxr : |x| * |r| ≤ 6 * C * h ^ 4 := by
    calc
      _ ≤ (6 * h) * (C * h ^ 3) := mul_le_mul hx hr (abs_nonneg r) (by positivity)
      _ = _ := by ring
  have hpert' : |Real.exp (x + r) - Real.exp x - r| ≤ (3 * C ^ 2 + 12 * C) * h ^ 4 := by
    nlinarith
  have hbase := exp_twoJet_cubic_error h a b hh hh12 ha hb
  have harg : h * Real.cos (3 * t) + u t = x + r := by dsimp [x, r, a]; ring
  have he : Real.exp (h * Real.cos (3 * t) + u t) -
      (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) + r) =
      (Real.exp (x + r) - Real.exp x - r) +
        (Real.exp x - (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6))) := by
    rw [harg]
    ring
  change |Real.exp (h * Real.cos (3 * t) + u t) -
      (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) + r)| ≤ K * h ^ 4
  rw [he]
  have ht := abs_add_le (Real.exp (x + r) - Real.exp x - r)
    (Real.exp x - (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6)))
  dsimp only [x] at hpert' ht
  dsimp only [K]
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
