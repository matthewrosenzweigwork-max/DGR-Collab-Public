import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMoments
import DGPS.Frontier.STR029.T44

/-! Actual low-jet Fourier integrals used in the ordinary-root moment limit.
These are exact trigonometric integral identities. The subsequent Euler estimates
consume the genuine same-branch C1 remainder, not a formal Taylor-series premise. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Exact Fourier integrals of the two proved spatial derivative jets. -/
theorem ordinaryRoot_derivativeJet_moments :
    normInt_STR02933 (fun t => (-2 * Real.sin t) ^ 2 * Real.cos (3 * t)) = 0 ∧
    normInt_STR02933 (fun t => (-2 * Real.sin t) *
      (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)) *
        Real.cos (3 * t)) = -(16 / 15 : ℝ) ∧
    normInt_STR02933 (fun t => Real.sin (3 * t) * (-2 * Real.sin t) * Real.cos (3 * t)) = 0 ∧
    normInt_STR02933 (fun t => Real.sin (3 * t) *
      (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)) *
        Real.cos (3 * t)) = 0 := by
  have hcos3 : normInt_STR02933 (fun t => Real.cos (3 * t)) = 0 := by
    simpa using normInt_cos_nat_STR02934 3
  have h13 : normInt_STR02933 (fun t => Real.cos t * Real.cos (3 * t)) = 0 := by
    simpa using normInt_cos_mul_cos_STR02934 1 3 (by norm_num)
  have h23 : normInt_STR02933 (fun t => Real.cos (2 * t) * Real.cos (3 * t)) = 0 := by
    simpa using normInt_cos_mul_cos_STR02934 2 3 (by norm_num)
  have h33 : normInt_STR02933 (fun t => Real.cos (3 * t) * Real.cos (3 * t)) = (1 / 2 : ℝ) := by
    simpa using normInt_cos_mul_cos_STR02934 3 3 (by norm_num)
  have h53 : normInt_STR02933 (fun t => Real.cos (5 * t) * Real.cos (3 * t)) = 0 := by
    simpa using normInt_cos_mul_cos_STR02934 5 3 (by norm_num)
  have h61 : normInt_STR02933 (fun t => Real.sin (6 * t) * Real.sin t) = 0 := by
    simpa using normInt_sin_mul_sin_STR02934 6 1 (by norm_num)
  have h62 : normInt_STR02933 (fun t => Real.sin (6 * t) * Real.sin (2 * t)) = 0 := by
    simpa using normInt_sin_mul_sin_STR02934 6 2 (by norm_num)
  have h64 : normInt_STR02933 (fun t => Real.sin (6 * t) * Real.sin (4 * t)) = 0 := by
    simpa using normInt_sin_mul_sin_STR02934 6 4 (by norm_num)
  have h12 (t : ℝ) : 2 * Real.sin t * Real.sin (2 * t) = Real.cos t - Real.cos (3 * t) := by
    have hminus := Real.cos_sub (2 * t) t
    have hplus := Real.cos_add (2 * t) t
    rw [show 2 * t - t = t by ring] at hminus
    rw [show 2 * t + t = 3 * t by ring] at hplus
    nlinarith
  have h14 (t : ℝ) : 2 * Real.sin t * Real.sin (4 * t) = Real.cos (3 * t) - Real.cos (5 * t) := by
    have hminus := Real.cos_sub (4 * t) t
    have hplus := Real.cos_add (4 * t) t
    rw [show 4 * t - t = 3 * t by ring] at hminus
    rw [show 4 * t + t = 5 * t by ring] at hplus
    nlinarith
  have h36 (t : ℝ) : Real.sin (3 * t) * Real.cos (3 * t) = Real.sin (6 * t) / 2 := by
    have ht := Real.sin_two_mul (3 * t)
    rw [show 2 * (3 * t) = 6 * t by ring] at ht
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : (fun t => (-2 * Real.sin t) ^ 2 * Real.cos (3 * t)) =
        fun t => 2 * Real.cos (3 * t) + (-2 : ℝ) * (Real.cos (2 * t) * Real.cos (3 * t)) := by
      funext t
      have hs : 4 * Real.sin t ^ 2 = 2 - 2 * Real.cos (2 * t) := by
        nlinarith [Real.cos_two_mul t, Real.sin_sq_add_cos_sq t]
      calc
        _ = (4 * Real.sin t ^ 2) * Real.cos (3 * t) := by ring
        _ = _ := by rw [hs]; ring
    rw [he, normInt_add_STR02934
      (f := fun t => 2 * Real.cos (3 * t))
      (g := fun t => (-2 : ℝ) * (Real.cos (2 * t) * Real.cos (3 * t)))
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop)),
      normInt_mul_const_STR02933, normInt_mul_const_STR02933, hcos3, h23]
    ring
  · have he : (fun t => (-2 * Real.sin t) *
        (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)) * Real.cos (3 * t)) =
        fun t => (4 / 3 : ℝ) * (Real.cos t * Real.cos (3 * t)) +
          (-(32 / 15) : ℝ) * (Real.cos (3 * t) * Real.cos (3 * t)) +
          (4 / 5 : ℝ) * (Real.cos (5 * t) * Real.cos (3 * t)) := by
      funext t
      linear_combination (4 / 3 : ℝ) * Real.cos (3 * t) * h12 t -
        (4 / 5 : ℝ) * Real.cos (3 * t) * h14 t
    rw [he, normInt_lin3_STR02935
      (u := fun t => Real.cos t * Real.cos (3 * t))
      (v := fun t => Real.cos (3 * t) * Real.cos (3 * t))
      (z := fun t => Real.cos (5 * t) * Real.cos (3 * t))
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop)), h13, h33, h53]
    ring
  · have he : (fun t => Real.sin (3 * t) * (-2 * Real.sin t) * Real.cos (3 * t)) =
        fun t => (-1 : ℝ) * (Real.sin (6 * t) * Real.sin t) := by
      funext t
      linear_combination (-2 * Real.sin t) * h36 t
    rw [he, normInt_mul_const_STR02933, h61]
    ring
  · have he : (fun t => Real.sin (3 * t) *
        (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)) * Real.cos (3 * t)) =
        fun t => (-(2 / 3) : ℝ) * (Real.sin (6 * t) * Real.sin (2 * t)) +
          (2 / 5 : ℝ) * (Real.sin (6 * t) * Real.sin (4 * t)) := by
      funext t
      linear_combination (-(4 / 3 : ℝ) * Real.sin (2 * t) +
        (4 / 5 : ℝ) * Real.sin (4 * t)) * h36 t
    rw [he, normInt_add_STR02934
      (f := fun t => (-(2 / 3) : ℝ) * (Real.sin (6 * t) * Real.sin (2 * t)))
      (g := fun t => (2 / 5 : ℝ) * (Real.sin (6 * t) * Real.sin (4 * t)))
      (integrable_continuous_STR02934 (by fun_prop))
      (integrable_continuous_STR02934 (by fun_prop)),
      normInt_mul_const_STR02933, normInt_mul_const_STR02933, h62, h64]
    ring


private theorem derivative_square_error (h l q r C : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hC : 0 ≤ C) (hl : |l| ≤ 2) (hq : |q| ≤ 3) (hr : |r| ≤ C * h ^ 3) :
    |(h * l + h ^ 2 * q + r) ^ 2 - h ^ 2 * l ^ 2 - 2 * h ^ 3 * l * q| ≤
      (9 + 10 * C + C ^ 2) * h ^ 4 := by
  have hq2 : q ^ 2 ≤ 9 := by
    have hs := pow_le_pow_left₀ (abs_nonneg q) hq 2
    norm_num only [sq_abs] at hs
    exact hs
  have hp5 : h ^ 5 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hp6 : h ^ 6 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hA : |h ^ 4 * q ^ 2| ≤ 9 * h ^ 4 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ h ^ 4 * q ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_left hq2 (pow_nonneg hh.le 4)]
  have hB : |2 * h * l * r| ≤ 4 * C * h ^ 4 := by
    calc
      _ = 2 * h * |l| * |r| := by
        simp only [abs_mul, abs_of_pos hh, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * h * 2 * (C * h ^ 3) := by gcongr
      _ = _ := by ring
  have hD : |2 * h ^ 2 * q * r| ≤ 6 * C * h ^ 4 := by
    calc
      _ = 2 * h ^ 2 * |q| * |r| := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg h), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * h ^ 2 * 3 * (C * h ^ 3) := by gcongr
      _ = 6 * C * h ^ 5 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp5 (by positivity)
  have hE : |r ^ 2| ≤ C ^ 2 * h ^ 4 := by
    rw [abs_pow]
    calc
      |r| ^ 2 ≤ (C * h ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg r) hr 2
      _ = C ^ 2 * h ^ 6 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp6 (sq_nonneg C)
  have he : (h * l + h ^ 2 * q + r) ^ 2 - h ^ 2 * l ^ 2 - 2 * h ^ 3 * l * q =
      h ^ 4 * q ^ 2 + 2 * h * l * r + 2 * h ^ 2 * q * r + r ^ 2 := by ring
  rw [he]
  have ht1 := abs_add_le (h ^ 4 * q ^ 2) (2 * h * l * r)
  have ht2 := abs_add_le (h ^ 4 * q ^ 2 + 2 * h * l * r) (2 * h ^ 2 * q * r)
  have ht3 := abs_add_le (h ^ 4 * q ^ 2 + 2 * h * l * r + 2 * h ^ 2 * q * r) (r ^ 2)
  nlinarith

/-- The actual Euler equation and the true C1 remainder determine the cubic
third-harmonic logarithmic moment with a uniform fourth-order residual. The
constant and interval precede h; no cubic Taylor coefficient is assumed. -/
theorem ordinaryRoot_cubic_logMoment_balance (D : OrdinaryRootGraphData) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ →
        let u := chartU_STR02924 D.ψ h (D.Z 0 h)
        |(16 - 2 * h ^ 2 * D.Z 0 h 2) *
            normInt_STR02933 (fun t => u t * Real.cos (3 * t)) + (32 / 15 : ℝ) * h ^ 3| ≤
          K * h ^ 4 := by
  obtain ⟨C, hC, hrem⟩ := ordinaryRoot_evenBranch_C1_expansion D
  let δ := min D.radius 1
  let K := 9 + 16 * C + C ^ 2
  refine ⟨K, δ, by dsimp [K]; positivity, lt_min D.radius_pos (by norm_num),
    min_le_left _ _, fun h hh hhd => ?_⟩
  have hhr : h ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos, hhd.trans_le (min_le_left D.radius 1)]
  have hh1 : h ≤ 1 := (hhd.trans_le (min_le_right D.radius 1)).le
  have hhR : |h| ≤ D.radius := by rw [abs_of_pos hh]; exact hhr.2.le
  let u := chartU_STR02924 D.ψ h (D.Z 0 h)
  let l : ℝ → ℝ := fun t => -2 * Real.sin t
  let q : ℝ → ℝ := fun t => -(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t)
  let r : ℝ → ℝ := fun t => deriv u t - h * l t - h ^ 2 * q t
  have hu := chartU_isC2_STR02924 D.ψ h (D.Z 0 h)
  have hdu : Continuous (deriv u) := hu.2.2.1.continuous
  have hl (t : ℝ) : |l t| ≤ 2 := by
    dsimp [l]
    simpa only [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) (by norm_num : (0 : ℝ) ≤ 2)
  have hq (t : ℝ) : |q t| ≤ 3 := by
    have ht := abs_add_le (-(4 / 3 : ℝ) * Real.sin (2 * t)) ((4 / 5 : ℝ) * Real.sin (4 * t))
    simp only [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5)] at ht
    dsimp [q]
    nlinarith [Real.abs_sin_le_one (2 * t), Real.abs_sin_le_one (4 * t)]
  have hr (t : ℝ) : |r t| ≤ C * h ^ 3 := by
    have he : r t = deriv u t -
        (-2 * h * Real.sin t + h ^ 2 *
          (-(4 / 3 : ℝ) * Real.sin (2 * t) + (4 / 5 : ℝ) * Real.sin (4 * t))) := by
      dsimp [r, l, q]; ring
    rw [he]
    simpa only [abs_of_pos hh] using (hrem h hhR t).2
  have hjet := ordinaryRoot_derivativeJet_moments
  have hL : normInt_STR02933 (fun t => l t ^ 2 * Real.cos (3 * t)) = 0 := hjet.1
  have hLQ : normInt_STR02933 (fun t => l t * q t * Real.cos (3 * t)) = -(16 / 15 : ℝ) := hjet.2.1
  have hSL : normInt_STR02933 (fun t => Real.sin (3 * t) * l t * Real.cos (3 * t)) = 0 := hjet.2.2.1
  have hSQ : normInt_STR02933 (fun t => Real.sin (3 * t) * q t * Real.cos (3 * t)) = 0 := hjet.2.2.2
  let e : ℝ → ℝ := fun t =>
    (deriv u t ^ 2 - h ^ 2 * l t ^ 2 - 2 * h ^ 3 * l t * q t) * Real.cos (3 * t)
  have he (t : ℝ) : |e t| ≤ (9 + 10 * C + C ^ 2) * h ^ 4 := by
    have hb := derivative_square_error h (l t) (q t) (r t) C hh hh1 hC (hl t) (hq t) (hr t)
    have hd : h * l t + h ^ 2 * q t + r t = deriv u t := by dsimp [r]; ring
    rw [hd] at hb
    dsimp only [e]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (3 * t)) (abs_nonneg _)).trans
      (by simpa only [mul_one] using hb)
  have heI := abs_normInt_le_STR02944 he
  have heFun : e = fun t => 1 * (deriv u t ^ 2 * Real.cos (3 * t)) +
      (-h ^ 2) * (l t ^ 2 * Real.cos (3 * t)) +
      (-2 * h ^ 3) * (l t * q t * Real.cos (3 * t)) := by
    funext t; dsimp [e]; ring
  rw [heFun, normInt_lin3_STR02935
    (u := fun t => deriv u t ^ 2 * Real.cos (3 * t))
    (v := fun t => l t ^ 2 * Real.cos (3 * t))
    (z := fun t => l t * q t * Real.cos (3 * t))
    (integrable_continuous_STR02934 (by fun_prop))
    (integrable_continuous_STR02934 (by dsimp [l]; fun_prop))
    (integrable_continuous_STR02934 (by dsimp [l, q]; fun_prop)), hL, hLQ] at heI
  have hSquare : |normInt_STR02933 (fun t => deriv u t ^ 2 * Real.cos (3 * t)) +
      (32 / 15 : ℝ) * h ^ 3| ≤ (9 + 10 * C + C ^ 2) * h ^ 4 := by
    convert heI using 1 <;> ring
  have hDriftError : |normInt_STR02933 (fun t => Real.sin (3 * t) * r t * Real.cos (3 * t))| ≤
      C * h ^ 3 := by
    apply abs_normInt_le_STR02944
    intro t
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 1 * |r t| * 1 := by
        gcongr <;> first | exact Real.abs_sin_le_one _ | exact Real.abs_cos_le_one _
      _ ≤ C * h ^ 3 := by simpa only [one_mul, mul_one] using hr t
  have hDriftFun : (fun t => Real.sin (3 * t) * deriv u t * Real.cos (3 * t)) =
      fun t => h * (Real.sin (3 * t) * l t * Real.cos (3 * t)) +
        h ^ 2 * (Real.sin (3 * t) * q t * Real.cos (3 * t)) +
        1 * (Real.sin (3 * t) * r t * Real.cos (3 * t)) := by
    funext t; dsimp [r]; ring
  have hDriftEq := congrArg normInt_STR02933 hDriftFun
  rw [normInt_lin3_STR02935
    (u := fun t => Real.sin (3 * t) * l t * Real.cos (3 * t))
    (v := fun t => Real.sin (3 * t) * q t * Real.cos (3 * t))
    (z := fun t => Real.sin (3 * t) * r t * Real.cos (3 * t))
    (integrable_continuous_STR02934 (by dsimp [l]; fun_prop))
    (integrable_continuous_STR02934 (by dsimp [q]; fun_prop))
    (integrable_continuous_STR02934 (by dsimp [r, l, q]; fun_prop)), hSL, hSQ] at hDriftEq
  have hDrift : |normInt_STR02933 (fun t => Real.sin (3 * t) * deriv u t * Real.cos (3 * t))| ≤
      C * h ^ 3 := by
    simp only [mul_zero, zero_add, one_mul] at hDriftEq
    rw [hDriftEq]
    exact hDriftError
  have hBal := ordinaryRoot_thirdHarmonic_balance D h hhr (0 : Fin 3)
  change (18 - 2 * (1 + h ^ 2 * D.Z 0 h 2)) *
    normInt_STR02933 (fun t => u t * Real.cos (3 * t)) =
    normInt_STR02933 (fun t => deriv u t ^ 2 * Real.cos (3 * t)) -
      6 * h * normInt_STR02933 (fun t => Real.sin (3 * t) * deriv u t * Real.cos (3 * t)) at hBal
  have hEq : (16 - 2 * h ^ 2 * D.Z 0 h 2) *
      normInt_STR02933 (fun t => u t * Real.cos (3 * t)) + (32 / 15 : ℝ) * h ^ 3 =
      (normInt_STR02933 (fun t => deriv u t ^ 2 * Real.cos (3 * t)) + (32 / 15 : ℝ) * h ^ 3) +
        (-6 * h) * normInt_STR02933 (fun t => Real.sin (3 * t) * deriv u t * Real.cos (3 * t)) := by
    linarith [hBal]
  dsimp only
  rw [hEq]
  calc
    _ ≤ |normInt_STR02933 (fun t => deriv u t ^ 2 * Real.cos (3 * t)) + (32 / 15 : ℝ) * h ^ 3| +
        |(-6 * h) * normInt_STR02933 (fun t => Real.sin (3 * t) * deriv u t * Real.cos (3 * t))| := abs_add_le _ _
    _ ≤ (9 + 10 * C + C ^ 2) * h ^ 4 + (6 * h) * (C * h ^ 3) := by
      apply add_le_add hSquare
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left hDrift (by positivity)
    _ = K * h ^ 4 := by dsimp [K]; ring

end DGPS.Examples.ThreeSpeciesCircle
