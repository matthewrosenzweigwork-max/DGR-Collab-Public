import DGPS.Circle.BesselConcavity
import DGPS.Examples.AttractiveXYTilt
import DGPS.Examples.AttractiveXYStationaryEX020
import DGPS.Analysis.BoundedPerturbation

/-!
# Uniform fold residual bound for the attractive XY model (EX026)

Real-analytic core: for `h = h_c + ε`, `0 < ε ≤ 1`, `|z| ≤ 1`, the distance of `z` to the fold point
`z_* = g(t_h) e₁` is bounded by `C_R |R_h(z)| / ε`, together with the uniform frozen LSI rate
`a0 exp(-2 M0)`, `M0 = h_c + 5`.
-/

open MeasureTheory UnitAddTorus
open DGPS DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical
open DGPS.Examples.AttractiveXYTilt DGPS.Examples.AttractiveXYStationaryEX020
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity DGPS.Circle.BesselConcavity

namespace DGPS.Examples.AttractiveXYCollapseEX026

/-- The fold function `A(u) = u - 4 g(u)`. -/
noncomputable def foldA_EX026 (u : ℝ) : ℝ := u - 4 * besselRatio u

theorem hasDerivAt_foldA_EX026 (u : ℝ) :
    HasDerivAt foldA_EX026 (1 - 4 * ratioDeriv u) u := by
  have := (hasDerivAt_id' u).sub ((hasDerivAt_ratio u).const_mul 4)
  exact this

theorem continuous_foldA_EX026 : Continuous foldA_EX026 :=
  continuous_id.sub (continuous_const.mul continuous_besselRatio)

/-- `A'(ξ) > A(ξ)/ξ`, hence `A(hi) - A(lo) ≥ (hi - lo) A(lo)/lo`. -/
theorem foldA_slope_EX026 {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo < hi) :
    (hi - lo) * (foldA_EX026 lo / lo) ≤ foldA_EX026 hi - foldA_EX026 lo := by
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope foldA_EX026
    (fun x => 1 - 4 * ratioDeriv x) hlh continuous_foldA_EX026.continuousOn
    (fun x _ => hasDerivAt_foldA_EX026 x)
  have hξ0 : 0 < ξ := hlo.trans hξ.1
  have h1 := ratioDeriv_lt_div ξ hξ0
  have h2 : besselRatio ξ / ξ < besselRatio lo / lo :=
    strictAntiOn_ratio (Set.mem_Ioi.mpr hlo) (Set.mem_Ioi.mpr hξ0) hξ.1
  have h3 : foldA_EX026 lo / lo = 1 - 4 * (besselRatio lo / lo) := by
    unfold foldA_EX026; field_simp
  have h4 : 1 - 4 * (besselRatio lo / lo) ≤ (foldA_EX026 hi - foldA_EX026 lo) / (hi - lo) := by
    rw [← hd]
    have : besselRatio ξ / ξ * ξ = besselRatio ξ := by field_simp
    nlinarith
  rw [h3]
  have hpos : 0 < hi - lo := by linarith
  rw [le_div_iff₀ hpos] at h4
  linarith

theorem fold_dist_EX026 {h M0 s t : ℝ} (hh : 0 < h) (hs : 0 < s) (ht : 0 < t)
    (hsM : s ≤ M0) (htM : t ≤ M0) (hAt : foldA_EX026 t = h)
    (hAs : h / 2 ≤ foldA_EX026 s) :
    (s - t) ^ 2 * h ^ 2 ≤ 4 * M0 ^ 2 * (foldA_EX026 s - h) ^ 2 := by
  have hM0 : 0 < M0 := hs.trans_le hsM
  rcases lt_trichotomy s t with hlt | heq | hgt
  · have hk := foldA_slope_EX026 hs hlt
    rw [hAt] at hk
    have hr : h / (2 * M0) ≤ foldA_EX026 s / s := by
      rw [div_le_div_iff₀ (by positivity) hs]
      nlinarith
    have hr' : (t - s) * (h / (2 * M0)) ≤ h - foldA_EX026 s := by
      have := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ t - s)
      linarith
    have hr'' : (t - s) * h ≤ 2 * M0 * (h - foldA_EX026 s) := by
      have e : (t - s) * (h / (2 * M0)) * (2 * M0) = (t - s) * h := by field_simp
      nlinarith
    have hn : 0 ≤ (t - s) * h := by nlinarith
    have := pow_le_pow_left₀ hn hr'' 2
    nlinarith
  · subst heq
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    positivity
  · have hk := foldA_slope_EX026 ht hgt
    rw [hAt] at hk
    have hr : h / M0 ≤ h / t := div_le_div_of_nonneg_left hh.le ht htM
    have hr' : (s - t) * (h / M0) ≤ foldA_EX026 s - h := by
      have := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ s - t)
      linarith
    have hr'' : (s - t) * h ≤ M0 * (foldA_EX026 s - h) := by
      have e : (s - t) * (h / M0) * M0 = (s - t) * h := by field_simp
      nlinarith
    have hn : 0 ≤ (s - t) * h := by nlinarith
    have hA2 : 0 ≤ foldA_EX026 s - h := by
      by_contra hc
      have hc' := lt_of_not_ge hc
      nlinarith
    have hr3 : (s - t) * h ≤ 2 * M0 * (foldA_EX026 s - h) := by nlinarith
    have := pow_le_pow_left₀ hn hr3 2
    nlinarith


theorem core_EX026 {h hc ε M0 CR t s u A : ℝ}
    (hc0 : 0 < hc) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hh : h = hc + ε) (hM0 : M0 = hc + 5)
    (hCR1 : 8 ≤ CR) (hCR2 : 16 / hc ≤ CR) (hCR3 : (2 + Real.sqrt 2) * M0 / hc ≤ CR)
    (hs0 : 0 ≤ s) (hsM : s ≤ M0) (htM : t ≤ M0)
    (hu1 : u ≤ 1) (hu2 : -1 ≤ u) (hA : -hc ≤ A)
    (hDd : (s - t) ^ 2 + 2 * t * s * (1 - u) ≤ 64)
    (hkey : h / 2 ≤ A → (s - t) ^ 2 * h ^ 2 ≤ 4 * M0 ^ 2 * (A - h) ^ 2) :
    (s - t) ^ 2 + 2 * t * s * (1 - u) ≤ (CR / ε) ^ 2 * (A ^ 2 - 2 * h * A * u + h ^ 2) := by
  have hCRpos : 0 < CR := by linarith
  have hK : CR ≤ CR / ε := (le_div_iff₀ hε0).2 (by nlinarith)
  have hKε : (CR / ε) ^ 2 * ε ^ 2 = CR ^ 2 := by field_simp
  have hhpos : 0 < h := by rw [hh]; linarith
  have hKpos : 0 < CR / ε := hCRpos.trans_le hK
  have hK2 : CR ^ 2 ≤ (CR / ε) ^ 2 := pow_le_pow_left₀ hCRpos.le hK 2
  rcases lt_or_ge A 0 with hA0 | hA0
  · have hP : ε ^ 2 ≤ A ^ 2 - 2 * h * A * u + h ^ 2 := by
      have h1 : 0 ≤ h * (-A) * (u + 1) := by
        apply mul_nonneg (mul_nonneg hhpos.le (by linarith)) (by linarith)
      have h2 : ε ≤ A + h := by linarith
      nlinarith
    have : CR ^ 2 ≤ (CR / ε) ^ 2 * (A ^ 2 - 2 * h * A * u + h ^ 2) := by
      rw [← hKε]
      exact mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  · rcases lt_or_ge A (h / 2) with hA1 | hA1
    · have hP : (h / 2) ^ 2 ≤ A ^ 2 - 2 * h * A * u + h ^ 2 := by
        have h1 : 0 ≤ h * A * (1 - u) := mul_nonneg (mul_nonneg hhpos.le hA0) (by linarith)
        nlinarith
      have hCRhc : 16 ≤ CR * hc := by
        have := (div_le_iff₀ hc0).1 hCR2
        linarith
      have hh2 : hc ≤ h := by rw [hh]; linarith
      have hch : 16 ≤ CR * h := by nlinarith
      have h3 : 64 ≤ CR ^ 2 * (h / 2) ^ 2 := by nlinarith
      have : CR ^ 2 * (h / 2) ^ 2 ≤ (CR / ε) ^ 2 * (A ^ 2 - 2 * h * A * u + h ^ 2) :=
        mul_le_mul hK2 hP (by positivity) (by positivity)
      linarith
    · have hk := hkey hA1
      have hP : (A - h) ^ 2 + h ^ 2 * (1 - u) ≤ A ^ 2 - 2 * h * A * u + h ^ 2 := by
        have h1 : 0 ≤ (2 * A - h) * (h * (1 - u)) :=
          mul_nonneg (by linarith) (mul_nonneg hhpos.le (by linarith))
        nlinarith
      have hts : t * s ≤ M0 ^ 2 := by nlinarith
      have hu0 : 0 ≤ 1 - u := by linarith
      have e1 : 2 * t * s * (1 - u) * h ^ 2 ≤ 2 * M0 ^ 2 * (h ^ 2 * (1 - u)) := by
        have := mul_le_mul_of_nonneg_right hts (mul_nonneg (by positivity : (0:ℝ) ≤ h ^ 2) hu0)
        nlinarith
      have e2 : ((s - t) ^ 2 + 2 * t * s * (1 - u)) * h ^ 2 ≤
          4 * M0 ^ 2 * (A ^ 2 - 2 * h * A * u + h ^ 2) := by
        have hM2 : 0 ≤ M0 ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hP (by positivity : (0:ℝ) ≤ 4 * M0 ^ 2)
        have h4 : 0 ≤ M0 ^ 2 * (h ^ 2 * (1 - u)) := mul_nonneg hM2 (mul_nonneg (by positivity) hu0)
        nlinarith
      have hKh : 2 * M0 ≤ (CR / ε) * h := by
        have h1 : (2 + Real.sqrt 2) * M0 ≤ CR * hc := by
          have := (div_le_iff₀ hc0).1 hCR3
          linarith
        have hM0p : 0 ≤ M0 := by rw [hM0]; linarith
        have h2 : 2 * M0 ≤ (2 + Real.sqrt 2) * M0 :=
          mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg 2]) hM0p
        have hh2 : hc ≤ h := by rw [hh]; linarith
        have : CR * hc ≤ (CR / ε) * h := mul_le_mul hK hh2 hc0.le hKpos.le
        linarith
      have h5 : 4 * M0 ^ 2 ≤ ((CR / ε) * h) ^ 2 := by
        calc 4 * M0 ^ 2 = (2 * M0) ^ 2 := by ring
          _ ≤ _ := pow_le_pow_left₀ (by rw [hM0]; linarith) hKh 2
      have hPn : 0 ≤ A ^ 2 - 2 * h * A * u + h ^ 2 := by
        have : 0 ≤ (A - h) ^ 2 + h ^ 2 * (1 - u) :=
          add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hu0)
        linarith
      have e3 : ((s - t) ^ 2 + 2 * t * s * (1 - u)) * h ^ 2 ≤
          (CR / ε) ^ 2 * (A ^ 2 - 2 * h * A * u + h ^ 2) * h ^ 2 := by
        have := mul_le_mul_of_nonneg_right h5 hPn
        calc _ ≤ 4 * M0 ^ 2 * (A ^ 2 - 2 * h * A * u + h ^ 2) := e2
          _ ≤ _ := this
          _ = _ := by ring
      exact le_of_mul_le_mul_right e3 (by positivity)



theorem sqrt_half_EX026 (a b : ℝ) :
    2 * Real.sqrt ((a / 2) ^ 2 + (b / 2) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) := by
  have : a ^ 2 + b ^ 2 = 2 ^ 2 * ((a / 2) ^ 2 + (b / 2) ^ 2) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

theorem partition_pos_EX026 (a b : ℝ) (hb : 0 < a ^ 2 + b ^ 2) :
    ∫ y, Real.exp (xyTrig a b 0 y) ∂haar 1 = besselI 0 (Real.sqrt (a ^ 2 + b ^ 2)) := by
  have hb' : 0 < (a / 2) ^ 2 + (b / 2) ^ 2 := by nlinarith
  have := integral_exp_rot_xyc (a / 2) (b / 2) hb'
  rw [sqrt_half_EX026] at this
  rw [← this]
  congr 1
  funext x
  congr 1
  simp only [xyTrig]
  ring

theorem mean_proj_EX026 (a b : ℝ) (hb : 0 < a ^ 2 + b ^ 2) :
    a * xyZ1 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) +
      b * xyZ2 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) =
      Real.sqrt (a ^ 2 + b ^ 2) * besselRatio (Real.sqrt (a ^ 2 + b ^ 2)) := by
  set μ : Measure (Torus 1) := (xyBivariateLaw_EX023 a b : Measure (Torus 1)) with hμ
  have i1 := (integrable_xyMode_re μ).const_mul a
  have i2 := (integrable_xyMode_im μ).const_mul b
  have e : a * xyZ1 μ + b * xyZ2 μ = ∫ x, (a * (xyMode x).re + b * (xyMode x).im) ∂μ := by
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul]; rfl
  rw [e]
  change (∫ x, (a * (xyMode x).re + b * (xyMode x).im) ∂(haar 1).tilted (xyTrig a b 0)) = _
  rw [integral_tilted]
  simp only [smul_eq_mul]
  rw [partition_pos_EX026 a b hb]
  have hb' : 0 < (a / 2) ^ 2 + (b / 2) ^ 2 := by nlinarith
  have h1 := integral_firstTilt_EX020 (a / 2) (b / 2) hb'
  rw [sqrt_half_EX026] at h1
  have h2 : ∫ x, Real.exp (xyTrig a b 0 x) / besselI 0 (Real.sqrt (a ^ 2 + b ^ 2)) *
      (a * (xyMode x).re + b * (xyMode x).im) ∂haar 1 =
      (2 * ∫ x, Real.exp (2 * (a / 2 * (xyMode x).re + b / 2 * (xyMode x).im)) *
        (a / 2 * (xyMode x).re + b / 2 * (xyMode x).im) ∂haar 1) /
          besselI 0 (Real.sqrt (a ^ 2 + b ^ 2)) := by
    rw [← integral_const_mul, ← integral_div]
    congr 1
    funext x
    simp only [xyTrig]
    ring_nf
  rw [h2]
  have h3 : 2 * Real.sqrt ((a / 2) ^ 2 + (b / 2) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) :=
    sqrt_half_EX026 a b
  rw [h1]
  calc 2 * (Real.sqrt ((a / 2) ^ 2 + (b / 2) ^ 2) * besselI 1 (Real.sqrt (a ^ 2 + b ^ 2))) /
        besselI 0 (Real.sqrt (a ^ 2 + b ^ 2))
      = (2 * Real.sqrt ((a / 2) ^ 2 + (b / 2) ^ 2)) *
        (besselI 1 (Real.sqrt (a ^ 2 + b ^ 2)) / besselI 0 (Real.sqrt (a ^ 2 + b ^ 2))) := by ring
    _ = _ := by rw [h3]; rfl


theorem polar_EX026 {w1 w2 s u v A : ℝ} (hs0 : 0 ≤ s) (hs2 : s ^ 2 = w1 ^ 2 + w2 ^ 2)
    (hu : u = w1 / s) (hv : v = w2 / s) (hA0 : s = 0 → A = 0) :
    w1 = s * u ∧ w2 = s * v ∧ u ^ 2 + v ^ 2 ≤ 1 ∧ A ^ 2 * (u ^ 2 + v ^ 2) = A ^ 2 := by
  rcases hs0.eq_or_lt with h0 | h0
  · have h1 : w1 = 0 := by
      rw [← h0] at hs2; nlinarith [sq_nonneg w1, sq_nonneg w2]
    have h2 : w2 = 0 := by
      rw [← h0] at hs2; nlinarith [sq_nonneg w1, sq_nonneg w2]
    have e1 : u = 0 := by rw [hu, h1]; simp
    have e2 : v = 0 := by rw [hv, h2]; simp
    refine ⟨by rw [h1, ← h0]; simp, by rw [h2, ← h0]; simp, ?_, ?_⟩
    · rw [e1, e2]; norm_num
    · rw [hA0 h0.symm]; ring
  · have e : u ^ 2 + v ^ 2 = 1 := by
      rw [hu, hv]; field_simp; linarith
    refine ⟨by rw [hu]; field_simp, by rw [hv]; field_simp, e.le, ?_⟩
    rw [e, mul_one]

theorem ident_P_EX026 {h z1 z2 T1 T2 w1 w2 s u v A gs : ℝ} (hw1 : w1 = h + 4 * z1)
    (hw2 : w2 = 4 * z2) (hwu : w1 = s * u) (hwv : w2 = s * v) (hAd : 4 * gs = s - A)
    (huv : A ^ 2 * (u ^ 2 + v ^ 2) = A ^ 2) (hT1 : T1 = u * gs) (hT2 : T2 = v * gs) :
    16 * ((z1 - T1) ^ 2 + (z2 - T2) ^ 2) = A ^ 2 - 2 * h * A * u + h ^ 2 := by
  have e1 : 4 * (z1 - T1) = u * A - h := by
    rw [hT1]
    have : 4 * (u * gs) = u * (s - A) := by rw [← hAd]; ring
    have h4 : 4 * z1 = w1 - h := by rw [hw1]; ring
    rw [mul_sub, this, h4, hwu]; ring
  have e2 : 4 * (z2 - T2) = v * A := by
    rw [hT2]
    have : 4 * (v * gs) = v * (s - A) := by rw [← hAd]; ring
    have h4 : 4 * z2 = w2 := hw2.symm
    rw [mul_sub, this, h4, hwv]; ring
  have : 16 * ((z1 - T1) ^ 2 + (z2 - T2) ^ 2) =
      (4 * (z1 - T1)) ^ 2 + (4 * (z2 - T2)) ^ 2 := by ring
  rw [this, e1, e2]
  linear_combination huv

theorem ident_D_EX026 {h z1 z2 t gt w1 w2 s u : ℝ} (hte : t = 4 * gt + h)
    (hw1 : w1 = h + 4 * z1) (hw2 : w2 = 4 * z2) (hwu : w1 = s * u)
    (hs2 : s ^ 2 = w1 ^ 2 + w2 ^ 2) :
    16 * ((z1 - gt) ^ 2 + z2 ^ 2) = (s - t) ^ 2 + 2 * t * s * (1 - u) := by
  have e1 : 4 * (z1 - gt) = w1 - t := by rw [hw1]; linarith
  have : 16 * ((z1 - gt) ^ 2 + z2 ^ 2) = (4 * (z1 - gt)) ^ 2 + (4 * z2) ^ 2 := by ring
  rw [this, e1, ← hw2]
  rw [hwu] at hs2 ⊢
  have : w2 ^ 2 = s ^ 2 - (s * u) ^ 2 := by linarith
  rw [this]; ring

theorem sM_bound_EX026 {hc ε h z1 z2 w1 w2 s : ℝ} (hc0 : 0 < hc) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hh : h = hc + ε) (hz : z1 ^ 2 + z2 ^ 2 ≤ 1) (hw1 : w1 = h + 4 * z1) (hw2 : w2 = 4 * z2)
    (hs2 : s ^ 2 = w1 ^ 2 + w2 ^ 2) : s ≤ hc + 5 := by
  have hz1 : z1 ≤ 1 := by
    have : z1 ^ 2 ≤ 1 := by linarith [sq_nonneg z2]
    exact (abs_le.1 ((sq_le_one_iff_abs_le_one z1).1 this)).2
  have hhpos : 0 < h := by rw [hh]; linarith
  have e : s ^ 2 = h ^ 2 + 8 * h * z1 + 16 * (z1 ^ 2 + z2 ^ 2) := by
    rw [hs2, hw1, hw2]; ring
  have h3 : 8 * h * z1 ≤ 8 * h := by
    have := mul_le_mul_of_nonneg_left hz1 (by linarith : (0:ℝ) ≤ 8 * h)
    linarith
  have h4 : s ^ 2 ≤ (h + 4) ^ 2 := by nlinarith
  have h5 : h + 4 ≤ hc + 5 := by rw [hh]; linarith
  have h6 : s ≤ h + 4 := abs_le_of_sq_le_sq' h4 (by linarith) |>.2
  linarith

theorem D2_bound_EX026 {z1 z2 gt : ℝ} (hz : z1 ^ 2 + z2 ^ 2 ≤ 1) (hg0 : 0 < gt) (hg1 : gt < 1) :
    (z1 - gt) ^ 2 + z2 ^ 2 ≤ 4 := by
  have h1 : (z1 - gt) ^ 2 ≤ 2 * z1 ^ 2 + 2 * gt ^ 2 := by
    have := sq_nonneg (z1 + gt)
    calc (z1 - gt) ^ 2 = 2 * z1 ^ 2 + 2 * gt ^ 2 - (z1 + gt) ^ 2 := by ring
      _ ≤ _ := by linarith
  have h2 : gt ^ 2 ≤ 1 := by
    have : gt ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hg0.le hg1.le 2
    linarith
  have h3 : z2 ^ 2 ≤ 1 := by linarith [sq_nonneg z1]
  have h4 : z1 ^ 2 ≤ 1 := by linarith [sq_nonneg z2]
  linarith

/-- Real core with all auxiliary quantities explicit. -/
theorem residual_abs_EX026 {hc ε h CR t z1 z2 T1 T2 w1 w2 s gs gt : ℝ} (hc0 : 0 < hc)
    (hfold : ∀ x : ℝ, 0 ≤ x → 4 * besselRatio x - x ≤ hc)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hh : h = hc + ε)
    (hCR1 : 8 ≤ CR) (hCR2 : 16 / hc ≤ CR) (hCR3 : (2 + Real.sqrt 2) * (hc + 5) / hc ≤ CR)
    (ht : 0 < t) (hgt : gt = besselRatio t) (hte : t = 4 * gt + h)
    (hz : z1 ^ 2 + z2 ^ 2 ≤ 1)
    (hw1 : w1 = h + 4 * z1) (hw2 : w2 = 4 * z2) (hs0 : 0 ≤ s) (hs2 : s ^ 2 = w1 ^ 2 + w2 ^ 2)
    (hgs : gs = besselRatio s) (hT1 : T1 = w1 * gs / s) (hT2 : T2 = w2 * gs / s) :
    (z1 - gt) ^ 2 + z2 ^ 2 ≤ (CR / ε) ^ 2 * ((z1 - T1) ^ 2 + (z2 - T2) ^ 2) := by
  have hhpos : 0 < h := by rw [hh]; linarith
  have hgt0 : 0 < gt := by rw [hgt]; exact besselRatio_pos t ht
  have hgt1 : gt < 1 := by rw [hgt]; exact besselRatio_lt_one t
  have hsM : s ≤ hc + 5 := sM_bound_EX026 hc0 hε0 hε1 hh hz hw1 hw2 hs2
  have htM : t ≤ hc + 5 := by linarith
  obtain ⟨A, hA⟩ : ∃ A, A = foldA_EX026 s := ⟨_, rfl⟩
  have hAd : 4 * gs = s - A := by rw [hA, hgs]; simp only [foldA_EX026]; ring
  have hAhc : -hc ≤ A := by have := hfold s hs0; rw [hA]; simp only [foldA_EX026]; linarith
  have hA0 : s = 0 → A = 0 := by
    intro h0; rw [hA, h0]; simp [foldA_EX026, ratio_zero]
  obtain ⟨u, hu⟩ : ∃ u, u = w1 / s := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = w2 / s := ⟨_, rfl⟩
  obtain ⟨hwu, hwv, huv1, huv⟩ := polar_EX026 hs0 hs2 hu hv hA0
  have hu_abs : |u| ≤ 1 := (sq_le_one_iff_abs_le_one u).1 (by linarith [sq_nonneg v])
  have hu1 : u ≤ 1 := (abs_le.1 hu_abs).2
  have hu2 : -1 ≤ u := (abs_le.1 hu_abs).1
  have hT1' : T1 = u * gs := by rw [hT1, hu]; ring
  have hT2' : T2 = v * gs := by rw [hT2, hv]; ring
  have hP := ident_P_EX026 hw1 hw2 hwu hwv hAd huv hT1' hT2'
  have hD := ident_D_EX026 hte hw1 hw2 hwu hs2
  have hD2 := D2_bound_EX026 hz hgt0 hgt1
  have hkey : h / 2 ≤ A → (s - t) ^ 2 * h ^ 2 ≤ 4 * (hc + 5) ^ 2 * (A - h) ^ 2 := by
    intro hA2
    have hspos : 0 < s := by
      rcases hs0.eq_or_lt with h0 | h0
      · exfalso
        have := hA0 h0.symm
        linarith
      · exact h0
    have hAt : foldA_EX026 t = h := by simp only [foldA_EX026]; rw [← hgt]; linarith
    have := fold_dist_EX026 hhpos hspos ht hsM htM hAt (by rw [← hA]; exact hA2)
    rwa [← hA] at this
  have hcore := core_EX026 (h := h) (hc := hc) (ε := ε) (M0 := hc + 5) (CR := CR) (t := t) (s := s)
    (u := u) (A := A) hc0 hε0 hε1 hh rfl hCR1 hCR2 hCR3 hs0 hsM htM hu1 hu2 hAhc
    (by linarith) hkey
  rw [← hD, ← hP] at hcore
  linarith


theorem mean_closed_EX026 (a b : ℝ) :
    xyZ1 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) =
        a * besselRatio (Real.sqrt (a ^ 2 + b ^ 2)) / Real.sqrt (a ^ 2 + b ^ 2) ∧
      xyZ2 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) =
        b * besselRatio (Real.sqrt (a ^ 2 + b ^ 2)) / Real.sqrt (a ^ 2 + b ^ 2) := by
  by_cases hb : 0 < a ^ 2 + b ^ 2
  · have hr : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.2 hb
    have hr2 : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hb.le
    have hp := mean_proj_EX026 a b hb
    have ht := bivariate_torque_EX023 a b
    generalize Real.sqrt (a ^ 2 + b ^ 2) = r at hr hr2 hp ⊢
    generalize xyZ1 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) = Z1 at hp ht ⊢
    generalize xyZ2 (xyBivariateLaw_EX023 a b : Measure (Torus 1)) = Z2 at hp ht ⊢
    generalize besselRatio r = g at hp ⊢
    constructor
    · rw [eq_div_iff hr.ne']
      apply mul_right_cancel₀ hr.ne'
      linear_combination a * hp - b * ht + Z1 * hr2
    · rw [eq_div_iff hr.ne']
      apply mul_right_cancel₀ hr.ne'
      linear_combination b * hp + a * ht + Z2 * hr2
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    subst ha hb0
    have h1 : xyZ1 (xyBivariateLaw_EX023 0 0 : Measure (Torus 1)) = 0 :=
      (law_cos_EX023 0).trans ratio_zero
    have h2 : xyZ2 (xyBivariateLaw_EX023 0 0 : Measure (Torus 1)) = 0 := law_sin_EX023 0
    refine ⟨?_, ?_⟩
    · simpa using h1
    · simpa using h2

theorem frozen_measure_EX026 (a b : ℝ) :
    (xyFrozen a b).measure = (xyBivariateLaw_EX023 a b : Measure (Torus 1)) := rfl

theorem frozen_mean_EX026 (a b : ℝ) :
    xyZ1 (xyFrozen a b).measure =
        a * besselRatio (Real.sqrt (a ^ 2 + b ^ 2)) / Real.sqrt (a ^ 2 + b ^ 2) ∧
      xyZ2 (xyFrozen a b).measure =
        b * besselRatio (Real.sqrt (a ^ 2 + b ^ 2)) / Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [frozen_measure_EX026]
  exact mean_closed_EX026 a b

theorem sqrt_scale_EX026 {D N c : ℝ} (hc : 0 ≤ c) (h : D ≤ c ^ 2 * N) :
    Real.sqrt D ≤ c * Real.sqrt N := by
  calc Real.sqrt D ≤ Real.sqrt (c ^ 2 * N) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt N := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

theorem residual_sqrt_EX026 {hc ε CR t z1 z2 : ℝ} (hc0 : 0 < hc)
    (hfold : ∀ x : ℝ, 0 ≤ x → 4 * besselRatio x - x ≤ hc)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hCR1 : 8 ≤ CR) (hCR2 : 16 / hc ≤ CR) (hCR3 : (2 + Real.sqrt 2) * (hc + 5) / hc ≤ CR)
    (ht : 0 < t) (hte : t = 4 * besselRatio t + (hc + ε)) (hz : z1 ^ 2 + z2 ^ 2 ≤ 1) :
    Real.sqrt ((z1 - besselRatio t) ^ 2 + z2 ^ 2) ≤
      CR * Real.sqrt ((z1 - xyZ1 (xyFrozen (hc + ε + 4 * z1) (4 * z2)).measure) ^ 2 +
        (z2 - xyZ2 (xyFrozen (hc + ε + 4 * z1) (4 * z2)).measure) ^ 2) / ε := by
  obtain ⟨hm1, hm2⟩ := frozen_mean_EX026 (hc + ε + 4 * z1) (4 * z2)
  rw [hm1, hm2]
  have hs2 : Real.sqrt ((hc + ε + 4 * z1) ^ 2 + (4 * z2) ^ 2) ^ 2 =
      (hc + ε + 4 * z1) ^ 2 + (4 * z2) ^ 2 := Real.sq_sqrt (by positivity)
  have key := residual_abs_EX026 (hc := hc) (ε := ε) (h := hc + ε) (CR := CR) (t := t)
    (z1 := z1) (z2 := z2) (w1 := hc + ε + 4 * z1) (w2 := 4 * z2)
    (s := Real.sqrt ((hc + ε + 4 * z1) ^ 2 + (4 * z2) ^ 2))
    (gs := besselRatio (Real.sqrt ((hc + ε + 4 * z1) ^ 2 + (4 * z2) ^ 2))) (gt := besselRatio t)
    hc0 hfold hε0 hε1 rfl hCR1 hCR2 hCR3 ht rfl hte hz rfl rfl (Real.sqrt_nonneg _) hs2 rfl rfl rfl
  have hCε : 0 ≤ CR / ε := div_nonneg (by linarith) hε0.le
  exact (sqrt_scale_EX026 hCε key).trans (le_of_eq (by ring))

/-! ### Oscillation bounds -/

theorem xyTrig_abs_le_EX026 (a b : ℝ) (x : Torus 1) :
    |xyTrig a b 0 x| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hn : (xyMode x).re ^ 2 + (xyMode x).im ^ 2 = 1 := by
    have h1 := xyMode_norm x
    have h2 : ‖xyMode x‖ ^ 2 = (xyMode x).re * (xyMode x).re + (xyMode x).im * (xyMode x).im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [h1] at h2
    nlinarith
  apply Real.abs_le_sqrt
  simp only [xyTrig, add_zero]
  have : (a * (xyMode x).re + b * (xyMode x).im) ^ 2 + (a * (xyMode x).im - b * (xyMode x).re) ^ 2 =
      (a ^ 2 + b ^ 2) * ((xyMode x).re ^ 2 + (xyMode x).im ^ 2) := by ring
  rw [hn, mul_one] at this
  linarith [sq_nonneg (a * (xyMode x).im - b * (xyMode x).re)]

theorem xyFrozen_lsi_EX026 {hc ε z1 z2 : ℝ} (hc0 : 0 < hc) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hz : z1 ^ 2 + z2 ^ 2 ≤ 1) :
    ENNReal.ofReal (a0 * Real.exp (-(2 * (hc + 5)))) ≤
      ordinaryLSRate (xyFrozen (hc + ε + 4 * z1) (4 * z2)) := by
  have hsM : Real.sqrt ((hc + ε + 4 * z1) ^ 2 + (4 * z2) ^ 2) ≤ hc + 5 :=
    sM_bound_EX026 hc0 hε0 hε1 rfl hz rfl rfl (Real.sq_sqrt (by positivity))
  refine boundedPerturbation_lsi (xyFrozen (hc + ε + 4 * z1) (4 * z2))
    (fun x => -xyTrig (hc + ε + 4 * z1) (4 * z2) 0 x) (xyPartition (hc + ε + 4 * z1) (4 * z2))
    (2 * (hc + 5)) (Filter.Eventually.of_forall fun x => ?_) (fun x y => ?_)
  · simp [xyFrozen]
  · have h1 := (abs_le.1 (xyTrig_abs_le_EX026 (hc + ε + 4 * z1) (4 * z2) y)).2
    have h2 := (abs_le.1 (xyTrig_abs_le_EX026 (hc + ε + 4 * z1) (4 * z2) x)).1
    linarith

open DGPS.Models in
theorem attractiveXY_oscillation_EX026 {κ h : ℝ} (hκ : 0 ≤ κ) (hh : 0 ≤ h) :
    totalOscillation (attractiveXY κ h) ≤ 2 * h + 2 * κ := by
  have hV : potentialOscillation (attractiveXY κ h) ≤ 2 * h := by
    unfold potentialOscillation
    have h1 : sSup (Set.range (attractiveXY κ h).V) ≤ h := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨x, rfl⟩
      have := abs_xyMode_re_le x
      have h3 := mul_le_mul_of_nonneg_left (abs_le.1 this).1 hh
      show -h * (xyMode x).re ≤ h
      linarith
    have h2 : -h ≤ sInf (Set.range (attractiveXY κ h).V) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨x, rfl⟩
      have := abs_xyMode_re_le x
      have h3 := mul_le_mul_of_nonneg_left (abs_le.1 this).2 hh
      show -h ≤ -h * (xyMode x).re
      linarith
    linarith
  have hW : interactionOscillation (attractiveXY κ h) ≤ 2 * κ := by
    unfold interactionOscillation
    have h1 : sSup (Set.range fun p : Torus 1 × Torus 1 => (attractiveXY κ h).W p.1 p.2) ≤ 2 * κ := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨x, rfl⟩
      have := abs_xyMode_re_le (x.1 - x.2)
      have h3 := mul_le_mul_of_nonneg_left (abs_le.1 this).1 hκ
      show κ * (1 - (xyMode (x.1 - x.2)).re) ≤ 2 * κ
      linarith
    have h2 : 0 ≤ sInf (Set.range fun p : Torus 1 × Torus 1 => (attractiveXY κ h).W p.1 p.2) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨x, rfl⟩
      have := abs_xyMode_re_le (x.1 - x.2)
      have h3 := mul_le_mul_of_nonneg_left (abs_le.1 this).2 hκ
      show 0 ≤ κ * (1 - (xyMode (x.1 - x.2)).re)
      linarith
    linarith
  unfold totalOscillation
  linarith

open DGPS.Models in
theorem frozenInf_lsi_EX026 {hc ε : ℝ} (hc0 : 0 < hc) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ENNReal.ofReal (a0 * Real.exp (-(2 * (hc + 5)))) ≤ frozenLSRateInf (attractiveXY 4 (hc + ε)) := by
  refine le_trans ?_ (def025_frozenLSRateInf_lower_bound (attractiveXY 4 (hc + ε)))
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ a0_pos.le
  apply Real.exp_le_exp.2
  have := attractiveXY_oscillation_EX026 (κ := 4) (h := hc + ε) (by norm_num) (by linarith)
  linarith

end DGPS.Examples.AttractiveXYCollapseEX026

namespace DGPS.Examples

open DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCollapseEX026
open DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity

/-- **EX026 (uniform fold residual bound).** Let `s > 0` solve `g'(s) = 1/4` and
`h_c = 4 g(s) - s` (the fold parameter of `strict_bessel_concavity_and_fold_parameter`), `κ = 4`,
`M0 = h_c + 5`, `C_R = max {8, 16/h_c, (2+√2) M0/h_c}`.  Then `h_c > 0` and, for every
`0 < ε ≤ 1` (`h = h_c + ε`): (1) `t = 4 g(t) + h` has a unique positive root; (2) for every
positive root `t_h` and every `z` in the closed unit disk, with `T_h(z) = ∫ φ p_{h,z} dm` the mean of
the frozen law `p_{h,z} ∝ exp((h e₁ + 4 z)·φ)`, one has
`|z - g(t_h) e₁| ≤ C_R |z - T_h(z)| / ε`; (3) every frozen one-site law has log-Sobolev rate at least
`a0 exp(-2 M0)`, for the frozen laws `p_{h,z}`, for every `frozenGibbs` of the attractive XY model
and for `frozenLSRateInf`. -/
theorem uniform_fold_residual_bound {s hc : ℝ} (hs : 0 < s)
    (hd : deriv besselRatio s = 1 / 4) (hhc : hc = 4 * besselRatio s - s) :
    0 < hc ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃! t : ℝ, 0 < t ∧ t = 4 * besselRatio t + (hc + ε)) ∧
    (∀ ε z1 z2 t : ℝ, 0 < ε → ε ≤ 1 → z1 ^ 2 + z2 ^ 2 ≤ 1 → 0 < t →
      t = 4 * besselRatio t + (hc + ε) →
      Real.sqrt ((z1 - besselRatio t) ^ 2 + z2 ^ 2) ≤
        max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc)) *
          Real.sqrt ((z1 - xyZ1 (xyFrozen (hc + ε + 4 * z1) (4 * z2)).measure) ^ 2 +
            (z2 - xyZ2 (xyFrozen (hc + ε + 4 * z1) (4 * z2)).measure) ^ 2) / ε) ∧
    (∀ ε z1 z2 : ℝ, 0 < ε → ε ≤ 1 → z1 ^ 2 + z2 ^ 2 ≤ 1 →
      ENNReal.ofReal (DGPS.a0 * Real.exp (-(2 * (hc + 5)))) ≤
        DGPS.ordinaryLSRate (xyFrozen (hc + ε + 4 * z1) (4 * z2))) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ENNReal.ofReal (DGPS.a0 * Real.exp (-(2 * (hc + 5)))) ≤
          DGPS.frozenLSRateInf (attractiveXY 4 (hc + ε)) ∧
        ∀ ν : ProbabilityMeasure (DGPS.Torus 1),
          ENNReal.ofReal (DGPS.a0 * Real.exp (-(2 * (hc + 5)))) ≤
            DGPS.ordinaryLSRate (DGPS.frozenGibbs (attractiveXY 4 (hc + ε)) ν)) := by
  obtain ⟨_, _, _, hfd⟩ := strict_bessel_concavity_and_fold_parameter
  obtain ⟨hmax, hhalf⟩ := hfd s hs hd
  have hc0 : 0 < hc := by rw [hhc]; linarith
  have hfold : ∀ x : ℝ, 0 ≤ x → 4 * besselRatio x - x ≤ hc := by
    intro x hx
    by_cases hxs : x = s
    · rw [hxs, hhc]
    · rw [hhc]; exact (hmax x hx hxs).le
  refine ⟨hc0, fun ε hε0 hε1 => positive_root_unique_EX023 (by norm_num) (by linarith),
    fun ε z1 z2 t hε0 hε1 hz ht hte => ?_, fun ε z1 z2 hε0 hε1 hz =>
      xyFrozen_lsi_EX026 hc0 hε0 hε1 hz, fun ε hε0 hε1 => ?_⟩
  · exact residual_sqrt_EX026 hc0 hfold hε0 hε1 (le_trans (le_max_left _ _) le_rfl)
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) le_rfl)
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl) ht hte hz
  · have h := frozenInf_lsi_EX026 hc0 hε0 hε1
    exact ⟨h, (le_frozenLSRateInf_iff _ _).1 h⟩

end DGPS.Examples
