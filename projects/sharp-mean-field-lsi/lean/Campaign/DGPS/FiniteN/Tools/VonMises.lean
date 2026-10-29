import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open MeasureTheory Real

/-!
# FIN008: von Mises half circle resistance estimates

For `p_r(θ) = e^{r cos θ} / Z(r)` on `[-π, π]`, `r ≥ 1`, and `0 ≤ a ≤ π/2`, with
`J(a) = ∫₀^a e^{-r cos u} du` and `K(a) = ∫_a^π e^{r cos u} du`:
`J ≤ e^{-r cos a} min(a, π²/(2ra))`, `K ≤ e^{r cos a} min(C/√r, π²/(2ra))`, `J K ≤ C/r`,
`J K ≤ C a/√r` for `a ≤ r^{-1/2}`, and the median logarithmic Hardy products
`T(x) log(1/T(x)) ∫₀^x du/p_r(u)` are bounded by `C`, uniformly in `r ≥ 1` and `0 < x < π`.

Module placement: the preparation plan assigns FIN008 to `DGPS/FiniteN/Tools.lean`; to avoid file
contention it lives in the new module `DGPS.FiniteN.Tools.VonMises`, the declarations remaining
in namespace `DGPS.FiniteN` so that the interface name is
`DGPS.FiniteN.von_mises_half_circle_resistance_estimates`.

Conventions: `r^{-1/2}` is written `1 / √r`; the bound `π²/(2ra)` is only asserted for `a > 0`
(at `a = 0` Lean's `x / 0 = 0` would make it false), where `K ≤ e^{r cos a} C/√r` covers the
endpoint.  The Hardy product is stated for the cut points `0 < x < π` (the cut points `x < 0`
follow by symmetry); `J, K` are the unnormalized integrals and `Z(r) = ∫_{-π}^π e^{r cos θ}`.
Proof route as in the preparation plan: cosine inequalities (Jordan's inequality and a chord
estimate for `sin`), Gaussian and exponential tail integrals, reflection `θ ↦ π - θ`, and a
case split at `a = r^{-1/2}`.
-/

namespace DGPS.FiniteN

/-- Chord bound for the sine on `[0, c]`, `0 < c ≤ π`. -/
theorem vonMises_sin_chord {c x : ℝ} (hc : 0 < c) (hcπ : c ≤ π) (hx : 0 ≤ x) (hxc : x ≤ c) :
    x / c * sin c ≤ sin x := by
  have hcv := strictConcaveOn_sin_Icc.concaveOn
  have h0 : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, pi_pos.le⟩
  have h1 : c ∈ Set.Icc 0 π := ⟨hc.le, hcπ⟩
  have := hcv.2 h0 h1 (show (0:ℝ) ≤ 1 - x / c by rw [sub_nonneg, div_le_one hc]; exact hxc)
    (show (0:ℝ) ≤ x / c by positivity) (by ring)
  have e : x / c * c = x := by field_simp
  simp only [smul_eq_mul, mul_zero, zero_add, sin_zero] at this
  rw [e] at this
  exact this

/-- `cos u - cos a ≥ (2/π²)(a² - u²)` for `0 ≤ u ≤ a ≤ π/2`. -/
theorem vonMises_cos_sub_cos_left {u a : ℝ} (hu : 0 ≤ u) (hua : u ≤ a) (ha : a ≤ π / 2) :
    2 / π ^ 2 * (a ^ 2 - u ^ 2) ≤ cos u - cos a := by
  have h1 : cos u - cos a = 2 * (sin ((a + u) / 2) * sin ((a - u) / 2)) := by
    rw [cos_sub_cos]; have : (u - a) / 2 = -((a - u) / 2) := by ring
    rw [this, sin_neg, show (u + a) / 2 = (a + u) / 2 by ring]; ring
  have s1 := mul_le_sin (x := (a + u) / 2) (by linarith) (by linarith)
  have s2 := mul_le_sin (x := (a - u) / 2) (by linarith) (by linarith)
  have hp := pi_pos
  have := mul_le_mul s1 s2 (by positivity) (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  rw [h1]
  have e : 2 / π ^ 2 * (a ^ 2 - u ^ 2) = 2 * (2 / π * ((a + u) / 2) * (2 / π * ((a - u) / 2))) := by
    field_simp; ring
  rw [e]; linarith

/-- `cos a - cos u ≥ (1/π²)(u² - a²)` for `0 ≤ a ≤ π/2`, `a ≤ u ≤ π`. -/
theorem vonMises_cos_sub_cos_right {u a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ π / 2) (hau : a ≤ u)
    (hu : u ≤ π) : 1 / π ^ 2 * (u ^ 2 - a ^ 2) ≤ cos a - cos u := by
  have hp := pi_pos
  have h1 : cos a - cos u = 2 * (sin ((u + a) / 2) * sin ((u - a) / 2)) := by
    rw [cos_sub_cos]
    have : (a - u) / 2 = -((u - a) / 2) := by ring
    rw [this, sin_neg, show (a + u) / 2 = (u + a) / 2 by ring]; ring
  set s := (u + a) / 2 with hs
  set t := (u - a) / 2 with ht
  have e : 1 / π ^ 2 * (u ^ 2 - a ^ 2) = 2 / π ^ 2 * (2 * s * t) := by
    rw [hs, ht]; field_simp; ring
  rw [h1, e]
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hts : t ≤ s := by rw [hs, ht]; linarith
  have hst : s + t ≤ π := by rw [hs, ht]; linarith
  have hs34 : s ≤ 3 * π / 4 := by rw [hs]; linarith
  rcases le_or_gt s (π / 2) with h | h
  · have s1 := mul_le_sin hs0 h
    have s2 := mul_le_sin ht0 (hts.trans h)
    have := mul_le_mul s1 s2 (by positivity) (by
      have := sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith); exact this)
    have e2 : 2 / π ^ 2 * (2 * s * t) = 2 * (2 / π * s * (2 / π * t)) / 2 := by
      field_simp
    have hst0 : 0 ≤ s * t := by positivity
    have hpos : 0 ≤ 2 / π ^ 2 * (s * t) := by positivity
    nlinarith [this]
  · -- w = π - s ∈ [π/4, π/2)
    set w := π - s with hw
    have hw0 : π / 4 ≤ w := by rw [hw]; linarith
    have hw1 : w ≤ π / 2 := by rw [hw]; linarith
    have htw : t ≤ w := by rw [hw]; linarith
    have hsin_s : sin s = sin w := by rw [hw, sin_pi_sub]
    have hch := vonMises_sin_chord (c := w) (by linarith) (by linarith) ht0 htw
    have hsw : sin (π / 4) ≤ sin w := sin_le_sin_of_le_of_le_pi_div_two (by linarith) hw1 hw0
    rw [sin_pi_div_four] at hsw
    have hsq : (1 : ℝ) / 2 ≤ sin w ^ 2 := by
      have h2 : (√2 / 2) ^ 2 = 1 / 2 := by
        rw [div_pow, sq_sqrt (by norm_num)]; norm_num
      have : 0 ≤ √2 / 2 := by positivity
      nlinarith [hsw]
    have hwpos : 0 < w := by linarith
    have hsw0 : 0 ≤ sin w := sin_nonneg_of_nonneg_of_le_pi hwpos.le (by linarith)
    rw [hsin_s]
    -- sin w * sin t ≥ sin w * (t/w) sin w
    have h3 : sin w * (t / w * sin w) ≤ sin w * sin t := mul_le_mul_of_nonneg_left hch hsw0
    have h4 : 2 / π ^ 2 * (2 * s * t) ≤ 2 * (sin w * (t / w * sin w)) := by
      have hs' : s = π - w := by rw [hw]; ring
      have key : 2 / π ^ 2 * (2 * s * t) * w ≤ 2 * (sin w ^ 2 * t) := by
        have hwb : w * (π - w) ≤ π ^ 2 / 4 := by nlinarith [sq_nonneg (w - π / 2)]
        have : 2 / π ^ 2 * (2 * s * t) * w = 4 / π ^ 2 * (w * (π - w)) * t := by
          rw [hs']; ring
        rw [this]
        have h5 : 4 / π ^ 2 * (w * (π - w)) ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h5 ht0]
      have : sin w * (t / w * sin w) = sin w ^ 2 * t / w := by field_simp
      have h6 : 2 * (sin w ^ 2 * t / w) = (2 * (sin w ^ 2 * t)) / w := by ring
      rw [this, h6, le_div_iff₀ hwpos]
      linarith
    linarith


/-- `J(a) = ∫₀^a e^{-r cos u} du`. -/
noncomputable def vonMisesJ (r a : ℝ) : ℝ := ∫ u in (0 : ℝ)..a, exp (-(r * cos u))

/-- `K(a) = ∫_a^π e^{r cos u} du`. -/
noncomputable def vonMisesK (r a : ℝ) : ℝ := ∫ u in a..π, exp (r * cos u)

theorem vonMises_integral_exp_decay {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L) :
    ∫ v in (0 : ℝ)..L, exp (-c * v) ≤ 1 / c := by
  rw [intervalIntegral.integral_of_le hL]
  have hi := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
  calc _ ≤ ∫ v in Set.Ioi (0 : ℝ), exp (-c * v) :=
        setIntegral_mono_set hi (ae_of_all _ fun _ => (exp_pos _).le)
          Set.Ioc_subset_Ioi_self.eventuallyLE
    _ = 1 / c := by
        rw [integral_exp_mul_Ioi (by linarith)]
        field_simp
        simp

theorem vonMises_integral_gaussian_le {b L : ℝ} (hb : 0 < b) (hL : 0 ≤ L) :
    ∫ v in (0 : ℝ)..L, exp (-b * v ^ 2) ≤ √(π / b) / 2 := by
  rw [intervalIntegral.integral_of_le hL, ← integral_gaussian_Ioi]
  exact setIntegral_mono_set (integrable_exp_neg_mul_sq hb).integrableOn
    (ae_of_all _ fun _ => (exp_pos _).le) Set.Ioc_subset_Ioi_self.eventuallyLE

theorem vonMisesJ_le_mul {r a : ℝ} (hr : 0 ≤ r) (ha0 : 0 ≤ a) (ha : a ≤ π / 2) :
    vonMisesJ r a ≤ exp (-(r * cos a)) * a := by
  unfold vonMisesJ
  calc _ ≤ ∫ u in (0 : ℝ)..a, exp (-(r * cos a)) := by
        apply intervalIntegral.integral_mono_on ha0
        · exact (by fun_prop : Continuous fun u : ℝ => exp (-(r * cos u))).intervalIntegrable _ _
        · exact intervalIntegrable_const
        · intro u hu
          apply exp_le_exp.2
          have := cos_le_cos_of_nonneg_of_le_pi hu.1 (by linarith [pi_pos]) hu.2
          nlinarith
    _ = _ := by rw [intervalIntegral.integral_const]; simp [mul_comm]

theorem vonMisesJ_le_div {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ π / 2) :
    vonMisesJ r a ≤ exp (-(r * cos a)) * (π ^ 2 / (2 * r * a)) := by
  have hp := pi_pos
  set c := 2 * r * a / π ^ 2 with hc
  have hcpos : 0 < c := by positivity
  unfold vonMisesJ
  calc _ ≤ ∫ u in (0 : ℝ)..a, exp (-(r * cos a)) * exp (-c * (a - u)) := by
        apply intervalIntegral.integral_mono_on ha0.le
        · exact (by fun_prop : Continuous fun u : ℝ => exp (-(r * cos u))).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun u : ℝ =>
            exp (-(r * cos a)) * exp (-c * (a - u))).intervalIntegrable _ _
        · intro u hu
          rw [← exp_add]
          apply exp_le_exp.2
          have h1 := vonMises_cos_sub_cos_left hu.1 hu.2 ha
          have h2 : c * (a - u) ≤ r * (cos u - cos a) := by
            have : 2 / π ^ 2 * (a ^ 2 - u ^ 2) ≥ 2 / π ^ 2 * (a * (a - u)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [hu.1, hu.2]
            have e : c * (a - u) = r * (2 / π ^ 2 * (a * (a - u))) := by rw [hc]; field_simp
            rw [e]
            exact mul_le_mul_of_nonneg_left (by linarith) hr.le
          nlinarith
    _ = exp (-(r * cos a)) * ∫ u in (0 : ℝ)..a, exp (-c * (a - u)) := by
        rw [intervalIntegral.integral_const_mul]
    _ = exp (-(r * cos a)) * ∫ v in (0 : ℝ)..a, exp (-c * v) := by
        congr 1
        have := intervalIntegral.integral_comp_sub_left (a := 0) (b := a)
          (fun v => exp (-c * v)) a
        simpa using this
    _ ≤ exp (-(r * cos a)) * (1 / c) :=
        mul_le_mul_of_nonneg_left (vonMises_integral_exp_decay hcpos ha0.le) (exp_pos _).le
    _ = _ := by rw [hc]; field_simp

theorem vonMisesK_pointwise {r a u : ℝ} (hr : 0 ≤ r) (ha0 : 0 ≤ a) (ha : a ≤ π / 2)
    (hau : a ≤ u) (hu : u ≤ π) :
    exp (r * cos u) ≤ exp (r * cos a) * exp (-(r / π ^ 2 * (u - a) ^ 2)) := by
  have hp := pi_pos
  rw [← exp_add]
  apply exp_le_exp.2
  have h1 := vonMises_cos_sub_cos_right ha0 ha hau hu
  have h2 : (u - a) ^ 2 ≤ u ^ 2 - a ^ 2 := by nlinarith
  have h3 : 1 / π ^ 2 * (u - a) ^ 2 ≤ cos a - cos u :=
    le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have := mul_le_mul_of_nonneg_left h3 hr
  have e : r * (1 / π ^ 2 * (u - a) ^ 2) = r / π ^ 2 * (u - a) ^ 2 := by ring
  nlinarith

theorem vonMisesK_le_sqrt {r a : ℝ} (hr : 0 < r) (ha0 : 0 ≤ a) (ha : a ≤ π / 2) :
    vonMisesK r a ≤ exp (r * cos a) * (π ^ 2 / √r) := by
  have hp := pi_pos
  have hb : 0 < r / π ^ 2 := by positivity
  have hle : a ≤ π := by linarith
  unfold vonMisesK
  calc _ ≤ ∫ u in a..π, exp (r * cos a) * exp (-(r / π ^ 2) * (u - a) ^ 2) := by
        apply intervalIntegral.integral_mono_on hle
        · exact (by fun_prop : Continuous fun u : ℝ => exp (r * cos u)).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun u : ℝ =>
            exp (r * cos a) * exp (-(r / π ^ 2) * (u - a) ^ 2)).intervalIntegrable _ _
        · intro u hu
          have := vonMisesK_pointwise hr.le ha0 ha hu.1 hu.2
          simpa [neg_mul] using this
    _ = exp (r * cos a) * ∫ u in a..π, exp (-(r / π ^ 2) * (u - a) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
    _ = exp (r * cos a) * ∫ v in (0 : ℝ)..(π - a), exp (-(r / π ^ 2) * v ^ 2) := by
        congr 1
        have := intervalIntegral.integral_comp_sub_right (a := a) (b := π)
          (fun v => exp (-(r / π ^ 2) * v ^ 2)) a
        simpa using this
    _ ≤ exp (r * cos a) * (√(π / (r / π ^ 2)) / 2) :=
        mul_le_mul_of_nonneg_left (vonMises_integral_gaussian_le hb (by linarith)) (exp_pos _).le
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
        have e : π / (r / π ^ 2) = π ^ 3 / r := by field_simp
        rw [e, sqrt_div (by positivity)]
        have h1 : √(π ^ 3) ≤ 2 * π ^ 2 := by
          rw [sqrt_le_left (by positivity)]
          nlinarith [one_le_pi_div_two, pow_pos hp 3]
        have h2 : 0 < √r := sqrt_pos.2 hr
        rw [div_div, div_le_div_iff₀ (by positivity) h2]
        nlinarith [mul_pos h2 (pow_pos hp 2)]

theorem vonMisesK_le_div {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ π / 2) :
    vonMisesK r a ≤ exp (r * cos a) * (π ^ 2 / (2 * r * a)) := by
  have hp := pi_pos
  set c := 2 * r * a / π ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hle : a ≤ π := by linarith
  unfold vonMisesK
  calc _ ≤ ∫ u in a..π, exp (r * cos a) * exp (-c * (u - a)) := by
        apply intervalIntegral.integral_mono_on hle
        · exact (by fun_prop : Continuous fun u : ℝ => exp (r * cos u)).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun u : ℝ =>
            exp (r * cos a) * exp (-c * (u - a))).intervalIntegrable _ _
        · intro u hu
          rw [← exp_add]
          apply exp_le_exp.2
          have h1 := vonMises_cos_sub_cos_right ha0.le ha hu.1 hu.2
          have h2 : c * (u - a) ≤ r * (cos a - cos u) := by
            have : 1 / π ^ 2 * (u ^ 2 - a ^ 2) ≥ 1 / π ^ 2 * (2 * a * (u - a)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [hu.1, hu.2]
            have e : c * (u - a) = r * (1 / π ^ 2 * (2 * a * (u - a))) := by rw [hc]; field_simp
            rw [e]
            exact mul_le_mul_of_nonneg_left (by linarith) hr.le
          nlinarith
    _ = exp (r * cos a) * ∫ u in a..π, exp (-c * (u - a)) := by
        rw [intervalIntegral.integral_const_mul]
    _ = exp (r * cos a) * ∫ v in (0 : ℝ)..(π - a), exp (-c * v) := by
        congr 1
        have := intervalIntegral.integral_comp_sub_right (a := a) (b := π)
          (fun v => exp (-c * v)) a
        simpa using this
    _ ≤ exp (r * cos a) * (1 / c) :=
        mul_le_mul_of_nonneg_left (vonMises_integral_exp_decay hcpos (by linarith))
          (exp_pos _).le
    _ = _ := by rw [hc]; field_simp


theorem vonMisesJ_nonneg {r a : ℝ} (ha : 0 ≤ a) : 0 ≤ vonMisesJ r a :=
  intervalIntegral.integral_nonneg ha fun _ _ => (exp_pos _).le

theorem vonMisesK_nonneg {r a : ℝ} (ha : a ≤ π) : 0 ≤ vonMisesK r a :=
  intervalIntegral.integral_nonneg ha fun _ _ => (exp_pos _).le

theorem vonMisesJ_ge {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) : a * exp (-r) ≤ vonMisesJ r a := by
  unfold vonMisesJ
  have : ∫ u in (0 : ℝ)..a, exp (-r) ≤ ∫ u in (0 : ℝ)..a, exp (-(r * cos u)) := by
    apply intervalIntegral.integral_mono_on ha intervalIntegrable_const
    · exact (by fun_prop : Continuous fun u : ℝ => exp (-(r * cos u))).intervalIntegrable _ _
    · intro u _
      apply exp_le_exp.2
      nlinarith [cos_le_one u]
  simpa [mul_comm] using this

theorem vonMisesK_ge {r a : ℝ} (hr : 0 ≤ r) (ha : a ≤ π) : (π - a) * exp (-r) ≤ vonMisesK r a := by
  unfold vonMisesK
  have : ∫ u in a..π, exp (-r) ≤ ∫ u in a..π, exp (r * cos u) := by
    apply intervalIntegral.integral_mono_on ha intervalIntegrable_const
    · exact (by fun_prop : Continuous fun u : ℝ => exp (r * cos u)).intervalIntegrable _ _
    · intro u _
      apply exp_le_exp.2
      nlinarith [neg_one_le_cos u]
  simpa [mul_comm] using this

/-- Reflection `θ ↦ π - θ` exchanges the two half-circle integrals. -/
theorem vonMisesK_reflect (r x : ℝ) : vonMisesK r x = vonMisesJ r (π - x) := by
  unfold vonMisesK vonMisesJ
  have := intervalIntegral.integral_comp_sub_left (a := x) (b := π)
    (fun v => exp (-(r * cos v))) π
  simp only [sub_self] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro u _
  simp [cos_pi_sub]

theorem vonMisesJ_reflect (r x : ℝ) : vonMisesJ r x = vonMisesK r (π - x) := by
  rw [vonMisesK_reflect, sub_sub_cancel]

/-- Normalizing constant `∫_{-π}^{π} e^{r cos θ} dθ`. -/
noncomputable def vonMisesZ (r : ℝ) : ℝ := ∫ u in (-π)..π, exp (r * cos u)

/-- Von Mises density `p_r(θ) = e^{r cos θ} / Z(r)` on `[-π, π]`. -/
noncomputable def vonMisesDensity (r θ : ℝ) : ℝ := exp (r * cos θ) / vonMisesZ r

/-- Upper tail `T(x) = ∫_x^π p_r`. -/
noncomputable def vonMisesTail (r x : ℝ) : ℝ := ∫ u in x..π, vonMisesDensity r u

theorem vonMisesZ_le {r : ℝ} (hr : 0 ≤ r) : vonMisesZ r ≤ 2 * π * exp r := by
  have hp := pi_pos
  unfold vonMisesZ
  have : ∫ u in (-π)..π, exp (r * cos u) ≤ ∫ u in (-π)..π, exp r := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u : ℝ => exp (r * cos u)).intervalIntegrable _ _
    · exact intervalIntegrable_const
    · intro u _
      apply exp_le_exp.2
      nlinarith [cos_le_one u]
  simp only [intervalIntegral.integral_const, smul_eq_mul] at this
  nlinarith

theorem vonMisesZ_pos (r : ℝ) : 0 < vonMisesZ r := by
  have hp := pi_pos
  unfold vonMisesZ
  apply intervalIntegral.intervalIntegral_pos_of_pos
  · exact (by fun_prop : Continuous fun u : ℝ => exp (r * cos u)).intervalIntegrable _ _
  · intro u; exact exp_pos _
  · linarith

/-- Products of the half-circle integrals, bounded by `a/√r`. -/
theorem vonMises_JK_le_mul {r a : ℝ} (hr : 1 ≤ r) (ha0 : 0 ≤ a) (ha : a ≤ π / 2) :
    vonMisesJ r a * vonMisesK r a ≤ π ^ 2 * a / √r := by
  have hp := pi_pos
  have hs : 0 < √r := sqrt_pos.2 (by linarith)
  have h1 := vonMisesJ_le_mul (r := r) (by linarith) ha0 ha
  have h2 := vonMisesK_le_sqrt (r := r) (by linarith) ha0 ha
  have hEE : exp (-(r * cos a)) * exp (r * cos a) = 1 := by rw [← exp_add]; simp
  calc _ ≤ (exp (-(r * cos a)) * a) * (exp (r * cos a) * (π ^ 2 / √r)) :=
        mul_le_mul h1 h2 (vonMisesK_nonneg (by linarith)) (by positivity)
    _ = (exp (-(r * cos a)) * exp (r * cos a)) * (π ^ 2 * a / √r) := by ring
    _ = _ := by rw [hEE, one_mul]

theorem vonMises_JK_le_div {r a : ℝ} (hr : 1 ≤ r) (ha0 : 0 < a) (ha : a ≤ π / 2) :
    vonMisesJ r a * vonMisesK r a ≤ π ^ 4 / (2 * r * a * √r) := by
  have hp := pi_pos
  have hs : 0 < √r := sqrt_pos.2 (by linarith)
  have h1 := vonMisesJ_le_div (r := r) (by linarith) ha0 ha
  have h2 := vonMisesK_le_sqrt (r := r) (by linarith) ha0.le ha
  have hEE : exp (-(r * cos a)) * exp (r * cos a) = 1 := by rw [← exp_add]; simp
  calc _ ≤ (exp (-(r * cos a)) * (π ^ 2 / (2 * r * a))) * (exp (r * cos a) * (π ^ 2 / √r)) :=
        mul_le_mul h1 h2 (vonMisesK_nonneg (by linarith)) (by positivity)
    _ = (exp (-(r * cos a)) * exp (r * cos a)) * (π ^ 4 / (2 * r * a * √r)) := by
        field_simp
    _ = _ := by rw [hEE, one_mul]

theorem vonMises_JK_le {r a : ℝ} (hr : 1 ≤ r) (ha0 : 0 ≤ a) (ha : a ≤ π / 2) :
    vonMisesJ r a * vonMisesK r a ≤ π ^ 4 / r := by
  have hp := pi_pos
  have hs : 0 < √r := sqrt_pos.2 (by linarith)
  have hss : √r * √r = r := mul_self_sqrt (by linarith)
  have hπ : 1 ≤ π ^ 2 := by nlinarith [one_le_pi_div_two]
  have hπ4 : π ^ 2 ≤ π ^ 4 := by nlinarith [one_le_pi_div_two, pow_pos hp 2]
  rcases le_or_gt a (1 / √r) with h | h
  · calc _ ≤ π ^ 2 * a / √r := vonMises_JK_le_mul hr ha0 ha
      _ ≤ π ^ 2 * (1 / √r) / √r := by gcongr
      _ = π ^ 2 / r := by
        have : π ^ 2 * (1 / √r) / √r = π ^ 2 / (√r * √r) := by field_simp
        rw [this, hss]
      _ ≤ _ := by gcongr
  · have ha' : 0 < a := lt_of_le_of_lt (by positivity) h
    have has : 1 < a * √r := by
      rw [div_lt_iff₀ hs] at h; exact h
    calc _ ≤ π ^ 4 / (2 * r * a * √r) := vonMises_JK_le_div hr ha' ha
      _ ≤ π ^ 4 / r := by
        apply div_le_div_of_nonneg_left (by positivity) (by linarith)
        nlinarith [mul_pos (by linarith : (0:ℝ) < r) ha', has]


/-- Identity for the logarithmic Hardy product in terms of `J`, `K`, `Z`. -/
theorem vonMises_hardy_eq {r x : ℝ} (hxπ : x < π) (hr : 0 ≤ r) :
    vonMisesTail r x * Real.log (1 / vonMisesTail r x) *
        ∫ u in (0 : ℝ)..x, 1 / vonMisesDensity r u =
      vonMisesJ r x * vonMisesK r x * Real.log (vonMisesZ r / vonMisesK r x) := by
  have hZ := vonMisesZ_pos r
  have hK : 0 < vonMisesK r x := by
    have := vonMisesK_ge (r := r) hr hxπ.le
    have h2 : 0 < (π - x) * exp (-r) := mul_pos (by linarith) (exp_pos _)
    linarith
  have hT : vonMisesTail r x = vonMisesK r x / vonMisesZ r := by
    unfold vonMisesTail vonMisesDensity vonMisesK
    rw [intervalIntegral.integral_div]
  have hI : ∫ u in (0 : ℝ)..x, 1 / vonMisesDensity r u = vonMisesZ r * vonMisesJ r x := by
    unfold vonMisesJ
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [vonMisesDensity]
    rw [one_div_div, div_eq_mul_inv, ← exp_neg]
  rw [hT, hI, one_div_div]
  field_simp

theorem vonMises_hardy_bound_left {r x : ℝ} (hr : 1 ≤ r) (hx0 : 0 < x) (hx : x ≤ π / 2) :
    vonMisesJ r x * vonMisesK r x * Real.log (vonMisesZ r / vonMisesK r x) ≤ 5 * π ^ 4 := by
  have hp := pi_pos
  have hr0 : 0 ≤ r := by linarith
  have hZ := vonMisesZ_pos r
  have hZle := vonMisesZ_le hr0
  have hKge := vonMisesK_ge (r := r) hr0 (by linarith : x ≤ π)
  have he : 0 < exp r := exp_pos r
  have hen : exp (-r) = (exp r)⁻¹ := exp_neg r
  have hKpos : 0 < vonMisesK r x := by
    have h2 : 0 < (π - x) * exp (-r) := mul_pos (by linarith) (exp_pos _)
    linarith
  have hK2 : π / 2 * (exp r)⁻¹ ≤ vonMisesK r x := by
    rw [hen] at hKge
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hKge
  have hratio : vonMisesZ r ≤ 4 * exp r ^ 2 * vonMisesK r x := by
    have : 4 * exp r ^ 2 * (π / 2 * (exp r)⁻¹) = 2 * π * exp r := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hK2 (by positivity : (0:ℝ) ≤ 4 * exp r ^ 2)]
  have hlog : Real.log (vonMisesZ r / vonMisesK r x) ≤ 2 * r + 3 := by
    have h1 : vonMisesZ r / vonMisesK r x ≤ 4 * exp r ^ 2 := by
      rw [div_le_iff₀ hKpos]; linarith
    have h2 := Real.log_le_log (div_pos hZ hKpos) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp] at h2
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
    push_cast at h2
    linarith
  have hJK := vonMises_JK_le hr hx0.le hx
  have hJKnn : 0 ≤ vonMisesJ r x * vonMisesK r x :=
    mul_nonneg (vonMisesJ_nonneg hx0.le) (vonMisesK_nonneg (by linarith))
  calc _ ≤ vonMisesJ r x * vonMisesK r x * (2 * r + 3) :=
        mul_le_mul_of_nonneg_left hlog hJKnn
    _ ≤ π ^ 4 / r * (2 * r + 3) := mul_le_mul_of_nonneg_right hJK (by linarith)
    _ = π ^ 4 * (2 + 3 / r) := by field_simp
    _ ≤ π ^ 4 * (2 + 3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 3 / r ≤ 3 := by rw [div_le_iff₀ (by linarith)]; nlinarith
        linarith
    _ = 5 * π ^ 4 := by ring

theorem vonMises_hardy_bound_right {r x : ℝ} (hr : 1 ≤ r) (hx : π / 2 ≤ x) (hxπ : x < π) :
    vonMisesJ r x * vonMisesK r x * Real.log (vonMisesZ r / vonMisesK r x) ≤
      π ^ 4 * (2 + 2 * π) + 2 * π ^ 2 + 2 * π ^ 3 := by
  have hp := pi_pos
  have hr0 : 0 ≤ r := by linarith
  set a := π - x with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha2 : a ≤ π / 2 := by rw [ha]; linarith
  have hZ := vonMisesZ_pos r
  have hZle := vonMisesZ_le hr0
  have hKx : vonMisesK r x = vonMisesJ r a := vonMisesK_reflect r x
  have hJx : vonMisesJ r x = vonMisesK r a := by rw [vonMisesJ_reflect, ha]
  have hJge := vonMisesJ_ge (r := r) (a := a) hr0 ha0.le
  have he : 0 < exp r := exp_pos r
  have hen : exp (-r) = (exp r)⁻¹ := exp_neg r
  have hKpos : 0 < vonMisesK r x := by
    rw [hKx]; have : 0 < a * exp (-r) := mul_pos ha0 (exp_pos _); linarith
  have hK2 : a * (exp r)⁻¹ ≤ vonMisesK r x := by rw [hKx, ← hen]; exact hJge
  have hratio : vonMisesZ r ≤ (2 * π / a) * exp r ^ 2 * vonMisesK r x := by
    have : (2 * π / a) * exp r ^ 2 * (a * (exp r)⁻¹) = 2 * π * exp r := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hK2 (by positivity : (0:ℝ) ≤ (2 * π / a) * exp r ^ 2)]
  have hlog : Real.log (vonMisesZ r / vonMisesK r x) ≤ 2 * r + 2 * π / a := by
    have h1 : vonMisesZ r / vonMisesK r x ≤ (2 * π / a) * exp r ^ 2 := by
      rw [div_le_iff₀ hKpos]; linarith
    have h2 := Real.log_le_log (div_pos hZ hKpos) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h2
    have h4 : Real.log (2 * π / a) ≤ 2 * π / a := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π / a); linarith
    push_cast at h2
    linarith
  have hJKnn : 0 ≤ vonMisesJ r a * vonMisesK r a :=
    mul_nonneg (vonMisesJ_nonneg ha0.le) (vonMisesK_nonneg (by linarith))
  have hprod : vonMisesJ r x * vonMisesK r x = vonMisesJ r a * vonMisesK r a := by
    rw [hKx, hJx, mul_comm]
  rw [hprod]
  have hB : 0 < 2 * r + 2 * π / a := by positivity
  have hs : 0 < √r := sqrt_pos.2 (by linarith)
  have hss : √r * √r = r := mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ √r := by rw [Real.one_le_sqrt]; exact hr
  have hsr : √r ≤ r := by nlinarith
  calc _ ≤ vonMisesJ r a * vonMisesK r a * (2 * r + 2 * π / a) :=
        mul_le_mul_of_nonneg_left hlog hJKnn
    _ ≤ _ := by
      rcases le_or_gt a (1 / √r) with h | h
      · -- a small
        have h1 := vonMises_JK_le_mul hr ha0.le ha2
        calc _ ≤ π ^ 2 * a / √r * (2 * r + 2 * π / a) := mul_le_mul_of_nonneg_right h1 hB.le
          _ = 2 * π ^ 2 * (a * √r) + 2 * π ^ 3 / √r := by
            have key : ∀ t : ℝ, 0 < t → π ^ 2 * a / t * (2 * (t * t) + 2 * π / a) =
                2 * π ^ 2 * (a * t) + 2 * π ^ 3 / t := by
              intro t ht; field_simp
            have := key (√r) hs
            rwa [hss] at this
          _ ≤ 2 * π ^ 2 * 1 + 2 * π ^ 3 * 1 := by
            have h5 : a * √r ≤ 1 := by rw [le_div_iff₀ hs] at h; exact h
            have h6 : 2 * π ^ 3 / √r ≤ 2 * π ^ 3 * 1 := by
              rw [div_le_iff₀ hs]; nlinarith [pow_pos hp 3]
            nlinarith [pow_pos hp 2]
          _ ≤ _ := by nlinarith [pow_pos hp 4, pow_pos hp 2, pow_pos hp 3, pow_pos hp 5]
      · -- a large
        have h1 := vonMises_JK_le hr ha0.le ha2
        have h5 : 1 < a * √r := by rw [div_lt_iff₀ hs] at h; exact h
        have h6 : 2 * π / a ≤ 2 * π * √r := by
          rw [div_le_iff₀ ha0]; nlinarith
        have hB2 : 2 * r + 2 * π / a ≤ (2 + 2 * π) * r := by nlinarith
        calc _ ≤ π ^ 4 / r * (2 * r + 2 * π / a) := mul_le_mul_of_nonneg_right h1 hB.le
          _ ≤ π ^ 4 / r * ((2 + 2 * π) * r) := mul_le_mul_of_nonneg_left hB2 (by positivity)
          _ = π ^ 4 * (2 + 2 * π) := by field_simp
          _ ≤ _ := by nlinarith [pow_pos hp 2, pow_pos hp 3]


/-- **FIN008.** Von Mises half-circle resistance estimates.

Let `p_r(θ) = e^{r cos θ} / Z(r)` on `[-π, π]` and `r ≥ 1`, and for `0 ≤ a ≤ π/2`
`J(a) = ∫₀^a e^{-r cos u} du`, `K(a) = ∫_a^π e^{r cos u} du`.  There is a universal constant `C`
such that `J ≤ e^{-r cos a} min(a, π²/(2ra))`, `K ≤ e^{r cos a} min(C/√r, π²/(2ra))`
(the second entry of the minimum is only meaningful, and only asserted, for `a > 0`; for `a = 0`
the clause `K ≤ e^{r cos a} C/√r` is asserted), `J K ≤ C/r`, `J K ≤ C a/√r` when `a ≤ r^{-1/2}`,
and the median logarithmic Hardy products
`T(x) log(1/T(x)) ∫₀^x du/p_r(u)` (`T(x) = ∫_x^π p_r`) are bounded by `C` for all cut points
`0 < x < π`. -/
theorem von_mises_half_circle_resistance_estimates :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      (∀ a : ℝ, 0 ≤ a → a ≤ π / 2 →
        vonMisesJ r a ≤ exp (-(r * cos a)) * min a (π ^ 2 / (2 * r * a)) ∧
        vonMisesK r a ≤ exp (r * cos a) * (C / √r) ∧
        (0 < a → vonMisesK r a ≤ exp (r * cos a) * min (C / √r) (π ^ 2 / (2 * r * a))) ∧
        vonMisesJ r a * vonMisesK r a ≤ C / r ∧
        (a ≤ 1 / √r → vonMisesJ r a * vonMisesK r a ≤ C * a / √r)) ∧
      (∀ x : ℝ, 0 < x → x < π →
        vonMisesTail r x * Real.log (1 / vonMisesTail r x) *
          ∫ u in (0 : ℝ)..x, 1 / vonMisesDensity r u ≤ C) := by
  have hp := pi_pos
  have hp2 : 2 ≤ π := by linarith [one_le_pi_div_two]
  set C : ℝ := π ^ 4 * (2 + 2 * π) + 2 * π ^ 2 + 2 * π ^ 3 + 5 * π ^ 4 with hC
  have hp4 : 0 < π ^ 4 := by positivity
  have hp3 : 0 < π ^ 3 := by positivity
  have hp22 : 0 < π ^ 2 := by positivity
  have hCπ2 : π ^ 2 ≤ C := by nlinarith [mul_pos hp4 hp]
  have hCπ4 : π ^ 4 ≤ C := by nlinarith [mul_pos hp4 hp]
  have hCleft : 5 * π ^ 4 ≤ C := by nlinarith [mul_pos hp4 hp]
  have hCright : π ^ 4 * (2 + 2 * π) + 2 * π ^ 2 + 2 * π ^ 3 ≤ C := by nlinarith [mul_pos hp4 hp]
  refine ⟨C, by linarith, fun r hr => ⟨fun a ha0 ha => ?_, fun x hx0 hxπ => ?_⟩⟩
  · have hr0 : 0 < r := by linarith
    have hs : 0 < √r := sqrt_pos.2 hr0
    have hE := exp_pos (-(r * cos a))
    have hE' := exp_pos (r * cos a)
    have hKs : vonMisesK r a ≤ exp (r * cos a) * (C / √r) :=
      le_trans (vonMisesK_le_sqrt hr0 ha0 ha) (by gcongr)
    refine ⟨?_, hKs, fun ha' => ?_, ?_, fun h => ?_⟩
    · rcases ha0.eq_or_lt with h | h
      · subst h; simp [vonMisesJ]
      · rw [mul_min_of_nonneg _ _ hE.le]
        exact le_min (vonMisesJ_le_mul hr0.le ha0 ha) (vonMisesJ_le_div hr0 h ha)
    · rw [mul_min_of_nonneg _ _ hE'.le]
      exact le_min hKs (vonMisesK_le_div hr0 ha' ha)
    · exact le_trans (vonMises_JK_le hr ha0 ha) (by gcongr)
    · exact le_trans (vonMises_JK_le_mul hr ha0 ha) (by gcongr)
  · have hr0 : 0 ≤ r := by linarith
    rw [vonMises_hardy_eq hxπ hr0]
    rcases le_total x (π / 2) with h | h
    · exact le_trans (vonMises_hardy_bound_left hr hx0 h) hCleft
    · exact le_trans (vonMises_hardy_bound_right hr h hxπ) hCright

end DGPS.FiniteN
