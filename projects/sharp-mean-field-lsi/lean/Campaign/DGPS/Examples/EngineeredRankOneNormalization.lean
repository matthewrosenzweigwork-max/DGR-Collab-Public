import DGPS.Examples.EngineeredRankOneEstimates
import DGPS.Examples.EngineeredRankOneEigen

open MeasureTheory Real Set Filter Topology
open DGPS.Circle.AngularNormalization

/-!
# Engineered normalization and rare-mass bounds (EX036)

With `Z_h = ∫ exp(-hU - R_h(U)) dθ/(2π)` (`Zh`), `q_h = Z_h⁻¹ exp(-hU - R_h(U))` (`qAng`, the density
of `μ_h` with respect to the normalized angular Haar measure `m`), there are absolute `c, C > 0` such
that for every `h ≥ 2`: `c h^{-1/2} ≤ Z_h ≤ C h^{-1/2}`, `min q_h ≥ c h^{-1/2} exp(-2h)` and
`μ_h(exp(2hU)) ≤ C exp(2h)/h`. The proof uses the EX035 bounds `exp R_h(u) ≍ 1 + h u` on `[0,2]`
(`exp_corr_bounds`, the content of `engineered_ein_representation`) and `R_h ≥ 0` (EX031).
Main output: `DGPS.Examples.engineered_normalization_and_rare_mass_bounds`.
-/

namespace DGPS.Examples.EngineeredRankOne

/-- Integral over the angular circle as an integral over the window `[-π, π]`. -/
theorem integral_angHaar_eq_interval (f : AngCircle → ℝ) :
    ∫ θ, f θ ∂angHaar = (2 * π)⁻¹ * ∫ t in (-π)..π, f (t : AngCircle) := by
  rw [AddCircle.integral_haarAddCircle, smul_eq_mul]
  have := AddCircle.intervalIntegral_preimage (2 * π) (-π) f
  rw [show -π + 2 * π = π by ring] at this
  rw [← this]

theorem integrable_angHaar_of_continuous {f : AngCircle → ℝ} (hf : Continuous f) :
    Integrable f angHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem corr_zero (h : ℝ) : corr h 0 = 0 := by simp [corr]

theorem corr_nonneg (h : ℝ) (hh : 0 < h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) : 0 ≤ corr h u := by
  have := monotoneOn_corr h hh ⟨le_rfl, by norm_num⟩ hu hu.1
  rwa [corr_zero] at this

theorem Uang_coe_eq (t : ℝ) : Uang (t : AngCircle) = 1 - Real.cos t := Uang_coe t

theorem sq_div_le_one_sub_cos {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ π) :
    2 * s ^ 2 / π ^ 2 ≤ 1 - Real.cos s := by
  have hpi := Real.pi_pos
  have e : Real.cos s = 2 * Real.cos (s / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have h1 : 1 - Real.cos s = 2 * Real.sin (s / 2) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (s / 2)
    rw [e]; linarith
  have h2 : 2 / π * (s / 2) ≤ Real.sin (s / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have h3 : s / π ≤ Real.sin (s / 2) := by
    have : 2 / π * (s / 2) = s / π := by field_simp
    linarith
  have h4 : (s / π) ^ 2 ≤ Real.sin (s / 2) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hs0 hpi.le) h3 2
  have h5 : 2 * s ^ 2 / π ^ 2 = 2 * (s / π) ^ 2 := by field_simp
  rw [h1, h5]; linarith

theorem one_sub_cos_ge_of_abs {t : ℝ} (ht : |t| ≤ π) : 2 * t ^ 2 / π ^ 2 ≤ 1 - Real.cos t := by
  have := sq_div_le_one_sub_cos (abs_nonneg t) ht
  rwa [sq_abs, Real.cos_abs] at this

/-- Gaussian upper bound for `∫ exp(-hU) dm`. -/
theorem integral_exp_neg_Uang_le (h : ℝ) (hh : 0 < h) :
    ∫ θ, exp (-(h * Uang θ)) ∂angHaar ≤ (2 * π)⁻¹ * √(π / (2 * h / π ^ 2)) := by
  have hpi := Real.pi_pos
  have hb : 0 < 2 * h / π ^ 2 := by positivity
  rw [integral_angHaar_eq_interval]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hfi : IntervalIntegrable (fun t : ℝ => exp (-(h * Uang (t : AngCircle)))) volume (-π) π :=
    (((continuous_const.mul (continuous_Uang.comp Real.Angle.continuous_coe)).neg).rexp).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun t : ℝ => exp (-(2 * h / π ^ 2) * t ^ 2)) volume (-π) π :=
    (by fun_prop : Continuous fun t : ℝ => exp (-(2 * h / π ^ 2) * t ^ 2)).intervalIntegrable _ _
  calc ∫ t in (-π)..π, exp (-(h * Uang (t : AngCircle)))
      ≤ ∫ t in (-π)..π, exp (-(2 * h / π ^ 2) * t ^ 2) := by
        refine intervalIntegral.integral_mono_on (by linarith) hfi hgi ?_
        intro t ht
        have habs : |t| ≤ π := abs_le.2 ⟨ht.1, ht.2⟩
        have := one_sub_cos_ge_of_abs habs
        rw [Uang_coe_eq]
        refine exp_le_exp.2 ?_
        have h6 : h * (2 * t ^ 2 / π ^ 2) = 2 * h / π ^ 2 * t ^ 2 := by ring
        nlinarith [mul_le_mul_of_nonneg_left this hh.le]
    _ ≤ ∫ t : ℝ, exp (-(2 * h / π ^ 2) * t ^ 2) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
          (Eventually.of_forall fun t => (exp_pos _).le)
    _ = √(π / (2 * h / π ^ 2)) := integral_gaussian _

theorem Uang_mem' (θ : AngCircle) : 0 ≤ Uang θ ∧ Uang θ ≤ 2 := Uang_mem θ

theorem logq_le (h : ℝ) (hh : 0 < h) (θ : AngCircle) : logq h θ ≤ -(h * Uang θ) := by
  have := corr_nonneg h hh (Uang_mem θ)
  unfold logq; linarith

theorem Zh_le_integral (h : ℝ) (hh : 0 < h) :
    Zh h ≤ ∫ θ, exp (-(h * Uang θ)) ∂angHaar := by
  unfold Zh
  refine integral_mono (integrable_angHaar_of_continuous
    (continuous_exp.comp (continuous_logq h hh)))
    (integrable_angHaar_of_continuous ((continuous_const.mul continuous_Uang).neg.rexp)) ?_
  intro θ
  exact exp_le_exp.2 (logq_le h hh θ)

/-- `∫ exp(-hU) dm ≤ C₀ h^{-1/2}`. -/
theorem integral_exp_neg_Uang_le_sqrt (h : ℝ) (hh : 0 < h) :
    ∫ θ, exp (-(h * Uang θ)) ∂angHaar ≤ ((2 * π)⁻¹ * √(π / (2 / π ^ 2))) * (√h)⁻¹ := by
  have hpi := Real.pi_pos
  refine (integral_exp_neg_Uang_le h hh).trans (le_of_eq ?_)
  have : √(π / (2 * h / π ^ 2)) = √(π / (2 / π ^ 2)) * (√h)⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [this]; ring

/-- Upper bound `Z_h ≤ C₀ h^{-1/2}`. -/
theorem Zh_le (h : ℝ) (hh : 0 < h) :
    Zh h ≤ ((2 * π)⁻¹ * √(π / (2 / π ^ 2))) * (√h)⁻¹ :=
  (Zh_le_integral h hh).trans (integral_exp_neg_Uang_le_sqrt h hh)

theorem corr_le_fifteen {h : ℝ} (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) (hhu : h * u ≤ 1) :
    corr h u ≤ 15 := by
  have h1 := (exp_corr_bounds hh hu).2
  have h2 : exp (corr h u) ≤ exp 15 := by
    calc exp (corr h u) ≤ exp 14 * (1 + h * u) := h1
      _ ≤ exp 14 * exp 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          have := Real.add_one_le_exp 1; linarith
      _ = exp 15 := by rw [← exp_add]; norm_num
  exact exp_le_exp.1 h2

/-- Lower bound `Z_h ≥ (e^{-16}/π) h^{-1/2}`. -/
theorem Zh_ge (h : ℝ) (hh : 2 ≤ h) : exp (-16) / π * (√h)⁻¹ ≤ Zh h := by
  have hpi := Real.pi_pos
  have hp : 0 < h := by linarith
  have hs : 0 < √h := Real.sqrt_pos.2 hp
  set a : ℝ := (√h)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 hs
  have ha2 : a ^ 2 = h⁻¹ := by
    rw [ha, inv_pow, Real.sq_sqrt hp.le]
  have hha : h * a ^ 2 = 1 := by rw [ha2]; field_simp
  have ha1 : a ≤ 1 := by
    have : a ^ 2 ≤ 1 := by rw [ha2]; exact inv_le_one_of_one_le₀ (by linarith)
    nlinarith
  have hapi : a ≤ π := by linarith [Real.pi_gt_three]
  unfold Zh
  rw [integral_angHaar_eq_interval]
  have hF : ∀ t : ℝ, exp (logq h (t : AngCircle)) =
      exp (-(h * (1 - Real.cos t)) - corr h (1 - Real.cos t)) := by
    intro t; unfold logq; rw [Uang_coe_eq]
  simp_rw [hF]
  have hfc : Continuous fun t : ℝ => exp (-(h * (1 - Real.cos t)) - corr h (1 - Real.cos t)) := by
    have := (continuous_logq h hp).comp Real.Angle.continuous_coe
    have h2 := continuous_exp.comp this
    refine h2.congr ?_
    intro t; simp only [Function.comp_apply]; exact hF t
  have hfi : IntervalIntegrable (fun t : ℝ => exp (-(h * (1 - Real.cos t)) - corr h (1 - Real.cos t)))
      volume (-π) π := hfc.intervalIntegrable _ _
  have hmain : 2 * a * exp (-16) ≤
      ∫ t in (-π)..π, exp (-(h * (1 - Real.cos t)) - corr h (1 - Real.cos t)) := by
    calc 2 * a * exp (-16) = ∫ t in (-a)..a, exp (-16) := by
          rw [intervalIntegral.integral_const]; simp; ring
      _ ≤ ∫ t in (-a)..a, exp (-(h * (1 - Real.cos t)) - corr h (1 - Real.cos t)) := by
          refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
            (hfc.intervalIntegrable _ _) ?_
          intro t ht
          have habs : |t| ≤ a := abs_le.2 ⟨ht.1, ht.2⟩
          have ht2 : t ^ 2 ≤ a ^ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg t) habs 2
            rwa [sq_abs] at this
          have hc1 := Real.cos_le_one t
          have hc2 := Real.neg_one_le_cos t
          have hc3 := Real.one_sub_sq_div_two_le_cos (x := t)
          have hu : (1 - Real.cos t) ∈ Icc (0:ℝ) 2 := ⟨by linarith, by linarith⟩
          have hhu : h * (1 - Real.cos t) ≤ 1 / 2 := by
            have : 1 - Real.cos t ≤ a ^ 2 / 2 := by nlinarith
            nlinarith
          have hc := corr_le_fifteen hh hu (by linarith)
          exact exp_le_exp.2 (by linarith)
      _ ≤ ∫ t in (-π)..π, exp (-(h * (1 - Real.cos t)) - corr h (1 - Real.cos t)) := by
          refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Eventually.of_forall fun t => (exp_pos _).le) hfi
  calc exp (-16) / π * a = (2 * π)⁻¹ * (2 * a * exp (-16)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)

/-- Pointwise lower bound for the density `q_h`. -/
theorem qAng_ge (h : ℝ) (hh : 2 ≤ h) {C0 : ℝ} (hC0 : 0 < C0) (hZ : Zh h ≤ C0 * (√h)⁻¹)
    (θ : AngCircle) :
    1 / (3 * exp 14 * C0) * (√h)⁻¹ * exp (-2 * h) ≤ qAng h θ := by
  have hp : 0 < h := by linarith
  have hs : 0 < √h := Real.sqrt_pos.2 hp
  have hZp := Zh_pos h hp
  obtain ⟨hu0, hu2⟩ := Uang_mem θ
  have hb := (exp_corr_bounds hh (Uang_mem θ)).2
  have hq : exp (logq h θ) = exp (-(h * Uang θ)) / exp (corr h (Uang θ)) := by
    unfold logq; rw [exp_sub]
  have h1 : exp (-2 * h) / (exp 14 * (3 * h)) ≤ exp (logq h θ) := by
    rw [hq]
    calc exp (-2 * h) / (exp 14 * (3 * h)) ≤ exp (-(h * Uang θ)) / (exp 14 * (3 * h)) := by
          gcongr
          nlinarith
      _ ≤ exp (-(h * Uang θ)) / exp (corr h (Uang θ)) := by
          have hcp := exp_pos (corr h (Uang θ))
          refine div_le_div_of_nonneg_left (exp_pos _).le hcp ?_
          refine hb.trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          nlinarith
  have hZinv : (C0 * (√h)⁻¹)⁻¹ ≤ (Zh h)⁻¹ := inv_anti₀ hZp hZ
  unfold qAng
  calc 1 / (3 * exp 14 * C0) * (√h)⁻¹ * exp (-2 * h)
      = (C0 * (√h)⁻¹)⁻¹ * (exp (-2 * h) / (exp 14 * (3 * h))) := by
        have hsq : h = √h * √h := (Real.mul_self_sqrt hp.le).symm
        have e14 := (exp_pos 14).ne'
        field_simp
        exact (Real.sq_sqrt hp.le).symm
    _ ≤ (Zh h)⁻¹ * exp (logq h θ) := by
        gcongr

/-- Integral of `exp(hU)` against `m` equals `e^{2h}` times that of `exp(-hU)`. -/
theorem integral_exp_Uang (h : ℝ) :
    ∫ θ, exp (h * Uang θ) ∂angHaar = exp (2 * h) * ∫ θ, exp (-(h * Uang θ)) ∂angHaar := by
  have := integral_add_right_eq_self (μ := angHaar) (fun θ : AngCircle => exp (h * Uang θ))
    ((π : ℝ) : AngCircle)
  rw [← this, ← integral_const_mul]
  congr 1
  funext θ
  have hc : Uang (θ + ((π : ℝ) : AngCircle)) = 2 - Uang θ := by
    have hcos : Real.Angle.cos ((show Real.Angle from θ) + ((π : ℝ) : Real.Angle)) =
        - Real.Angle.cos (show Real.Angle from θ) :=
      Real.Angle.cos_add_pi _
    unfold Uang
    exact (by rw [show Real.Angle.cos (θ + ((π : ℝ) : AngCircle)) = _ from hcos]; ring)
  rw [hc, ← exp_add]
  congr 1; ring

theorem exp_corr_ge {h : ℝ} (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    exp (-15) * (1 + h * u) ≤ exp (corr h u) := (exp_corr_bounds hh hu).1

/-- Rare-mass estimate before inserting the normalizer bounds. -/
theorem rare_mass_le (h : ℝ) (hh : 2 ≤ h) :
    ∫ θ, exp (2 * h * Uang θ) * qAng h θ ∂angHaar ≤
      (Zh h)⁻¹ * (exp 15 / h * (exp (2 * h) * ∫ θ, exp (-(h * Uang θ)) ∂angHaar) + exp h) := by
  have hp : 0 < h := by linarith
  have hZp := Zh_pos h hp
  have hq : ∀ θ : AngCircle, exp (2 * h * Uang θ) * qAng h θ =
      (Zh h)⁻¹ * exp (h * Uang θ - corr h (Uang θ)) := by
    intro θ
    unfold qAng logq
    have : exp (2 * h * Uang θ) * exp (-(h * Uang θ) - corr h (Uang θ)) =
        exp (h * Uang θ - corr h (Uang θ)) := by
      rw [← exp_add]; congr 1; ring
    rw [← this]; ring
  simp_rw [hq]
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hZp.le)
  have hcont1 : Continuous fun θ : AngCircle => exp (h * Uang θ - corr h (Uang θ)) :=
    ((continuous_const.mul continuous_Uang).sub (continuous_corrU h hp)).rexp
  have hcont2 : Continuous fun θ : AngCircle => exp 15 / h * exp (h * Uang θ) + exp h :=
    ((continuous_const.mul ((continuous_const.mul continuous_Uang).rexp)).add continuous_const)
  have hmono : ∫ θ, exp (h * Uang θ - corr h (Uang θ)) ∂angHaar ≤
      ∫ θ, (exp 15 / h * exp (h * Uang θ) + exp h) ∂angHaar := by
    refine integral_mono (integrable_angHaar_of_continuous hcont1)
      (integrable_angHaar_of_continuous hcont2) ?_
    intro θ
    have hu := Uang_mem θ
    obtain ⟨hu0, hu2⟩ := hu
    have hc0 := corr_nonneg h hp (Uang_mem θ)
    have hE1 := exp_pos (h * Uang θ)
    have hEh := exp_pos h
    by_cases h1 : 1 ≤ Uang θ
    · have hge := exp_corr_ge hh (Uang_mem θ)
      have hcp := exp_pos (corr h (Uang θ))
      have hhh : h ≤ 1 + h * Uang θ := by nlinarith
      have h2 : exp (-15) * h ≤ exp (corr h (Uang θ)) :=
        le_trans (mul_le_mul_of_nonneg_left hhh (exp_pos _).le) hge
      have h3 : exp (h * Uang θ - corr h (Uang θ)) ≤ exp 15 / h * exp (h * Uang θ) := by
        rw [exp_sub, div_le_iff₀ hcp]
        have e15 : exp 15 * exp (-15) = 1 := by rw [← exp_add]; simp
        have h4 : exp 15 / h * exp (h * Uang θ) * exp (corr h (Uang θ)) ≥
            exp 15 / h * exp (h * Uang θ) * (exp (-15) * h) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h5 : exp 15 / h * exp (h * Uang θ) * (exp (-15) * h) = exp (h * Uang θ) := by
          rw [show exp 15 / h * exp (h * Uang θ) * (exp (-15) * h) =
            exp (h * Uang θ) * (exp 15 * exp (-15)) * (h / h) by ring, e15, div_self hp.ne']
          ring
        linarith
      linarith
    · replace h1 := not_le.1 h1
      have h3 : exp (h * Uang θ - corr h (Uang θ)) ≤ exp h := by
        refine exp_le_exp.2 ?_
        nlinarith
      have : 0 ≤ exp 15 / h * exp (h * Uang θ) := by positivity
      linarith
  refine hmono.trans (le_of_eq ?_)
  have i1 : Integrable (fun θ : AngCircle => exp 15 / h * exp (h * Uang θ)) angHaar :=
    integrable_angHaar_of_continuous
      (continuous_const.mul ((continuous_const.mul continuous_Uang).rexp))
  have i2 : Integrable (fun _ : AngCircle => exp h) angHaar :=
    integrable_angHaar_of_continuous continuous_const
  rw [integral_add i1 i2, integral_const_mul, integral_exp_Uang]
  simp

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne

/-- EX036: normalization and rare-mass bounds for the engineered rank-one family.  Here
`Z_h = Zh h = ∫ exp(-hU - R_h(U)) dθ/(2π)`, `q_h = qAng h` is the density of `μ_h` with respect to
the normalized angular Haar measure `m` (`angHaar`), `U = Uang = 1 - cos θ`.  There are absolute
constants `c, C > 0` such that for every `h ≥ 2`: `c h^{-1/2} ≤ Z_h ≤ C h^{-1/2}`,
`q_h θ ≥ c h^{-1/2} exp (-2h)` for all `θ` (so `min q_h` obeys the same bound), and
`μ_h(exp(2hU)) = ∫ exp(2hU) q_h dm ≤ C exp(2h)/h`. -/
theorem engineered_normalization_and_rare_mass_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ h : ℝ, 2 ≤ h →
      (c * h ^ (-(1 / 2 : ℝ)) ≤ Zh h ∧ Zh h ≤ C * h ^ (-(1 / 2 : ℝ))) ∧
      (∀ θ : AngCircle, c * h ^ (-(1 / 2 : ℝ)) * exp (-2 * h) ≤ qAng h θ) ∧
      ∫ θ, exp (2 * h * Uang θ) * qAng h θ ∂angHaar ≤ C * exp (2 * h) / h := by
  have hpi := Real.pi_pos
  obtain ⟨C0, hC0def⟩ : ∃ C0 : ℝ, C0 = (2 * π)⁻¹ * √(π / (2 / π ^ 2)) := ⟨_, rfl⟩
  have hC0 : 0 < C0 := by rw [hC0def]; positivity
  obtain ⟨cz, hczdef⟩ : ∃ cz : ℝ, cz = exp (-16) / π := ⟨_, rfl⟩
  have hcz : 0 < cz := by rw [hczdef]; positivity
  obtain ⟨kq, hkqdef⟩ : ∃ kq : ℝ, kq = 1 / (3 * exp 14 * C0) := ⟨_, rfl⟩
  have hkq : 0 < kq := by rw [hkqdef]; positivity
  obtain ⟨Cr, hCrdef⟩ : ∃ Cr : ℝ, Cr = (exp 15 * C0 + 2) / cz := ⟨_, rfl⟩
  have hCr : 0 < Cr := by rw [hCrdef]; positivity
  refine ⟨min cz kq, max C0 Cr, lt_min hcz hkq, lt_max_of_lt_left hC0, fun h hh => ?_⟩
  have hp : 0 < h := by linarith
  have hs : 0 < √h := Real.sqrt_pos.2 hp
  have hrp : h ^ (-(1 / 2 : ℝ)) = (√h)⁻¹ := by rw [Real.rpow_neg hp.le, Real.sqrt_eq_rpow]
  rw [hrp]
  have ha : 0 < (√h)⁻¹ := inv_pos.2 hs
  have hZu : Zh h ≤ C0 * (√h)⁻¹ := by rw [hC0def]; exact Zh_le h hp
  have hZl : cz * (√h)⁻¹ ≤ Zh h := by rw [hczdef]; exact Zh_ge h hh
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ha.le) hZl
  · exact hZu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le)
  · intro θ
    have := qAng_ge h hh hC0 hZu θ
    rw [← hkqdef] at this
    exact le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right _ _) ha.le) (exp_pos _).le) this
  · have hR := rare_mass_le h hh
    have hI : ∫ θ, exp (-(h * Uang θ)) ∂angHaar ≤ C0 * (√h)⁻¹ := by
      rw [hC0def]; exact integral_exp_neg_Uang_le_sqrt h hp
    have hZinv : (Zh h)⁻¹ ≤ (cz * (√h)⁻¹)⁻¹ := inv_anti₀ (mul_pos hcz ha) hZl
    have hE2 : exp (2 * h) = exp h * exp h := by rw [← exp_add]; ring_nf
    have hEh := exp_pos h
    have hsq : √h * √h = h := Real.mul_self_sqrt hp.le
    have hs1 : 1 ≤ √h := by
      rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hsh : √h ≤ h := by nlinarith
    have hq2 := Real.quadratic_le_exp_of_nonneg hp.le
    have step1 : (Zh h)⁻¹ * (exp 15 / h * (exp (2 * h) * ∫ θ, exp (-(h * Uang θ)) ∂angHaar) + exp h)
        ≤ (cz * (√h)⁻¹)⁻¹ * (exp 15 / h * (exp (2 * h) * (C0 * (√h)⁻¹)) + exp h) := by
      refine mul_le_mul hZinv ?_ (by positivity) (by positivity)
      refine add_le_add_left ?_ _
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI (exp_pos _).le) (by positivity)
    have e1 : (cz * (√h)⁻¹)⁻¹ * (exp 15 / h * (exp (2 * h) * (C0 * (√h)⁻¹)) + exp h)
        = exp 15 * C0 / cz * (exp (2 * h) / h) + √h * exp h / cz := by
      have hcz' := hcz.ne'
      have hs' := hs.ne'
      have hp' := hp.ne'
      field_simp
    have e2 : √h * exp h ≤ 2 * exp (2 * h) / h := by
      rw [le_div_iff₀ hp]
      have a1 : √h * exp h * h ≤ h * exp h * h := by gcongr
      have a2 : h * exp h * h ≤ (2 * exp h) * exp h := by
        have : h ^ 2 ≤ 2 * exp h := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this hEh.le]
      rw [hE2]; linarith
    have e3 : √h * exp h / cz ≤ 2 / cz * (exp (2 * h) / h) := by
      rw [div_le_iff₀ hcz]
      have : 2 / cz * (exp (2 * h) / h) * cz = 2 * exp (2 * h) / h := by
        field_simp
      rw [this]; exact e2
    have e4 : exp 15 * C0 / cz * (exp (2 * h) / h) + 2 / cz * (exp (2 * h) / h)
        = Cr * exp (2 * h) / h := by
      rw [hCrdef]; field_simp
    calc ∫ θ, exp (2 * h * Uang θ) * qAng h θ ∂angHaar
        ≤ _ := hR
      _ ≤ _ := step1
      _ = _ := e1
      _ ≤ exp 15 * C0 / cz * (exp (2 * h) / h) + 2 / cz * (exp (2 * h) / h) := by linarith
      _ = Cr * exp (2 * h) / h := e4
      _ ≤ max C0 Cr * exp (2 * h) / h := by
        have := exp_pos (2 * h)
        gcongr
        exact le_max_right _ _

end DGPS.Examples
