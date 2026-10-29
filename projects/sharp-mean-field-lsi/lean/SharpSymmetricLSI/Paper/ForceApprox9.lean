import SharpSymmetricLSI.Paper.GaussLaw6

/-!
# R31 groundwork: Hölder with exponential moments

`x^r ≤ (r/a)^r e^{ax}` (`x ≥ 0`), and for `w, G ≥ 0`, `1/p + 1/q = 1`:
`∫ wG ≤ ‖w‖_p ((∫G)^{1/2} (c_q ∫e^{aG})^{1/2})^{1/q}`, `c_q = ((2q-1)/a)^{2q-1}`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

theorem rpow_le_mul_exp {x r a : ℝ} (hx : 0 ≤ x) (hr : 0 < r) (ha : 0 < a) :
    x ^ r ≤ (r / a) ^ r * rexp (a * x) := by
  rcases hx.eq_or_lt with h | h
  · subst h; rw [Real.zero_rpow hr.ne']; positivity
  have hy : 0 < a * x / r := by positivity
  have hlog := Real.log_le_sub_one_of_pos hy
  have h1 : x ^ r = (r / a) ^ r * (a * x / r) ^ r := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.rpow_def_of_pos hy]
  refine Real.exp_le_exp.2 ?_
  calc Real.log (a * x / r) * r ≤ (a * x / r - 1) * r := mul_le_mul_of_nonneg_right hlog hr.le
    _ ≤ a * x := by
        have : (a * x / r - 1) * r = a * x - r := by field_simp
        rw [this]; linarith

theorem lintegral_mul_le_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {w G : Ω → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hG0 : ∀ x, 0 ≤ G x) (hwm : AEMeasurable w P)
    (hGm : AEMeasurable G P) {p q : ℝ} (hpq : p.HolderConjugate q) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, ENNReal.ofReal (w x * G x) ∂P ≤
      (∫⁻ x, ENNReal.ofReal (w x ^ p) ∂P) ^ (1 / p) *
        ((∫⁻ x, ENNReal.ofReal (G x) ∂P) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (((2 * q - 1) / a) ^ (2 * q - 1)) *
            ∫⁻ x, ENNReal.ofReal (rexp (a * G x)) ∂P) ^ (1 / 2 : ℝ)) ^ (1 / q) := by
  have hq1 : 1 < q := hpq.symm.lt
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set f : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (w x)
  set g : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (G x)
  have hfm : AEMeasurable f P := hwm.ennreal_ofReal
  have hgm : AEMeasurable g P := hGm.ennreal_ofReal
  -- Hölder with `p, q`
  have h1 : ∫⁻ x, ENNReal.ofReal (w x * G x) ∂P ≤
      (∫⁻ x, f x ^ p ∂P) ^ (1 / p) * (∫⁻ x, g x ^ q ∂P) ^ (1 / q) := by
    refine le_of_eq_of_le ?_ (ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hfm hgm)
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply, f, g]
    rw [ENNReal.ofReal_mul (hw0 x)]
  have hfp : ∫⁻ x, f x ^ p ∂P = ∫⁻ x, ENNReal.ofReal (w x ^ p) ∂P :=
    lintegral_congr fun x => ENNReal.ofReal_rpow_of_nonneg (hw0 x) hp0.le
  -- Cauchy–Schwarz for `g^q = g^{1/2} g^{q-1/2}`
  have h2 : ∫⁻ x, g x ^ q ∂P ≤
      (∫⁻ x, g x ∂P) ^ (1 / 2 : ℝ) * (∫⁻ x, g x ^ (2 * q - 1) ∂P) ^ (1 / 2 : ℝ) := by
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
      (hgm.pow_const (1 / 2 : ℝ)) (hgm.pow_const (q - 1 / 2))
    refine le_of_eq_of_le ?_ (hcs.trans (le_of_eq ?_))
    · refine lintegral_congr fun x => ?_
      simp only [Pi.mul_apply]
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by linarith)]
      congr 1; ring
    · congr 2
      · refine lintegral_congr fun x => ?_
        rw [← ENNReal.rpow_mul]; norm_num
      · refine lintegral_congr fun x => ?_
        rw [← ENNReal.rpow_mul]; congr 1; ring
  -- moments from the exponential moment
  have h3 : ∫⁻ x, g x ^ (2 * q - 1) ∂P ≤ ENNReal.ofReal (((2 * q - 1) / a) ^ (2 * q - 1)) *
      ∫⁻ x, ENNReal.ofReal (rexp (a * G x)) ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    simp only [g]
    rw [ENNReal.ofReal_rpow_of_nonneg (hG0 x) (by linarith),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg (by linarith) ha.le) _)]
    exact ENNReal.ofReal_le_ofReal (rpow_le_mul_exp (hG0 x) (by linarith) ha)
  rw [hfp] at h1
  refine h1.trans (mul_le_mul_right ?_ _)
  refine ENNReal.rpow_le_rpow (h2.trans ?_) (by positivity)
  exact mul_le_mul_right (ENNReal.rpow_le_rpow h3 (by norm_num)) _

end SharpLSI
