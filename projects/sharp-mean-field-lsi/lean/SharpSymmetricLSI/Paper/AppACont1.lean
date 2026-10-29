import SharpSymmetricLSI.Paper.AppAEvol3

/-!
# Continuity in time of linear mild solutions (1): mode bounds

`|b_n|² ≤ λ_n ∑ₖ |N̂ₖ(n)|²` (Cauchy–Schwarz), hence
`|D_n(s)|² ≤ ∫_{(0,T]} ∑ₖ |N̂_{v,k}(n)|² dv` uniformly in `s ∈ [0,T]` (weighted Cauchy–Schwarz and
`∫ e^{-λ(s-v)} ≤ 1/λ`), a summable bound.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem norm_sum_mul_sq_le (a c : ι → ℂ) :
    ‖∑ k, a k * c k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖c k‖ ^ 2 := by
  have h1 : ‖∑ k, a k * c k‖ ≤ ∑ k, ‖a k‖ * ‖c k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖c k‖)
  calc ‖∑ k, a k * c k‖ ^ 2 ≤ (∑ k, ‖a k‖ * ‖c k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem sum_norm_two_pi_sq (n : ι → ℤ) :
    ∑ k, ‖(2 * π * I * n k : ℂ)‖ ^ 2 = lamN n := by
  unfold lamN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
    show ((n k : ℤ) : ℂ) = (((n k : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring

/-- Weighted Cauchy–Schwarz for the Duhamel mode. -/
theorem norm_modeD_sq_le {lam : ℝ} (hlam : 0 < lam) {b : ℝ → ℂ} (hbm : Measurable b) {B : ℝ}
    (hbB : ∀ v, ‖b v‖ ≤ B) {s T : ℝ} (hs : s ∈ Icc 0 T) :
    ‖modeD lam b s‖ ^ 2 ≤ (1 / lam) * ∫ v in Ioc 0 T, ‖b v‖ ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) s)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set e : ℝ → ℝ := fun v => Real.exp (-lam * (s - v)) with he
  have hem : Measurable e := by fun_prop
  have hD : ‖modeD lam b s‖ ≤ ∫ v in Ioc 0 s, Real.sqrt (e v) * (Real.sqrt (e v) * ‖b v‖) := by
    unfold modeD
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioc fun v _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← mul_assoc,
      Real.mul_self_sqrt (Real.exp_pos _).le]
  have hf : MemLp (fun v => Real.sqrt (e v)) (ENNReal.ofReal 2) (volume.restrict (Ioc 0 s)) :=
    MemLp.of_bound (Real.continuous_sqrt.measurable.comp hem).aestronglyMeasurable 1
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
        exact Real.exp_le_one_iff.2 (by nlinarith [hv.2])))
  have hg : MemLp (fun v => Real.sqrt (e v) * ‖b v‖) (ENNReal.ofReal 2) (volume.restrict (Ioc 0 s)) :=
    MemLp.of_bound ((Real.continuous_sqrt.measurable.comp hem).mul hbm.norm).aestronglyMeasurable B
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h1 : Real.sqrt (e v) ≤ 1 := by
          rw [Real.sqrt_le_one]; exact Real.exp_le_one_iff.2 (by nlinarith [hv.2])
        calc Real.sqrt (e v) * ‖b v‖ ≤ 1 * B := mul_le_mul h1 (hbB v) (norm_nonneg _) zero_le_one
          _ = B := one_mul B))
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Eventually.of_forall fun v => Real.sqrt_nonneg _)
    (Eventually.of_forall fun v => by positivity) hf hg
  have e1 : ∀ v, Real.sqrt (e v) ^ (2 : ℝ) = e v := fun v => by
    rw [Real.rpow_two, Real.sq_sqrt (Real.exp_pos _).le]
  have e2 : ∀ v, (Real.sqrt (e v) * ‖b v‖) ^ (2 : ℝ) = e v * ‖b v‖ ^ 2 := fun v => by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (Real.exp_pos _).le]
  simp_rw [e1, e2, ← Real.sqrt_eq_rpow] at hH
  set X := ∫ v in Ioc 0 s, e v
  set Y := ∫ v in Ioc 0 s, e v * ‖b v‖ ^ 2
  have hX0 : 0 ≤ X := integral_nonneg fun v => (Real.exp_pos _).le
  have hY0 : 0 ≤ Y := integral_nonneg fun v => by positivity
  have hDsq : ‖modeD lam b s‖ ^ 2 ≤ X * Y := by
    calc ‖modeD lam b s‖ ^ 2 ≤ (Real.sqrt X * Real.sqrt Y) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hD.trans hH) 2
      _ = X * Y := by rw [mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hY0]
  have hX : X ≤ 1 / lam := by
    have hd : ∀ v ∈ uIcc 0 s, HasDerivAt (fun v => Real.exp (-lam * (s - v)))
        (lam * Real.exp (-lam * (s - v))) v := fun v _ => by
      have h1 : HasDerivAt (fun v : ℝ => -lam * (s - v)) lam v := by
        simpa using ((hasDerivAt_id v).const_sub s).const_mul (-lam)
      have := h1.exp
      convert this using 1; ring
    have hi : IntervalIntegrable (fun v => lam * Real.exp (-lam * (s - v))) volume 0 s :=
      (by fun_prop : Continuous fun v : ℝ => lam * Real.exp (-lam * (s - v))).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    rw [intervalIntegral.integral_of_le hs.1, integral_const_mul] at h
    simp only [sub_self, mul_zero, Real.exp_zero] at h
    rw [le_div_iff₀ hlam, mul_comm, show lam * X = 1 - Real.exp (-lam * (s - 0)) from h]
    linarith [Real.exp_pos (-lam * (s - 0))]
  have hY : Y ≤ ∫ v in Ioc 0 T, ‖b v‖ ^ 2 := by
    have hbi : IntegrableOn (fun v => ‖b v‖ ^ 2) (Ioc 0 T) :=
      (integrable_const (B ^ 2)).mono' (hbm.norm.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hbB v) 2)
    calc Y ≤ ∫ v in Ioc 0 s, ‖b v‖ ^ 2 := by
          refine setIntegral_mono_on ?_ (hbi.mono_set (Ioc_subset_Ioc le_rfl hs.2)) measurableSet_Ioc
            fun v hv => ?_
          · exact (hbi.mono_set (Ioc_subset_Ioc le_rfl hs.2)).mono'
              (hem.mul (hbm.norm.pow_const 2)).aestronglyMeasurable
              ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
                rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                exact mul_le_of_le_one_left (by positivity)
                  (Real.exp_le_one_iff.2 (by nlinarith [hv.2]))))
          · exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.2 (by nlinarith [hv.2]))
      _ ≤ ∫ v in Ioc 0 T, ‖b v‖ ^ 2 :=
          setIntegral_mono_set hbi (Eventually.of_forall fun v => by positivity)
            (Ioc_subset_Ioc le_rfl hs.2).eventuallyLE
  calc ‖modeD lam b s‖ ^ 2 ≤ X * Y := hDsq
    _ ≤ (1 / lam) * ∫ v in Ioc 0 T, ‖b v‖ ^ 2 := mul_le_mul hX hY hY0 (by positivity)

end SharpLSI
