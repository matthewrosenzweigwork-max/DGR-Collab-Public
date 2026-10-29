import SharpSymmetricLSI.Paper.AppAEvol4

/-!
# `L²_t H¹_x` regularity of linear mild solutions (1): mode estimates

For `λ > 0`: `|D(u)|² ≤ λ⁻¹ ∫_{(0,u]} e^{-λ(u-v)} |b(v)|² dv`, hence (Tonelli)
`∫_{(0,T]} |D|² ≤ λ⁻² ∫_{(0,T]} |b|²`, and
`λ ∫_{(0,T]} |a(u)|² ≤ |a(0)|² + 2 λ⁻¹ ∫_{(0,T]} |b|²`.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

section Mode

variable {lam : ℝ} (hlam : 0 < lam) {b : ℝ → ℂ} (hbm : Measurable b) {B : ℝ}
  (hbB : ∀ v, ‖b v‖ ≤ B)
include hlam hbm hbB

/-- Weighted Cauchy–Schwarz, pointwise in `u`. -/
theorem norm_modeD_sq_le_weighted {s : ℝ} (hs : 0 ≤ s) :
    ‖modeD lam b s‖ ^ 2 ≤ (1 / lam) * ∫ v in Ioc 0 s, Real.exp (-lam * (s - v)) * ‖b v‖ ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) s)) :=
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
    rw [intervalIntegral.integral_of_le hs, integral_const_mul] at h
    simp only [sub_self, mul_zero, Real.exp_zero] at h
    rw [le_div_iff₀ hlam, mul_comm, show lam * X = 1 - Real.exp (-lam * (s - 0)) from h]
    linarith [Real.exp_pos (-lam * (s - 0))]
  calc ‖modeD lam b s‖ ^ 2 ≤ X * Y := hDsq
    _ ≤ (1 / lam) * Y := mul_le_mul_of_nonneg_right hX hY0

/-- Young's inequality for the Duhamel mode: `∫₀ᵀ |D|² ≤ λ⁻² ∫₀ᵀ |b|²`. -/
theorem integral_norm_modeD_sq_le {T : ℝ} (hT : 0 ≤ T) :
    ∫ u in Ioc 0 T, ‖modeD lam b u‖ ^ 2 ≤ (1 / lam) ^ 2 * ∫ v in Ioc 0 T, ‖b v‖ ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set F : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then Real.exp (-lam * (p.1 - p.2)) * ‖b p.2‖ ^ 2
    else 0 with hF
  have hFm : Measurable F := by
    refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ measurable_const
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-lam * (p.1 - p.2))).mul
      ((hbm.comp measurable_snd).norm.pow_const 2)
  have hFb : ∀ p, ‖F p‖ ≤ B ^ 2 := fun p => by
    simp only [hF]
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc Real.exp (-lam * (p.1 - p.2)) * ‖b p.2‖ ^ 2 ≤ 1 * B ^ 2 := by
            gcongr
            · exact Real.exp_le_one_iff.2 (by nlinarith)
            · exact hbB _
        _ = B ^ 2 := one_mul _
    · simp; positivity
  have hFi : Integrable F ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))) :=
    (integrable_const (B ^ 2)).mono' hFm.aestronglyMeasurable (Eventually.of_forall hFb)
  -- the inner integrals
  have hinner : ∀ u ∈ Ioc 0 T, ∫ v in Ioc 0 u, Real.exp (-lam * (u - v)) * ‖b v‖ ^ 2 =
      ∫ v in Ioc 0 T, F (u, v) := by
    intro u hu
    have e : (fun v => F (u, v)) = (Iic u).indicator
        (fun v => Real.exp (-lam * (u - v)) * ‖b v‖ ^ 2) := by
      funext v; simp only [hF, Set.indicator, mem_Iic]
    rw [e, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hu.2]
  have houter : ∀ v ∈ Ioc 0 T, ∫ u in Ioc 0 T, F (u, v) ≤ (1 / lam) * ‖b v‖ ^ 2 := by
    intro v hv
    have e : (fun u => F (u, v)) = (Ici v).indicator
        (fun u => Real.exp (-lam * (u - v)) * ‖b v‖ ^ 2) := by
      funext u; simp only [hF, Set.indicator, mem_Ici]
    have hset : Ioc 0 T ∩ Ici v = Icc v T := by
      ext u; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hv.1 h1, h2⟩, h1⟩
    rw [e, setIntegral_indicator measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
      integral_mul_const]
    have hc := lam_integral_exp hlam.le hv.2
    have : ∫ u in Ioc v T, Real.exp (-lam * (u - v)) ≤ 1 / lam := by
      rw [le_div_iff₀ hlam, mul_comm, hc]; linarith [Real.exp_pos (-lam * (T - v))]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hDm := measurable_modeD hlam.le hbm hbB
  have hbi : Integrable (fun v => ‖b v‖ ^ 2) (volume.restrict (Ioc 0 T)) :=
    (integrable_const (B ^ 2)).mono' (hbm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbB v) 2)
  calc ∫ u in Ioc 0 T, ‖modeD lam b u‖ ^ 2
      ≤ ∫ u in Ioc 0 T, (1 / lam) * ∫ v in Ioc 0 T, F (u, v) := by
        refine setIntegral_mono_on ?_ (hFi.integral_prod_left.const_mul _) measurableSet_Ioc
          fun u hu => ?_
        · exact (integrable_const ((B * T) ^ 2)).mono' (hDm.norm.pow_const 2).aestronglyMeasurable
            ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => by
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
              exact pow_le_pow_left₀ (norm_nonneg _) ((norm_modeD_le hlam.le hbm hbB hu.1.le).trans
                (by gcongr; exact hu.2)) 2))
        · rw [← hinner u hu]; exact norm_modeD_sq_le_weighted hlam hbm hbB hu.1.le
    _ = (1 / lam) * ∫ v in Ioc 0 T, ∫ u in Ioc 0 T, F (u, v) := by
        rw [integral_const_mul, integral_integral_swap hFi]
    _ ≤ (1 / lam) * ∫ v in Ioc 0 T, (1 / lam) * ‖b v‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_on hFi.integral_prod_right
          (hbi.const_mul _) measurableSet_Ioc houter) (by positivity)
    _ = (1 / lam) ^ 2 * ∫ v in Ioc 0 T, ‖b v‖ ^ 2 := by rw [integral_const_mul]; ring

end Mode

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

theorem measurable_cf_section (n : ι → ℤ) : Measurable fun u => cf (ρ u) n := by
  simp only [cf]
  simp_rw [mFourierCoeff_eq_integral]
  have hm : StronglyMeasurable (fun p : ℝ × UnitAddTorus ι => mFourier (-n) p.2 • ((ρ p.1 p.2 : ℝ) : ℂ)) :=
    (((mFourier (-n)).continuous.measurable.comp measurable_snd).smul
      (Complex.measurable_ofReal.comp h.meas)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

/-- **The `H¹` energy of a mode.** -/
theorem lam_integral_norm_cf_sq_le {T K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) (hT : 0 ≤ T) (n : ι → ℤ) :
    lamN n * ∫ u in Ioc 0 T, ‖cf (ρ u) n‖ ^ 2 ≤ ‖cf ρ₀ n‖ ^ 2 + 2 * modeW N T n := by
  have hW0 : 0 ≤ modeW N T n := setIntegral_nonneg measurableSet_Ioc fun v _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg _
  rcases (lamN_nonneg n).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set lam := lamN n
  set c := cf ρ₀ n
  set b := modeB N T n
  have hbm := h.measurable_modeB T n
  have hbB := h.norm_modeB_le hK0 hK n
  set B := ∑ k : ι, 2 * π * |(n k : ℝ)| * (A * K)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  have hDm := measurable_modeD hpos.le hbm hbB
  -- pointwise
  have hpt : ∀ u ∈ Ioc 0 T, ‖cf (ρ u) n‖ ^ 2 ≤
      2 * (Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2) + 2 * ‖modeD lam b u‖ ^ 2 := by
    intro u hu
    rw [h.cf_eq_mode hK0 hK n ⟨hu.1.le, hu.2⟩]
    have he : ‖(Real.exp (-lam * u) : ℂ) * c‖ ^ 2 = Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
        ← Real.exp_nat_mul]
      congr 2; push_cast; ring
    rw [← he]
    have := norm_add_le ((Real.exp (-lam * u) : ℂ) * c) (modeD lam b u)
    nlinarith [sq_nonneg (‖(Real.exp (-lam * u) : ℂ) * c‖ - ‖modeD lam b u‖), norm_nonneg
      ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u)]
  have hEi : IntegrableOn (fun u => Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2) (Ioc 0 T) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2).integrableOn_Ioc
  have hDi : IntegrableOn (fun u => ‖modeD lam b u‖ ^ 2) (Ioc 0 T) :=
    (integrable_const ((B * T) ^ 2)).mono' (hDm.norm.pow_const 2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_modeD_le hpos.le hbm hbB hu.1.le).trans
          (by gcongr; exact hu.2)) 2))
  have hai : IntegrableOn (fun u => ‖cf (ρ u) n‖ ^ 2) (Ioc 0 T) :=
    (integrable_const (K ^ 2)).mono' ((h.measurable_cf_section n).norm.pow_const 2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (h.norm_cf_le (h.measurable_section u)
          (hK u ⟨hu.1.le, hu.2⟩) n) 2))
  -- the exponential part
  have hexp : lam * ∫ u in Ioc 0 T, Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2 ≤ ‖c‖ ^ 2 / 2 := by
    rw [integral_mul_const]
    have hc := lam_integral_exp (lam := 2 * lam) (by positivity) (v := 0) hT
    simp only [sub_zero] at hc
    have : (2 * lam) * ∫ u in Ioc 0 T, Real.exp (-(2 * lam) * u) ≤ 1 := by
      rw [hc]; linarith [Real.exp_pos (-(2 * lam) * T)]
    have hc2 : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    nlinarith
  -- the Duhamel part
  have hD := integral_norm_modeD_sq_le hpos hbm hbB hT
  have hb2 : ∫ v in Ioc 0 T, ‖b v‖ ^ 2 ≤ lam * modeW N T n := by
    unfold modeW
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) ?_
      (Eventually.of_forall fun v => h.norm_modeB_sq_le T n v)
    exact (integrable_const (lam * (Fintype.card ι * (A * K) ^ 2))).mono'
      ((h.measurable_cf_sq n).const_mul _).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
        have hv' : v ∈ Icc 0 T := ⟨hv.1.le, hv.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le
          (Finset.sum_nonneg fun k _ => sq_nonneg _))]
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        calc ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2 ≤ ∑ _k : ι, (A * K) ^ 2 :=
              Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
                (h.norm_cf_le (h.measurable_sectionN v k) (fun z => h.abs_N_le hK hv' z k) n) 2
          _ = _ := by simp))
  have hsum : IntegrableOn (fun u => 2 * (Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2) +
      2 * ‖modeD lam b u‖ ^ 2) (Ioc 0 T) := (hEi.const_mul 2).add (hDi.const_mul 2)
  calc lam * ∫ u in Ioc 0 T, ‖cf (ρ u) n‖ ^ 2
      ≤ lam * ∫ u in Ioc 0 T, (2 * (Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2) +
          2 * ‖modeD lam b u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hai hsum measurableSet_Ioc hpt) hpos.le
    _ = 2 * (lam * ∫ u in Ioc 0 T, Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2) +
          2 * lam * ∫ u in Ioc 0 T, ‖modeD lam b u‖ ^ 2 := by
        rw [integral_add (f := fun u => 2 * (Real.exp (-(2 * lam) * u) * ‖c‖ ^ 2))
          (g := fun u => 2 * ‖modeD lam b u‖ ^ 2) (hEi.const_mul 2) (hDi.const_mul 2),
          integral_const_mul, integral_const_mul]
        ring
    _ ≤ 2 * (‖c‖ ^ 2 / 2) + 2 * lam * ((1 / lam) ^ 2 * (lam * modeW N T n)) := by
        gcongr
        exact hD.trans (mul_le_mul_of_nonneg_left hb2 (by positivity))
    _ = ‖c‖ ^ 2 + 2 * modeW N T n := by field_simp

end LinMild

end SharpLSI
