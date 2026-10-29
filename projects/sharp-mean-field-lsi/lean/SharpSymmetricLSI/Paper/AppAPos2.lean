import SharpSymmetricLSI.Paper.AppAPos1

/-!
# Positivity (2): the integrated mode equation

For `a(t) = e^{-λt} c + ∫_{(0,t]} e^{-λ(t-v)} b(v) dv` (bounded measurable `b`):
`a(t) = c + ∫_{(0,t]} (-λ a(u) + b(u)) du` (`mode_ode`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- The Duhamel part `D(t) = ∫_{(0,t]} e^{-λ(t-v)} b(v) dv`. -/
noncomputable def modeD (lam : ℝ) (b : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ v in Ioc 0 t, (Real.exp (-lam * (t - v)) : ℂ) * b v

section Mode

variable {lam : ℝ} (hlam : 0 ≤ lam) {b : ℝ → ℂ} (hbm : Measurable b) {B : ℝ}
  (hbB : ∀ v, ‖b v‖ ≤ B)
include hlam hbm hbB

theorem norm_modeD_le {t : ℝ} (ht : 0 ≤ t) : ‖modeD lam b t‖ ≤ B * t := by
  unfold modeD
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  refine (norm_setIntegral_le_of_norm_le_const (C := B) (by simp) fun v hv => ?_).trans
    (le_of_eq ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-lam * (t - v)) * ‖b v‖ ≤ 1 * B := by
          gcongr
          · exact Real.exp_le_one_iff.2 (by nlinarith [hv.2])
          · exact hbB v
      _ = B := one_mul B
  · simp [mul_comm, ht]

theorem measurable_modeD : Measurable (modeD lam b) := by
  have hm : Measurable (Function.uncurry fun (t v : ℝ) =>
      (Ioc 0 t).indicator (fun v => (Real.exp (-lam * (t - v)) : ℂ) * b v) v) := by
    have e : (Function.uncurry fun (t v : ℝ) =>
        (Ioc 0 t).indicator (fun v => (Real.exp (-lam * (t - v)) : ℂ) * b v) v) =
        {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}.indicator
          (fun p => (Real.exp (-lam * (p.1 - p.2)) : ℂ) * b p.2) := by
      funext p; simp [Set.indicator, Function.uncurry]
    rw [e]
    refine Measurable.indicator ?_ ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst))
    exact (Complex.measurable_ofReal.comp (by fun_prop)).mul (hbm.comp measurable_snd)
  have := hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  have e2 : modeD lam b = fun t => ∫ v, (Ioc 0 t).indicator
      (fun v => (Real.exp (-lam * (t - v)) : ℂ) * b v) v := by
    funext t; unfold modeD; rw [integral_indicator measurableSet_Ioc]
  rw [e2]; exact this.measurable

omit hbm hbB in
theorem lam_integral_exp {v t : ℝ} (hvt : v ≤ t) :
    lam * ∫ u in Ioc v t, Real.exp (-lam * (u - v)) = 1 - Real.exp (-lam * (t - v)) := by
  have hd : ∀ u ∈ uIcc v t, HasDerivAt (fun u => -Real.exp (-lam * (u - v)))
      (lam * Real.exp (-lam * (u - v))) u := fun u _ => by
    have h1 : HasDerivAt (fun u => -lam * (u - v)) (-lam) u := by
      simpa using ((hasDerivAt_id u).sub_const v).const_mul (-lam)
    have := h1.exp.neg
    convert this using 1; ring
  have hi : IntervalIntegrable (fun u => lam * Real.exp (-lam * (u - v))) volume v t :=
    (by fun_prop : Continuous fun u => lam * Real.exp (-lam * (u - v))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_of_le hvt, integral_const_mul] at h
  rw [h]; simp; ring

/-- `λ ∫₀ᵗ D = ∫₀ᵗ b - D(t)`. -/
theorem lam_integral_modeD {t : ℝ} (ht : 0 ≤ t) :
    (lam : ℂ) * ∫ u in Ioc 0 t, modeD lam b u = (∫ v in Ioc 0 t, b v) - modeD lam b t := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  set F : ℝ × ℝ → ℂ := fun p => if p.2 ≤ p.1 then (Real.exp (-lam * (p.1 - p.2)) : ℂ) * b p.2
    else 0 with hF
  have hFm : Measurable F := by
    refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ measurable_const
    exact (Complex.measurable_ofReal.comp (by fun_prop)).mul (hbm.comp measurable_snd)
  have hFb : ∀ p, ‖F p‖ ≤ B := fun p => by
    simp only [hF]
    split_ifs with h
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-lam * (p.1 - p.2)) * ‖b p.2‖ ≤ 1 * B := by
            gcongr
            · exact Real.exp_le_one_iff.2 (by nlinarith)
            · exact hbB _
        _ = B := one_mul B
    · simpa using hB0
  have hFi : Integrable F ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) := isFiniteMeasure_restrict.2 (by simp)
    exact (integrable_const B).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall fun p => hFb p)
  -- the inner integrals
  have hD : ∀ u ∈ Ioc 0 t, modeD lam b u = ∫ v in Ioc 0 t, F (u, v) := by
    intro u hu
    unfold modeD
    have e : (fun v => F (u, v)) = (Iic u).indicator
        (fun v => (Real.exp (-lam * (u - v)) : ℂ) * b v) := by
      funext v; simp only [hF, Set.indicator, mem_Iic]
    rw [e, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hu.2]
  have hI : ∀ v ∈ Ioc 0 t, (lam : ℂ) * ∫ u in Ioc 0 t, F (u, v) =
      b v - (Real.exp (-lam * (t - v)) : ℂ) * b v := by
    intro v hv
    have e : (fun u => F (u, v)) = (Ici v).indicator
        (fun u => (Real.exp (-lam * (u - v)) : ℂ) * b v) := by
      funext u; simp only [hF, Set.indicator, mem_Ici]
    have hset : Ioc 0 t ∩ Ici v = Icc v t := by
      ext u; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hv.1 h1, h2⟩, h1⟩
    rw [e, setIntegral_indicator measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
      integral_mul_const, integral_complex_ofReal]
    have hc := lam_integral_exp hlam hv.2
    have : (lam : ℂ) * ((∫ u in Ioc v t, Real.exp (-lam * (u - v)) : ℝ) : ℂ) =
        ((1 - Real.exp (-lam * (t - v)) : ℝ) : ℂ) := by rw [← hc]; push_cast; ring
    rw [← mul_assoc, this]; push_cast; ring
  calc (lam : ℂ) * ∫ u in Ioc 0 t, modeD lam b u
      = (lam : ℂ) * ∫ u in Ioc 0 t, ∫ v in Ioc 0 t, F (u, v) := by
        rw [setIntegral_congr_fun measurableSet_Ioc hD]
    _ = (lam : ℂ) * ∫ v in Ioc 0 t, ∫ u in Ioc 0 t, F (u, v) := by
        rw [integral_integral_swap hFi]
    _ = ∫ v in Ioc 0 t, (lam : ℂ) * ∫ u in Ioc 0 t, F (u, v) := by rw [integral_const_mul]
    _ = ∫ v in Ioc 0 t, (b v - (Real.exp (-lam * (t - v)) : ℂ) * b v) :=
        setIntegral_congr_fun measurableSet_Ioc hI
    _ = (∫ v in Ioc 0 t, b v) - modeD lam b t := by
        haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
          isFiniteMeasure_restrict.2 (by simp)
        have hbi : Integrable b (volume.restrict (Ioc 0 t)) :=
          (integrable_const B).mono' hbm.aestronglyMeasurable (Eventually.of_forall hbB)
        have hb2 : Integrable (fun v => (Real.exp (-lam * (t - v)) : ℂ) * b v)
            (volume.restrict (Ioc 0 t)) := by
          refine (integrable_const B).mono' ((Complex.measurable_ofReal.comp (by fun_prop)).mul
            hbm).aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).2
              (Eventually.of_forall fun v hv => ?_))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          calc Real.exp (-lam * (t - v)) * ‖b v‖ ≤ 1 * B := by
                gcongr
                · exact Real.exp_le_one_iff.2 (by nlinarith [hv.2])
                · exact hbB v
            _ = B := one_mul B
        rw [integral_sub hbi hb2]; rfl

/-- **The integrated mode equation.** -/
theorem mode_ode (c : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (-lam * t) : ℂ) * c + modeD lam b t =
      c + ∫ u in Ioc 0 t, (-(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u) + b u) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) := isFiniteMeasure_restrict.2 (by simp)
  have hDm := measurable_modeD hlam hbm hbB
  have hDi : Integrable (modeD lam b) (volume.restrict (Ioc 0 t)) := by
    refine (integrable_const (B * t)).mono' hDm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_))
    exact (norm_modeD_le hlam hbm hbB hu.1.le).trans (by gcongr; exact hu.2)
  have hEi : Integrable (fun u => (Real.exp (-lam * u) : ℂ) * c) (volume.restrict (Ioc 0 t)) :=
    ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun u : ℝ => Real.exp (-lam * u))).mul
      continuous_const).integrableOn_Ioc
  have hbi : Integrable b (volume.restrict (Ioc 0 t)) :=
    (integrable_const B).mono' hbm.aestronglyMeasurable (Eventually.of_forall hbB)
  have hE : (lam : ℂ) * ∫ u in Ioc 0 t, (Real.exp (-lam * u) : ℂ) * c =
      (1 - Real.exp (-lam * t) : ℝ) * c := by
    rw [integral_mul_const, integral_complex_ofReal]
    have := lam_integral_exp hlam ht
    simp only [sub_zero] at this
    rw [← this]; push_cast; ring
  have hD := lam_integral_modeD hlam hbm hbB ht
  have e : (fun u => -(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u) + b u) =
      fun u => (-(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c) + -(lam : ℂ) * modeD lam b u) + b u := by
    funext u; ring
  have h1 := (hEi.const_mul (-(lam : ℂ)))
  have h2 := (hDi.const_mul (-(lam : ℂ)))
  rw [e, integral_add (f := fun u => -(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c) +
      -(lam : ℂ) * modeD lam b u) (h1.add h2) hbi,
    integral_add (f := fun u => -(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c))
      (g := fun u => -(lam : ℂ) * modeD lam b u) h1 h2, integral_const_mul, integral_const_mul]
  push_cast at hE ⊢
  linear_combination hE + hD

end Mode

end SharpLSI
