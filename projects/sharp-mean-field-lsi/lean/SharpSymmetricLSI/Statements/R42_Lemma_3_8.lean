import SharpSymmetricLSI.Infra.Entropy

/-!
# R42: Lemma 3.8 (`lem:cosine-centering`), centering

Manuscript Lemma 3.8, (3.40): for every probability measure `P` and every real `f ∈ L²(P)`,
`Ent_P(f²) ≤ 2 Ent_P((f - E_P f)²) + 8 Var_P(f)` (in `ℝ≥0∞`).
-/

open MeasureTheory

namespace SharpLSI

/-- Lemma 3.8. -/
theorem ent_le_two_centered {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {f : α → ℝ} (hf : MemLp f 2 P) :
    ent P (fun x => f x ^ 2) ≤
      2 * ent P (fun x => (f x - ∫ y, f y ∂P) ^ 2) + 8 * var P f := by
  -- `s log (s/a) ≤ s log (q/a) + s²/q - s` for `s ≥ 0`, `q, a > 0`
  have L1 : ∀ s q a : ℝ, 0 ≤ s → 0 < q → 0 < a →
      s * Real.log (s / a) ≤ s * Real.log (q / a) + s ^ 2 / q - s := by
    intro s q a hs hq ha
    rcases hs.eq_or_lt with h0 | h0
    · subst h0; simp
    · have h1 : Real.log (s / a) = Real.log (s / q) + Real.log (q / a) := by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
      have h2 : Real.log (s / q) ≤ s / q - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h3 : s * Real.log (s / q) ≤ s * (s / q - 1) := mul_le_mul_of_nonneg_left h2 h0.le
      have h4 : s * (s / q - 1) = s ^ 2 / q - s := by field_simp
      rw [h1]; nlinarith
  -- the pointwise inequality, with `ψ_a(y) = a klFun(y/a) = y log(y/a) + a - y`
  have key : ∀ v c x : ℝ, 0 < v →
      (v + c ^ 2) * InformationTheory.klFun ((x + c) ^ 2 / (v + c ^ 2)) ≤
        2 * (v * InformationTheory.klFun (x ^ 2 / v)) + 8 * x ^ 2 := by
    intro v c x hv
    set a := v + c ^ 2 with ha
    have ha0 : 0 < a := by positivity
    have hψ : ∀ b y : ℝ, 0 < b → b * InformationTheory.klFun (y / b) =
        y * Real.log (y / b) + b - y := by
      intro b y hb; unfold InformationTheory.klFun; field_simp
    rw [hψ a _ ha0, hψ v _ hv]
    -- Step B: `ψ_a(x² + c²) ≤ ψ_v(x²)` (log-sum inequality)
    have hB : (x ^ 2 + c ^ 2) * Real.log ((x ^ 2 + c ^ 2) / a) ≤
        x ^ 2 * Real.log (x ^ 2 / v) := by
      set y := x ^ 2 with hy
      have hy0 : 0 ≤ y := sq_nonneg x
      set A := y + c ^ 2
      have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
      rcases (add_nonneg hy0 hc0).eq_or_lt with hA | hA
      · have hA' : A = 0 := hA.symm
        rw [hA']; simp only [zero_mul]
        have : y = 0 := by linarith
        rw [this]; simp
      · have hr : 0 < A / a := by positivity
        have e1 : y * Real.log (y / v) - y * Real.log (A / a) ≥ y - v * (A / a) := by
          rcases hy0.eq_or_lt with h0 | h0
          · rw [← h0]; simp; positivity
          · have hdiff : Real.log (y / v) - Real.log (A / a) = Real.log ((y / v) / (A / a)) :=
              (Real.log_div (by positivity) hr.ne').symm
            have h2 := Real.add_one_le_exp (Real.log ((v * (A / a)) / y))
            have h3 : Real.log ((y / v) / (A / a)) = -Real.log ((v * (A / a)) / y) := by
              rw [← Real.log_inv]; congr 1; field_simp
            have h4 : 1 - (v * (A / a)) / y ≤ Real.log ((y / v) / (A / a)) := by
              rw [h3]
              have := Real.log_le_sub_one_of_pos (show 0 < (v * (A / a)) / y by positivity)
              linarith
            have h5 : y * (1 - (v * (A / a)) / y) = y - v * (A / a) := by field_simp
            rw [ge_iff_le, ← h5, ← mul_sub, hdiff]
            exact mul_le_mul_of_nonneg_left h4 h0.le
        have e2 : -(c ^ 2 * Real.log (A / a)) ≥ c ^ 2 - c ^ 2 * (A / a) := by
          have := Real.log_le_sub_one_of_pos hr
          nlinarith
        have e3 : y - v * (A / a) + (c ^ 2 - c ^ 2 * (A / a)) = 0 := by
          rw [ha]; field_simp; ring
        have : A * Real.log (A / a) = y * Real.log (A / a) + c ^ 2 * Real.log (A / a) := by ring
        linarith
    -- Step A: `ψ_a((x+c)²) ≤ 2 ψ_a(x² + c²) + 8x²`
    set q := x ^ 2 + c ^ 2 with hq
    have hA : (x + c) ^ 2 * Real.log ((x + c) ^ 2 / a) + a - (x + c) ^ 2 ≤
        2 * (q * Real.log (q / a) + a - q) + 8 * x ^ 2 := by
      rcases (add_nonneg (sq_nonneg x) (sq_nonneg c)).eq_or_lt with hq0 | hq0
      · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg c]
        have hc : c = 0 := by nlinarith [sq_nonneg x, sq_nonneg c]
        subst hx hc; simp; linarith
      · rw [← hq] at hq0
        have hs := L1 ((x + c) ^ 2) q a (sq_nonneg _) hq0 ha0
        have ht := L1 ((x - c) ^ 2) q a (sq_nonneg _) hq0 ha0
        -- `ψ_a(t) ≥ 0`
        have hψt : 0 ≤ (x - c) ^ 2 * Real.log ((x - c) ^ 2 / a) + a - (x - c) ^ 2 := by
          rw [← hψ a _ ha0]
          exact mul_nonneg ha0.le (InformationTheory.klFun_nonneg (by positivity))
        have hsum : ((x + c) ^ 2) ^ 2 / q + ((x - c) ^ 2) ^ 2 / q =
            2 * q + 8 * c ^ 2 * x ^ 2 / q := by
          rw [hq] at hq0 ⊢; field_simp; ring
        have hfrac : 8 * c ^ 2 * x ^ 2 / q ≤ 8 * x ^ 2 := by
          rw [div_le_iff₀ hq0, hq]; nlinarith [sq_nonneg x, sq_nonneg c, sq_nonneg (x * x)]
        have hlin : (x + c) ^ 2 + (x - c) ^ 2 = 2 * q := by rw [hq]; ring
        nlinarith
    linarith
  set c := ∫ y, f y ∂P with hc
  have hf1 : Integrable f P := hf.integrable one_le_two
  have hf2 : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have hg2 : Integrable (fun x => (f x - c) ^ 2) P := (hf.sub (memLp_const c)).integrable_sq
  set v := ∫ x, (f x - c) ^ 2 ∂P with hv
  have hfv : ∫ x, f x ^ 2 ∂P = v + c ^ 2 := by
    have e : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - 2 * c * f x) + c ^ 2 := by
      funext x; ring
    have h' : ∫ x, (f x - c) ^ 2 ∂P = ∫ x, f x ^ 2 ∂P - 2 * c * c + c ^ 2 := by
      have i1 : Integrable (fun x => f x ^ 2 - 2 * c * f x) P := hf2.sub (hf1.const_mul _)
      have i2 : Integrable (fun x => 2 * c * f x) P := hf1.const_mul _
      rw [e, integral_add i1 (integrable_const _), integral_sub hf2 i2, integral_const_mul,
        integral_const, ← hc]
      simp
    rw [hv, h']; ring
  have hv0 : 0 ≤ v := integral_nonneg fun x => sq_nonneg _
  unfold ent
  simp only [hf2, hg2, ↓reduceIte]
  rw [hfv, ← hv]
  rcases hv0.eq_or_lt with hv0 | hv0
  · -- `f = c` a.e.: the left side vanishes
    have hz : (fun x => (f x - c) ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hg2).mp hv0.symm
    have : ∫⁻ x, ENNReal.ofReal ((v + c ^ 2) *
        InformationTheory.klFun (f x ^ 2 / (v + c ^ 2))) ∂P = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hz] with x hx
        simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hx
        rw [hx, ← hv0, zero_add]
        rcases eq_or_ne (c ^ 2) 0 with h | h
        · simp [h]
        · simp [div_self h, InformationTheory.klFun_one]
    rw [this]; exact zero_le
  · rw [var, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← hc]
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal
        (v * InformationTheory.klFun ((f x - c) ^ 2 / v))) P := by
      have := hf.aestronglyMeasurable.aemeasurable
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        (((InformationTheory.measurable_klFun.comp_aemeasurable
          (((this.sub_const c).pow_const 2).div_const v))).const_mul v)
    calc ∫⁻ x, ENNReal.ofReal ((v + c ^ 2) *
          InformationTheory.klFun (f x ^ 2 / (v + c ^ 2))) ∂P
        ≤ ∫⁻ x, (2 * ENNReal.ofReal (v * InformationTheory.klFun ((f x - c) ^ 2 / v)) +
            8 * ENNReal.ofReal ((f x - c) ^ 2)) ∂P := by
          apply lintegral_mono
          intro x
          have hk := key v c (f x - c) hv0
          simp only [sub_add_cancel] at hk
          have h1 : 0 ≤ v * InformationTheory.klFun ((f x - c) ^ 2 / v) :=
            mul_nonneg hv0.le (InformationTheory.klFun_nonneg (by positivity))
          calc ENNReal.ofReal ((v + c ^ 2) * InformationTheory.klFun (f x ^ 2 / (v + c ^ 2)))
              ≤ ENNReal.ofReal (2 * (v * InformationTheory.klFun ((f x - c) ^ 2 / v)) +
                  8 * (f x - c) ^ 2) := ENNReal.ofReal_le_ofReal hk
            _ = _ := by
              rw [ENNReal.ofReal_add (by linarith) (by positivity),
                ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num),
                ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 by norm_num)]
              norm_num
      _ = 2 * ∫⁻ x, ENNReal.ofReal (v * InformationTheory.klFun ((f x - c) ^ 2 / v)) ∂P +
            8 * ∫⁻ x, ENNReal.ofReal ((f x - c) ^ 2) ∂P := by
          rw [lintegral_add_left' (hmeas.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]

end SharpLSI
