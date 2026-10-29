import Mathlib

/-!
# Pinsker's inequality for densities (Phase 3, lane C)

`(∫ |ρ - 1| dP)² ≤ 2 ∫ klFun(ρ) dP` for a probability density `ρ` (`pinsker_lintegral`), from the
pointwise bound `3(t-1)² ≤ (2t+4) klFun(t)` (`three_sq_le_klFun`) and `|x| ≤ sw/2 + x²/(2sw)`.
-/

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal

namespace SharpLSI

/-- `φ(t) = (t+1) log t - 2(t-1)`. -/
noncomputable def pinPhi (t : ℝ) : ℝ := (t + 1) * Real.log t - 2 * (t - 1)

theorem hasDerivAt_pinPhi {t : ℝ} (ht : 0 < t) :
    HasDerivAt pinPhi (Real.log t + (t + 1) * t⁻¹ - 2) t := by
  have := (((hasDerivAt_id t).add_const 1).mul (Real.hasDerivAt_log ht.ne')).sub
    (((hasDerivAt_id t).sub_const 1).const_mul 2)
  convert this using 1
  · funext s; simp [pinPhi]
  · simp

theorem deriv_pinPhi_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ deriv pinPhi t := by
  rw [(hasDerivAt_pinPhi ht).deriv]
  have h1 := Real.one_sub_inv_le_log_of_pos ht
  have : (t + 1) * t⁻¹ = 1 + t⁻¹ := by field_simp
  rw [this]; linarith

theorem continuousOn_pinPhi : ContinuousOn pinPhi (Ioi 0) := fun t ht =>
  (hasDerivAt_pinPhi ht).continuousAt.continuousWithinAt

theorem pos_of_mem_interior_Ici {s : ℝ} (hs : s ∈ interior (Ici (1 : ℝ))) : 0 < s := by
  rw [interior_Ici] at hs; exact lt_trans one_pos hs

theorem pos_of_mem_interior_Ioc {s : ℝ} (hs : s ∈ interior (Ioc (0 : ℝ) 1)) : 0 < s := by
  rw [interior_Ioc] at hs; exact hs.1

theorem pinPhi_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ pinPhi t := by
  have hm : MonotoneOn pinPhi (Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (continuousOn_pinPhi.mono fun s hs => mem_Ioi.mpr (lt_of_lt_of_le one_pos hs))
      (fun s hs => (hasDerivAt_pinPhi (pos_of_mem_interior_Ici hs)).differentiableAt
        |>.differentiableWithinAt)
      (fun s hs => deriv_pinPhi_nonneg (pos_of_mem_interior_Ici hs))
  have := hm (Set.mem_Ici.mpr le_rfl) ht ht
  simpa [pinPhi] using this

theorem pinPhi_nonpos {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1) : pinPhi t ≤ 0 := by
  have hm : MonotoneOn pinPhi (Ioc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
      (continuousOn_pinPhi.mono fun s hs => mem_Ioi.mpr hs.1)
      (fun s hs => (hasDerivAt_pinPhi (pos_of_mem_interior_Ioc hs)).differentiableAt
        |>.differentiableWithinAt)
      (fun s hs => deriv_pinPhi_nonneg (pos_of_mem_interior_Ioc hs))
  have := hm ⟨ht0, ht⟩ ⟨one_pos, le_rfl⟩ ht
  simpa [pinPhi] using this

/-- `f(t) = (2t+4) klFun(t) - 3(t-1)²`. -/
noncomputable def pinF (t : ℝ) : ℝ := (2 * t + 4) * klFun t - 3 * (t - 1) ^ 2

theorem hasDerivAt_pinF {t : ℝ} (ht : 0 < t) : HasDerivAt pinF (4 * pinPhi t) t := by
  have hk : HasDerivAt klFun (Real.log t) t := by
    have := ((Real.hasDerivAt_mul_log ht.ne').add_const 1).sub (hasDerivAt_id t)
    convert this using 1
    · funext s; simp [klFun_apply]
    · simp
  have := (((hasDerivAt_id t).const_mul 2).add_const 4).mul hk |>.sub
    (((hasDerivAt_id t).sub_const 1).pow 2 |>.const_mul 3)
  convert this using 1
  · funext s; simp [pinF]
  · simp only [pinPhi, klFun_apply, id]
    push_cast
    ring

theorem continuousOn_pinF : ContinuousOn pinF (Ioi 0) := fun t ht =>
  (hasDerivAt_pinF ht).continuousAt.continuousWithinAt

theorem pinF_one : pinF 1 = 0 := by simp [pinF, klFun_apply]

theorem pinF_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ pinF t := by
  rcases ht.eq_or_lt with h0 | h0
  · subst h0; simp [pinF, klFun_apply]; norm_num
  rcases le_total t 1 with h1 | h1
  · have ha : AntitoneOn pinF (Ioc 0 1) :=
      antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
        (continuousOn_pinF.mono fun s hs => mem_Ioi.mpr hs.1)
        (fun s hs => (hasDerivAt_pinF (pos_of_mem_interior_Ioc hs)).differentiableAt
          |>.differentiableWithinAt)
        (fun s hs => by
          have hs' := hs
          rw [interior_Ioc] at hs'
          rw [(hasDerivAt_pinF hs'.1).deriv]
          linarith [pinPhi_nonpos hs'.1 hs'.2.le])
    have := ha ⟨h0, h1⟩ ⟨one_pos, le_rfl⟩ h1
    rw [pinF_one] at this; exact this
  · have hm : MonotoneOn pinF (Ici 1) :=
      monotoneOn_of_deriv_nonneg (convex_Ici 1)
        (continuousOn_pinF.mono fun s hs => mem_Ioi.mpr (lt_of_lt_of_le one_pos hs))
        (fun s hs => (hasDerivAt_pinF (pos_of_mem_interior_Ici hs)).differentiableAt
          |>.differentiableWithinAt)
        (fun s hs => by
          have hs' := hs
          rw [interior_Ici] at hs'
          rw [(hasDerivAt_pinF (pos_of_mem_interior_Ici hs)).deriv]
          linarith [pinPhi_nonneg hs'.le])
    have := hm (Set.mem_Ici.mpr le_rfl) h1 h1
    rw [pinF_one] at this; exact this

/-- `3(t-1)² ≤ (2t+4) klFun(t)` for `t ≥ 0`. -/
theorem three_sq_le_klFun {t : ℝ} (ht : 0 ≤ t) : 3 * (t - 1) ^ 2 ≤ (2 * t + 4) * klFun t := by
  have := pinF_nonneg ht
  unfold pinF at this; linarith

/-- `|t - 1| ≤ s(t+2)/3 + klFun(t)/(2s)` for `t ≥ 0`, `s > 0`. -/
theorem abs_sub_one_le {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    |t - 1| ≤ s * (t + 2) / 3 + klFun t / (2 * s) := by
  have hk := three_sq_le_klFun ht
  set w := (2 * t + 4) / 3 with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  have h1 : (t - 1) ^ 2 ≤ w * klFun t := by rw [hw]; nlinarith
  have h2 : |t - 1| ≤ s * w / 2 + (t - 1) ^ 2 / (2 * s * w) := by
    rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|t - 1| - s * w), sq_abs (t - 1), abs_nonneg (t - 1)]
  have h3 : (t - 1) ^ 2 / (2 * s * w) ≤ klFun t / (2 * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h4 : s * w / 2 = s * (t + 2) / 3 := by rw [hw]; ring
  linarith

/-- **Pinsker's inequality** for a probability density. -/
theorem pinsker_lintegral {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {ρ : α → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hint : Integrable ρ P) (h1 : ∫ x, ρ x ∂P = 1) :
    (∫⁻ x, ‖ρ x - 1‖ₑ ∂P) ^ 2 ≤ 2 * ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂P := by
  set K := ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂P with hK
  by_cases hKt : K = ⊤
  · rw [hKt]; simp
  -- `L ≤ s + K/(2s)` for every `s > 0`
  have hs : ∀ s : ℝ, 0 < s → ∫⁻ x, ‖ρ x - 1‖ₑ ∂P ≤ ENNReal.ofReal s + ENNReal.ofReal (1 / (2 * s)) * K := by
    intro s hs0
    have hi2 : Integrable (fun x => s * (ρ x + 2) / 3) P :=
      ((hint.add (integrable_const 2)).const_mul s).div_const 3
    calc ∫⁻ x, ‖ρ x - 1‖ₑ ∂P ≤ ∫⁻ x, (ENNReal.ofReal (s * (ρ x + 2) / 3) +
          ENNReal.ofReal (1 / (2 * s)) * ENNReal.ofReal (klFun (ρ x))) ∂P := by
          refine lintegral_mono fun x => ?_
          have hx := hρ0 x
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity)
              (klFun_nonneg hx))]
          refine ENNReal.ofReal_le_ofReal ((abs_sub_one_le (hρ0 x) hs0).trans (le_of_eq ?_))
          ring
      _ = ENNReal.ofReal s + ENNReal.ofReal (1 / (2 * s)) * K := by
          rw [lintegral_add_left' (f := fun x => ENNReal.ofReal (s * (ρ x + 2) / 3))
              (ENNReal.measurable_ofReal.comp_aemeasurable
              hi2.aestronglyMeasurable.aemeasurable), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← ofReal_integral_eq_lintegral_ofReal hi2
              (Eventually.of_forall fun x => by have := hρ0 x; positivity)]
          congr 1
          rw [integral_div, integral_const_mul, integral_add hint (integrable_const 2), h1]
          simp; ring_nf
  set L := ∫⁻ x, ‖ρ x - 1‖ₑ ∂P with hL
  set k := K.toReal with hk
  have hKk : K = ENNReal.ofReal k := (ENNReal.ofReal_toReal hKt).symm
  have hLt : L ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKt⟩) (hs 1 one_pos)
  set l := L.toReal with hl
  have hLl : L = ENNReal.ofReal l := (ENNReal.ofReal_toReal hLt).symm
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hl0 : 0 ≤ l := ENNReal.toReal_nonneg
  have hreal : ∀ s : ℝ, 0 < s → l ≤ s + k / (2 * s) := by
    intro s hs0
    have h := hs s hs0
    rw [hLl, hKk, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hs0.le
      (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    linarith [show 1 / (2 * s) * k = k / (2 * s) by ring]
  have hsq : l ^ 2 ≤ 2 * k := by
    rcases hl0.eq_or_lt with h0 | h0
    · rw [← h0]; nlinarith
    · have h := hreal (l / 2) (by positivity)
      have : k / (2 * (l / 2)) = k / l := by ring
      rw [this, ← sub_le_iff_le_add', le_div_iff₀ h0] at h
      nlinarith
  rw [hLl, hKk, ← ENNReal.ofReal_pow hl0, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul
    (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hsq

end SharpLSI
