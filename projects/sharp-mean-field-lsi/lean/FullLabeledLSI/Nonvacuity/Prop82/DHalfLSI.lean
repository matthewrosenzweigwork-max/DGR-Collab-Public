import SharpSymmetricLSI.Paper.TorusLSI

/-!
# Lane D: the doubled-frequency circle LSI on the unit interval

For a smooth positive density `σ` of period `1/2`, the sharp circle log-Sobolev inequality
(`SharpLSI.lsi_interval`, constant `2/aCos` for period-1 functions) improves by a factor `4`.
-/

open MeasureTheory intervalIntegral InformationTheory
open scoped ContDiff

namespace SharpLSI.FL.Prop82

lemma half_comp_integral {G : ℝ → ℝ} (hG : Continuous G) (hper : ∀ t, G (t + 1 / 2) = G t) :
    ∫ t in (0 : ℝ)..1, G (t / 2) = ∫ t in (0 : ℝ)..1, G t := by
  have h1 : ∫ t in (0 : ℝ)..1, G (t / 2) = 2 * ∫ t in (0 : ℝ)..(1 / 2), G t := by
    rw [intervalIntegral.integral_comp_div (fun x => G x) (two_ne_zero)]
    simp
  have h2 : ∫ t in (1 / 2 : ℝ)..1, G t = ∫ t in (0 : ℝ)..(1 / 2), G t := by
    have := intervalIntegral.integral_comp_add_right (fun x => G x) (a := 0) (b := 1 / 2) (1 / 2 : ℝ)
    simp only [hper] at this
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, zero_add] at this
    exact this.symm
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable 0 (1 / 2)) (hG.intervalIntegrable (1 / 2) 1), h2]
  ring

theorem halfperiod_lsi {σ : ℝ → ℝ} (hs : ContDiff ℝ ∞ σ) (hpos : ∀ t, 0 < σ t)
    (hper : ∀ t, σ (t + 1 / 2) = σ t) (hmass : ∫ t in (0 : ℝ)..1, σ t = 1) :
    8 * SharpLSI.aCos * ∫ t in (0 : ℝ)..1, klFun (σ t) ≤
      ∫ t in (0 : ℝ)..1, deriv σ t ^ 2 / σ t := by
  have hc : Continuous σ := hs.continuous
  have hdc : Continuous (deriv σ) := hs.continuous_deriv (by simp)
  have hdper : ∀ t, deriv σ (t + 1 / 2) = deriv σ t := by
    intro t
    have : (fun x => σ (x + 1 / 2)) = σ := funext hper
    have h := deriv_comp_add_const (f := σ) (x := t) (a := 1 / 2)
    rw [← h, this]
  set ψ : ℝ → ℝ := fun t => Real.sqrt (σ (t / 2)) with hψ
  have hσ2 : ContDiff ℝ ∞ (fun t : ℝ => σ (t / 2)) :=
    hs.comp (contDiff_id.div_const 2)
  have hψs : ContDiff ℝ ∞ ψ := hσ2.sqrt (fun t => (hpos _).ne')
  have hψpos : ∀ t, 0 < ψ t := fun t => Real.sqrt_pos.2 (hpos _)
  have hψper : ∀ t, ψ (t + 1) = ψ t := by
    intro t
    simp only [hψ]
    congr 1
    rw [show (t + 1) / 2 = t / 2 + 1 / 2 by ring, hper]
  have hψ2 : ∀ t, ψ t ^ 2 = σ (t / 2) := fun t => Real.sq_sqrt (hpos _).le
  have hderiv : ∀ t, deriv ψ t ^ 2 = deriv σ (t / 2) ^ 2 / σ (t / 2) / 16 := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => σ (t / 2)) (deriv σ (t / 2) / 2) t := by
      have h := ((hs.differentiable (by simp)) (t / 2)).hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
      have := h.comp t h2
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using this
    have h3 := h1.sqrt (hpos _).ne'
    have : deriv ψ t = deriv σ (t / 2) / 2 / (2 * Real.sqrt (σ (t / 2))) := h3.deriv
    rw [this, div_pow, mul_pow, Real.sq_sqrt (hpos _).le, div_pow]
    field_simp
    ring
  have key := SharpLSI.lsi_interval hψs hψper hψpos
  have hcont1 : Continuous fun t => ψ t ^ 2 := (hψs.continuous).pow 2
  simp only [hψ2] at key
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one] at key
  simp only [hderiv] at key
  have hσc : Continuous fun t => σ (t / 2) := hc.comp (continuous_id.div_const 2)
  have hA : Continuous fun t => σ t * Real.log (σ t) :=
    hc.mul (Continuous.log hc (fun t => (hpos t).ne'))
  have hB : Continuous fun t => deriv σ t ^ 2 / σ t :=
    (hdc.pow 2).div hc (fun t => (hpos t).ne')
  have hD : ∫ x in (0 : ℝ)..1, deriv σ (x / 2) ^ 2 / σ (x / 2) / 16 =
      (∫ t in (0 : ℝ)..1, deriv σ t ^ 2 / σ t) / 16 := by
    rw [intervalIntegral.integral_div,
      half_comp_integral (G := fun t => deriv σ t ^ 2 / σ t) hB
        (fun t => by simp only [hper, hdper])]
  rw [half_comp_integral (G := fun t => σ t * Real.log (σ t)) hA
      (fun t => by simp only [hper]),
    half_comp_integral (G := σ) hc hper, hmass, hD] at key
  have hK : ∫ t in (0 : ℝ)..1, klFun (σ t) = ∫ t in (0 : ℝ)..1, σ t * Real.log (σ t) := by
    have e : ∀ t, klFun (σ t) = σ t * Real.log (σ t) - σ t + 1 := fun t => by rw [klFun_apply]; ring
    simp only [e]
    have i1 : IntervalIntegrable (fun t => σ t * Real.log (σ t) - σ t) MeasureTheory.volume 0 1 :=
      (hA.sub hc).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    rw [intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_sub (hA.intervalIntegrable 0 1) (hc.intervalIntegrable 0 1), hmass]
    simp
  rw [hK]
  have ha0 : 0 < SharpLSI.aCos := by unfold SharpLSI.aCos; positivity
  simp only [Real.log_one, mul_zero, sub_zero] at key
  set I := ∫ t in (0 : ℝ)..1, σ t * Real.log (σ t)
  set J := ∫ t in (0 : ℝ)..1, deriv σ t ^ 2 / σ t
  have : I * SharpLSI.aCos ≤ 2 / 16 * J := by
    have := mul_le_mul_of_nonneg_right key ha0.le
    rw [show 2 / SharpLSI.aCos * (J / 16) * SharpLSI.aCos = 2 / 16 * J by field_simp] at this
    exact this
  nlinarith

end SharpLSI.FL.Prop82
