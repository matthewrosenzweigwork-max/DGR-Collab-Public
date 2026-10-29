import FullLabeledLSI.Paper.Sec3Entropy
import SharpSymmetricLSI.Infra.Pinsker

/-!
# Entropy relative to a general reference density, and the compensation inequality

`klDiv (ρ m) (q m) = ∫ q klFun(ρ/q) dm` for densities with `ρ = 0` where `q = 0`, and
`∑ₐ θₐ H(ρₐ|ρ̄) ≤ ∑ₐ θₐ H(ρₐ|q)` for a reference density `q > 0`.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

theorem klDiv_ratio_eq {ρ q : Torus d → ℝ} (hρm : AEMeasurable ρ (haar d))
    (hqm : AEMeasurable q (haar d)) (hρ0 : ∀ x, 0 ≤ ρ x) (hq0 : ∀ x, 0 ≤ q x)
    (hz : ∀ x, q x = 0 → ρ x = 0) (hρ1 : ∫ x, ρ x ∂haar d = 1) (hq1 : ∫ x, q x ∂haar d = 1) :
    klDiv (densMeasure ρ) (densMeasure q) =
      ∫⁻ x, ENNReal.ofReal (q x * klFun (ρ x / q x)) ∂haar d := by
  have hb : AEMeasurable (fun x => ENNReal.ofReal (q x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hqm
  have hr : AEMeasurable (fun x => ENNReal.ofReal (ρ x / q x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hρm.div hqm)
  have hrat : densMeasure ρ = (densMeasure q).withDensity
      (fun x => ENNReal.ofReal (ρ x / q x)) := by
    unfold densMeasure
    rw [← withDensity_mul₀ hb hr]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    by_cases h : q x = 0
    · rw [hz x h, h]; simp
    · rw [← ENNReal.ofReal_mul (hq0 x)]
      congr 1
      field_simp
  have hac : densMeasure ρ ≪ densMeasure q := by
    rw [hrat]; exact withDensity_absolutelyContinuous _ _
  have : IsProbabilityMeasure (densMeasure q) := isProbabilityMeasure_densMeasure' hq0 hq1
  have : IsProbabilityMeasure (densMeasure ρ) := isProbabilityMeasure_densMeasure' hρ0 hρ1
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hrn : (densMeasure ρ).rnDeriv (densMeasure q) =ᵐ[densMeasure q]
      fun x => ENNReal.ofReal (ρ x / q x) := by
    rw [hrat]
    exact Measure.rnDeriv_withDensity₀ _ (hr.mono_ac (withDensity_absolutelyContinuous _ _))
  have h1 : ∫⁻ x, ENNReal.ofReal (klFun ((densMeasure ρ).rnDeriv (densMeasure q) x).toReal)
      ∂(densMeasure q) = ∫⁻ x, ENNReal.ofReal (klFun (ρ x / q x)) ∂(densMeasure q) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (div_nonneg (hρ0 x) (hq0 x))]
  rw [h1]
  have hg : AEMeasurable (fun x => ENNReal.ofReal (klFun (ρ x / q x))) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (measurable_klFun.comp_aemeasurable (hρm.div hqm))
  unfold densMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ hb hg]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hq0 x)]


section Comp

variable (F : Family d)

theorem klFun_compensation_pt (hF : F.Admissible) {q : ℝ} (hq : 0 < q) (x : Torus d) :
    ∑ a, F.θ a * (F.bar x * klFun (F.ρ a x / F.bar x)) ≤
      ∑ a, F.θ a * (q * klFun (F.ρ a x / q)) := by
  have hρ0 := fun a => (hF.2.2 a).1 x
  have hd := klFun_decomp F.θ (fun a => F.ρ a x / q) hF.1 hF.2.1 (fun a => div_nonneg (hρ0 a) hq.le)
  have hbar : (∑ b, F.θ b * (F.ρ b x / q)) = F.bar x / q := by
    simp only [Family.bar]; rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hbar] at hd
  have hnn : 0 ≤ klFun (F.bar x / q) := klFun_nonneg (div_nonneg (bar_nonneg F hF x) hq.le)
  have e : ∀ a, F.θ a * (q * klFun (F.ρ a x / q)) = q * (F.θ a * klFun (F.ρ a x / q)) :=
    fun a => by ring
  have e2 : ∀ a, F.θ a * (F.bar x * klFun (F.ρ a x / F.bar x)) =
      q * (F.θ a * ((F.bar x / q) * klFun ((F.ρ a x / q) / (F.bar x / q)))) := fun a => by
    rw [div_div_div_cancel_right₀ hq.ne']
    field_simp
  simp_rw [e, e2, ← Finset.mul_sum]
  rw [hd, mul_add]
  have : 0 ≤ q * klFun (F.bar x / q) := mul_nonneg hq.le hnn
  linarith

theorem entropy_compensation (hF : F.Admissible) {q : Torus d → ℝ} (hqm : AEMeasurable q (haar d))
    (hq0 : ∀ x, 0 < q x) (hq1 : ∫ x, q x ∂haar d = 1) :
    ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) ≤
      ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure q) := by
  have hρ0 := fun a => (hF.2.2 a).1
  have hρ1 := fun a => (hF.2.2 a).2.1
  simp_rw [klDiv_species F hF, klDiv_ratio_eq (rho_aemeasurable F hF _) hqm (hρ0 _)
    (fun x => (hq0 x).le) (fun x h => absurd h (hq0 x).ne') (hρ1 _) hq1]
  have hm1 : ∀ a, AEMeasurable (fun x => ENNReal.ofReal (F.bar x * klFun (F.ρ a x / F.bar x)))
      (haar d) := fun a =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((bar_aemeasurable F hF).mul
        (measurable_klFun.comp_aemeasurable ((rho_aemeasurable F hF a).div (bar_aemeasurable F hF))))
  have hm2 : ∀ a, AEMeasurable (fun x => ENNReal.ofReal (q x * klFun (F.ρ a x / q x))) (haar d) :=
    fun a => ENNReal.measurable_ofReal.comp_aemeasurable
      (hqm.mul (measurable_klFun.comp_aemeasurable ((rho_aemeasurable F hF a).div hqm)))
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_finsetSum' _ fun a _ => (hm1 a).const_mul _,
    ← lintegral_finsetSum' _ fun a _ => (hm2 a).const_mul _]
  refine lintegral_mono fun x => ?_
  have hθ0 : ∀ a, 0 ≤ F.θ a := fun a => (hF.1 a).le
  have hk1 : ∀ a, 0 ≤ F.bar x * klFun (F.ρ a x / F.bar x) := fun a =>
    mul_nonneg (bar_nonneg F hF x) (klFun_nonneg (div_nonneg ((hρ0 a) x) (bar_nonneg F hF x)))
  have hk2 : ∀ a, 0 ≤ q x * klFun (F.ρ a x / q x) := fun a =>
    mul_nonneg (hq0 x).le (klFun_nonneg (div_nonneg ((hρ0 a) x) (hq0 x).le))
  have e1 : ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (F.bar x * klFun (F.ρ a x / F.bar x)) =
      ENNReal.ofReal (∑ a, F.θ a * (F.bar x * klFun (F.ρ a x / F.bar x))) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a) (hk1 a)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_mul (hθ0 a)).symm
  have e2 : ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (q x * klFun (F.ρ a x / q x)) =
      ENNReal.ofReal (∑ a, F.θ a * (q x * klFun (F.ρ a x / q x))) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a) (hk2 a)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_mul (hθ0 a)).symm
  simp only [Pi.mul_apply]
  rw [e1, e2]
  exact ENNReal.ofReal_le_ofReal (klFun_compensation_pt F hF (hq0 x) x)

end Comp


/-- **L¹ Pinsker** for densities: `(∫ |ρ - q|)² ≤ 2 H(ρ|q)`, in `ℝ≥0∞`. -/
theorem l1_sq_le_two_klDiv {ρ q : Torus d → ℝ} (hρm : AEMeasurable ρ (haar d))
    (hqm : Measurable q) (hρ0 : ∀ x, 0 ≤ ρ x) (hq0 : ∀ x, 0 < q x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) (hq1 : ∫ x, q x ∂haar d = 1) :
    (∫⁻ x, ‖ρ x - q x‖ₑ ∂haar d) ^ 2 ≤ 2 * klDiv (densMeasure ρ) (densMeasure q) := by
  have hqm' : AEMeasurable q (haar d) := hqm.aemeasurable
  have hP : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  have hρi : Integrable ρ (haar d) := integrable_of_integral_eq_one' hρ1
  have hb : Measurable fun x => ENNReal.ofReal (q x) := hqm.ennreal_ofReal
  set r : Torus d → ℝ := fun x => ρ x / q x with hr
  have hr0 : ∀ x, 0 ≤ r x := fun x => div_nonneg (hρ0 x) (hq0 x).le
  have hint : Integrable r (densMeasure q) := by
    unfold densMeasure
    rw [integrable_withDensity_iff_integrable_smul' hb (Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_lt_top)]
    refine hρi.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hq0 x).le, hr]
    field_simp [(hq0 x).ne']
  have h1 : ∫ x, r x ∂densMeasure q = 1 := by
    rw [integral_densMeasure' (fun x => (hq0 x).le) hq1]
    simp_rw [hr, mul_div_cancel₀ _ (hq0 _).ne']; exact hρ1
  have hp := pinsker_lintegral hr0 hint h1
  have hL : ∫⁻ x, ‖r x - 1‖ₑ ∂densMeasure q = ∫⁻ x, ‖ρ x - q x‖ₑ ∂haar d := by
    have hm : AEMeasurable (fun x => ‖r x - 1‖ₑ) (haar d) :=
      ((hρm.div hqm').sub aemeasurable_const).enorm
    unfold densMeasure
    rw [lintegral_withDensity_eq_lintegral_mul₀ hb.aemeasurable hm]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply, hr]
    rw [← Real.enorm_of_nonneg (hq0 x).le]
    rw [← enorm_mul]
    congr 1
    field_simp [(hq0 x).ne']
  have hK : ∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂densMeasure q = klDiv (densMeasure ρ) (densMeasure q) := by
    rw [klDiv_ratio_eq hρm hqm' hρ0 (fun x => (hq0 x).le) (fun x h => absurd h (hq0 x).ne') hρ1 hq1]
    unfold densMeasure
    have hg : AEMeasurable (fun x => ENNReal.ofReal (klFun (r x))) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (measurable_klFun.comp_aemeasurable (hρm.div hqm'))
    rw [lintegral_withDensity_eq_lintegral_mul₀ hb.aemeasurable hg]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hq0 x).le]
  rw [hL, hK] at hp
  exact hp

end SharpLSI.FL
