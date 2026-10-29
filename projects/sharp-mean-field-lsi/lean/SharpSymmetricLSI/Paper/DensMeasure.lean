import SharpSymmetricLSI.Paper.PartitionLower
import SharpSymmetricLSI.Defs.D06_Dissipation

/-!
# Densities on `𝕋^d` (Phase 3, lane D)

General-`d` versions of the `densMeasure` lemmas of `Paper/CosineMeanField.lean`.
-/

open MeasureTheory InformationTheory Set Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem integrable_of_integral_eq_one' {ρ : Torus d → ℝ} (hρ1 : ∫ x, ρ x ∂haar d = 1) :
    Integrable ρ (haar d) := by
  by_contra h
  rw [integral_undef h] at hρ1
  exact zero_ne_one hρ1

theorem isProbabilityMeasure_densMeasure' {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) : IsProbabilityMeasure (densMeasure ρ) := by
  refine ⟨?_⟩
  rw [densMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one' hρ1)
      (Eventually.of_forall hρ0), hρ1, ENNReal.ofReal_one]

theorem integral_densMeasure' {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) (F : Torus d → ℝ) :
    ∫ x, F x ∂densMeasure ρ = ∫ x, ρ x * F x ∂haar d := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_of_integral_eq_one' hρ1).aestronglyMeasurable.aemeasurable
  rw [densMeasure, integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul]

theorem klDiv_densMeasure' {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) :
    klDiv (densMeasure ρ) (haar d) = ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂haar d := by
  have := isProbabilityMeasure_densMeasure' hρ0 hρ1
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_of_integral_eq_one' hρ1).aestronglyMeasurable.aemeasurable
  rw [klDiv_eq_lintegral_klFun_of_ac (μ := densMeasure ρ) (ν := haar d)
    (withDensity_absolutelyContinuous _ _)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity₀ (haar d) hm] with x hx
  rw [densMeasure, hx, ENNReal.toReal_ofReal (hρ0 x)]

/-- For a bounded density: `H(ρ|m) = ∫ klFun ρ dm`, finite. -/
theorem klDiv_densMeasure_bdd {ρ : Torus d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) {B : ℝ} (hB : ∀ x, ρ x ≤ B) :
    klDiv (densMeasure ρ) (haar d) ≠ ⊤ ∧
      (klDiv (densMeasure ρ) (haar d)).toReal = ∫ x, klFun (ρ x) ∂haar d := by
  have hi : Integrable (fun x => klFun (ρ x)) (haar d) := by
    refine Integrable.of_bound (measurable_klFun.comp hρm).aestronglyMeasurable (B ^ 2 + 1)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hρ0 x))]
    have h1 : klFun (ρ x) ≤ (ρ x - 1) ^ 2 := by
      rw [klFun_apply]
      rcases (hρ0 x).eq_or_lt with h | h
      · rw [← h]; simp
      · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) (hρ0 x)
        nlinarith
    have h2 := hρ0 x
    have h3 := hB x
    nlinarith
  rw [klDiv_densMeasure' hρ0 hρ1, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => klFun_nonneg (hρ0 x))]
  exact ⟨ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (integral_nonneg fun x => klFun_nonneg (hρ0 x))⟩

end SharpLSI
