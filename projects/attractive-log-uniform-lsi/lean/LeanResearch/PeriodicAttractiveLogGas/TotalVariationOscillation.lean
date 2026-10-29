import LeanResearch.PeriodicAttractiveLogGas.NormalizedExponentialInterpolation
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! The bounded-observable total-variation inequality in source line 613.
The arbitrary probability laws are represented over their actual sum;
the Radon--Nikodym and half-L1 identifications are proved explicitly. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace PeriodicAttractiveLogGas.TotalVariationOscillation

open NormalizedExponentialInterpolation

variable {α : Type*} [MeasurableSpace α] {μ ν τ : Measure α}

theorem withDensity_real_rnDeriv [SigmaFinite μ] [SigmaFinite τ] (h : μ ≪ τ) :
    τ.withDensity (fun x ↦ ENNReal.ofReal ((μ.rnDeriv τ x).toReal)) = μ := by
  calc
    _ = τ.withDensity (μ.rnDeriv τ) := withDensity_congr_ae
      ((Measure.rnDeriv_lt_top μ τ).mono fun _ hx ↦ ENNReal.ofReal_toReal hx.ne)
    _ = μ := Measure.withDensity_rnDeriv_eq μ τ h

theorem integrable_real_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x ↦ (μ.rnDeriv τ x).toReal) τ := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := τ) (measure_ne_top μ univ))

theorem setTV_eq_halfL1_rnDeriv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    setTotalVariation μ ν = halfL1Distance (μ + ν)
      (fun x ↦ (μ.rnDeriv (μ + ν) x).toReal)
      (fun x ↦ (ν.rnDeriv (μ + ν) x).toReal) := by
  have hm : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hn : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hp : (∫ x, (μ.rnDeriv (μ + ν) x).toReal ∂(μ + ν)) = 1 := by
    simpa using Measure.integral_toReal_rnDeriv hm
  have hq : (∫ x, (ν.rnDeriv (μ + ν) x).toReal ∂(μ + ν)) = 1 := by
    simpa using Measure.integral_toReal_rnDeriv hn
  have h := setTotalVariation_withDensity_eq_halfL1
    (integrable_real_rnDeriv (μ := μ) (τ := μ + ν))
    (integrable_real_rnDeriv (μ := ν) (τ := μ + ν))
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg) hp hq
  simpa only [withDensity_real_rnDeriv hm, withDensity_real_rnDeriv hn] using h

theorem setTV_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ setTotalVariation μ ν := by
  rw [setTV_eq_halfL1_rnDeriv]
  exact mul_nonneg (by norm_num) (integral_nonneg fun x ↦ abs_nonneg _)

theorem setTV_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    setTotalVariation μ ν ≤ 1 := by
  apply csSup_le
  · exact ⟨_, ∅, MeasurableSet.empty, rfl⟩
  · rintro _ ⟨s, _, rfl⟩
    have hm : (μ s).toReal ≤ 1 := measureReal_le_one
    have hn : (ν s).toReal ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith [ENNReal.toReal_nonneg (a := μ s)],
      by linarith [ENNReal.toReal_nonneg (a := ν s)]⟩

/-- A bounded interval, rather than a chosen norm bound, gives the exact
oscillation factor. The reference measure need not be finite. -/
theorem abs_integral_difference_le_halfL1 {p q f : α → ℝ}
    (hp : Integrable p τ) (hq : Integrable q τ)
    (hp1 : (∫ x, p x ∂τ) = 1) (hq1 : (∫ x, q x ∂τ) = 1)
    (hf : AEStronglyMeasurable f τ) {a b : ℝ}
    (hfbound : ∀ x, f x ∈ Icc a b) :
    |(∫ x, p x * f x ∂τ) - (∫ x, q x * f x ∂τ)| ≤
      halfL1Distance τ p q * (b - a) := by
  have hfb : ∀ᵐ x ∂τ, ‖f x‖ ≤ |a| + |b| := Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hfbound x).1, neg_abs_le a, abs_nonneg b],
      by linarith [(hfbound x).2, le_abs_self b, abs_nonneg a]⟩
  have hip := hp.mul_bdd hf hfb
  have hiq := hq.mul_bdd hf hfb
  have hig : Integrable (fun x ↦ p x - q x) τ := hp.sub hq
  have hz : (∫ x, p x - q x ∂τ) = 0 := by
    rw [integral_sub hp hq, hp1, hq1, sub_self]
  let c := (a + b) / 2
  have hcenter : ∀ x, |f x - c| ≤ (b - a) / 2 := by
    intro x
    dsimp [c]
    exact abs_le.mpr ⟨by linarith [(hfbound x).1], by linarith [(hfbound x).2]⟩
  have he : (∫ x, (p x - q x) * (f x - c) ∂τ) =
      (∫ x, p x * f x ∂τ) - (∫ x, q x * f x ∂τ) := by
    have hid : Integrable (fun x ↦ (p x - q x) * f x) τ := hig.mul_bdd hf hfb
    simp_rw [mul_sub]
    rw [integral_sub hid (hig.mul_const c), integral_mul_const, hz, zero_mul, sub_zero]
    simp_rw [sub_mul]
    exact integral_sub hip hiq
  have h := norm_integral_le_of_norm_le (hig.abs.mul_const ((b - a) / 2))
    (Eventually.of_forall fun x ↦ show ‖(p x - q x) * (f x - c)‖ ≤
      |p x - q x| * ((b - a) / 2) from by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hcenter x) (abs_nonneg _))
  rw [Real.norm_eq_abs, he, integral_mul_const] at h
  unfold halfL1Distance
  nlinarith [h]

/-- Source probability TV convention, for any pair of probabilities on
the same measurable space and every measurable bounded real observable. -/
theorem abs_integral_sub_le_setTV_mul_range [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Measurable f) {a b : ℝ} (hfbound : ∀ x, f x ∈ Icc a b) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ setTotalVariation μ ν * (b - a) := by
  have hm : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hn : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hp : (∫ x, (μ.rnDeriv (μ + ν) x).toReal ∂(μ + ν)) = 1 := by
    simpa using Measure.integral_toReal_rnDeriv hm
  have hq : (∫ x, (ν.rnDeriv (μ + ν) x).toReal ∂(μ + ν)) = 1 := by
    simpa using Measure.integral_toReal_rnDeriv hn
  have h := abs_integral_difference_le_halfL1
    (integrable_real_rnDeriv (μ := μ) (τ := μ + ν))
    (integrable_real_rnDeriv (μ := ν) (τ := μ + ν)) hp hq hf.aestronglyMeasurable hfbound
  rw [integral_toReal_rnDeriv_mul hm, integral_toReal_rnDeriv_mul hn,
    ← setTV_eq_halfL1_rnDeriv] at h
  exact h

def oscillation (f : α → ℝ) : ℝ := sSup (range f) - sInf (range f)

theorem abs_integral_sub_le_setTV_mul_oscillation
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hf : Measurable f) (hup : BddAbove (range f)) (hlow : BddBelow (range f)) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ setTotalVariation μ ν * oscillation f := by
  apply abs_integral_sub_le_setTV_mul_range hf
  intro x
  exact ⟨csInf_le hlow (mem_range_self x), le_csSup hup (mem_range_self x)⟩

omit [MeasurableSpace α] in
theorem oscillation_le_of_pairwise [Nonempty α] {f : α → ℝ} {D : ℝ}
    (hD : ∀ x y, |f x - f y| ≤ D) : oscillation f ≤ D := by
  have hx (x : α) : f x - D ≤ sInf (range f) := by
    apply le_csInf (range_nonempty f)
    rintro _ ⟨y, rfl⟩
    have h := (abs_le.mp (hD x y)).2
    linarith
  have hs : sSup (range f) ≤ sInf (range f) + D := by
    apply csSup_le (range_nonempty f)
    rintro _ ⟨x, rfl⟩
    linarith [hx x]
  unfold oscillation
  linarith

theorem abs_integral_sub_le_setTV_mul_pairwise
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ} {D : ℝ}
    (hf : Measurable f) (hup : BddAbove (range f)) (hlow : BddBelow (range f))
    (hD : ∀ x y, |f x - f y| ≤ D) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ setTotalVariation μ ν * D := by
  let := nonempty_of_isProbabilityMeasure μ
  exact (abs_integral_sub_le_setTV_mul_oscillation hf hup hlow).trans
    (mul_le_mul_of_nonneg_left (oscillation_le_of_pairwise hD) setTV_nonneg)

end PeriodicAttractiveLogGas.TotalVariationOscillation
