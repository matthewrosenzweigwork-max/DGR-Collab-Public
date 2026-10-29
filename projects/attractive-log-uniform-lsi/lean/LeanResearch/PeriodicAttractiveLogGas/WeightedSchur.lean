import LeanResearch.Imported.TauCetiAppendix.MeasureTheory.Integral.SchurTest

/-! Weighted-column version of the Cauchy--Schwarz and Tonelli argument
in Appendix A. Adapted from the attributed local Tau Ceti Schur proof.
The weight remains on the final integral; it is not discarded or replaced
by an unweighted norm. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace PeriodicAttractiveLogGas.WeightedSchur
open ImportedTauCeti
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

theorem lintegral_rpow_lintegral_mul_le_weighted [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) {g : β → ℝ≥0∞} (hg : AEMeasurable g ν) {p : ℝ}
    (hp : 1 ≤ p) {w : β → ℝ≥0∞} (hw : AEMeasurable w ν) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂μ ≤ B * w y) :
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, w y * g y ^ p ∂ν := by
  have hkx : ∀ x, Measurable (k x) := fun x => hk.comp measurable_prodMk_left
  have hky : ∀ y, Measurable fun x => k x y := fun y => hk.comp measurable_prodMk_right
  -- Hölder's inequality for the measure `ν.withDensity (k x)`, for each fixed `x`.
  have hrow : ∀ x, (∫⁻ y, k x y * g y ∂ν) ^ p ≤
      (∫⁻ y, k x y ∂ν) ^ (p - 1) * ∫⁻ y, k x y * g y ^ p ∂ν := by
    intro x
    have h := rpow_lintegral_le_measure_univ_rpow_mul
      (hg.mono_ac (withDensity_absolutelyContinuous ν (k x))) hp
    rwa [lintegral_withDensity_eq_lintegral_mul₀ (hkx x).aemeasurable hg,
      lintegral_withDensity_eq_lintegral_mul₀ (hkx x).aemeasurable (hg.pow_const p),
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have hjoint : AEMeasurable (Function.uncurry fun x y => k x y * g y ^ p) (μ.prod ν) :=
    hk.aemeasurable.mul (hg.pow_const p).comp_snd
  calc
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ
        ≤ ∫⁻ x, A ^ (p - 1) * ∫⁻ y, k x y * g y ^ p ∂ν ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards [hA] with x hx
      exact (hrow x).trans (by gcongr)
    _ = A ^ (p - 1) * ∫⁻ y, ∫⁻ x, k x y * g y ^ p ∂μ ∂ν := by
      have hmeas : AEMeasurable (fun x => ∫⁻ y, k x y * g y ^ p ∂ν) μ :=
        hjoint.lintegral_prod_right'
      rw [lintegral_const_mul'' _ hmeas, lintegral_lintegral_swap hjoint]
    _ = A ^ (p - 1) * ∫⁻ y, (∫⁻ x, k x y ∂μ) * g y ^ p ∂ν := by
      simp_rw [lintegral_mul_const _ (hky _)]
    _ ≤ A ^ (p - 1) * ∫⁻ y, B * w y * g y ^ p ∂ν := by
      gcongr 1
      refine lintegral_mono_ae ?_
      filter_upwards [hB] with y hy
      gcongr
    _ = A ^ (p - 1) * B * ∫⁻ y, w y * g y ^ p ∂ν := by
      simp_rw [mul_assoc B]
      have hwg : AEMeasurable (fun y => w y * g y ^ p) ν := by
        convert! hw.mul (hg.pow_const p) using 1
      rw [lintegral_const_mul'' _ hwg, mul_assoc]


end PeriodicAttractiveLogGas.WeightedSchur
