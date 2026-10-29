import Mathlib

/-!
# Gibbs measures of continuous energies on compact spaces (Phase 1 infrastructure)

For a continuous `H` on a compact space with a probability measure `μ`, the partition function
`Z = ∫ e^{-H} dμ` is positive and finite, and `Z^{-1} e^{-H} μ` is a probability measure that is
mutually absolutely continuous with `μ`.
-/

open MeasureTheory

namespace SharpLSI

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {H : X → ℝ}

theorem integrable_exp_neg_of_continuous (hH : Continuous H) :
    Integrable (fun x => Real.exp (-H x)) μ :=
  (BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Real.exp (-H x), by fun_prop⟩).integrable μ

theorem partition_pos_of_continuous (hH : Continuous H) :
    0 < ∫ x, Real.exp (-H x) ∂μ :=
  integral_exp_pos (integrable_exp_neg_of_continuous μ hH)

/-- The normalized Gibbs density `Z^{-1} e^{-H}`. -/
noncomputable def gibbsDensity (H : X → ℝ) (x : X) : ENNReal :=
  ENNReal.ofReal (Real.exp (-H x) / ∫ y, Real.exp (-H y) ∂μ)

theorem gibbsDensity_pos (hH : Continuous H) (x : X) : 0 < gibbsDensity μ H x :=
  ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) (partition_pos_of_continuous μ hH))

omit [CompactSpace X] [IsProbabilityMeasure μ] in
theorem measurable_gibbsDensity (hH : Continuous H) : Measurable (gibbsDensity μ H) :=
  ENNReal.measurable_ofReal.comp ((by fun_prop : Continuous fun x =>
    Real.exp (-H x) / ∫ y, Real.exp (-H y) ∂μ).measurable)

theorem isProbabilityMeasure_withDensity_gibbs (hH : Continuous H) :
    IsProbabilityMeasure (μ.withDensity (gibbsDensity μ H)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hZ := partition_pos_of_continuous μ hH
  have hint : Integrable (fun x => Real.exp (-H x) / ∫ y, Real.exp (-H y) ∂μ) μ :=
    (integrable_exp_neg_of_continuous μ hH).div_const _
  unfold gibbsDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (div_pos (Real.exp_pos _) hZ).le),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]

omit [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure μ] in
theorem withDensity_gibbs_absolutelyContinuous :
    μ.withDensity (gibbsDensity μ H) ≪ μ :=
  withDensity_absolutelyContinuous _ _

theorem absolutelyContinuous_withDensity_gibbs (hH : Continuous H) :
    μ ≪ μ.withDensity (gibbsDensity μ H) :=
  withDensity_absolutelyContinuous' (measurable_gibbsDensity μ hH).aemeasurable
    (Filter.Eventually.of_forall fun x => (gibbsDensity_pos μ hH x).ne')

end SharpLSI
