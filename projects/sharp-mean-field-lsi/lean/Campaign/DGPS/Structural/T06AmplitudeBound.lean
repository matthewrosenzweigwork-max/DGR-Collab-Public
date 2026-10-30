import DGPS.Structural.T06ScalarSmoothBound
import DGPS.Structural.T06SineBounds
import DGPS.Structural.T06DensityBounds
import DGPS.Lipschitz.T01PositiveEquilibrium

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGPS.Structural
variable {d : ℕ}

/-- The amplitude-only upper bound for the actual scalar nonlinear rate.
Positive scalar rate supplies the coercive equilibrium; neither uniqueness nor
coercivity is a new hypothesis. -/
theorem scalarRate_le_amplitude_bound (d : ℕ) (hd : 0 < d)
    (A : InteractionData d) (hLip : LipschitzData A)
    (hpos : 0 < scalarRate A (lipschitz_absoluteDrift A hLip)) :
    scalarRate A (lipschitz_absoluteDrift A hLip) ≤
      ENNReal.ofReal (a0 * (1 + DGPS.interactionOscillation A / 2) * Real.exp (totalOscillation A)) := by
  let b := lipschitz_absoluteDrift A hLip
  obtain ⟨μ, hμ, -, hH⟩ := DGPS.Lipschitz.t01_unique_minimizer_and_coercive_hessian A hLip b hpos
  obtain ⟨c, C, hc, hlo, hup, hratio⟩ := frozenGibbs_sharp_density_bounds A hLip μ
  let P := frozenGibbs A μ
  have hprob : (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus d)) = μ :=
    ProbabilityMeasure.toMeasure_injective (minimizer_eq_frozenGibbs A hμ).symm
  let p : Fin d := ⟨0, hd⟩
  have hv := t06_sine_rayleigh_le_density_ratio P p hc
    (Filter.Eventually.of_forall hlo) (Filter.Eventually.of_forall hup) hratio
  change 0 < weightedVariance (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus d)) (sineTest p) ∧ _ at hv
  rw [hprob] at hv
  have hmeasure : P.measure = (μ : Measure (Torus d)) := (minimizer_eq_frozenGibbs A hμ).symm
  rw [hmeasure] at hv
  have hs := t06_scalarRate_le_smooth_rayleigh A hLip b μ (minimizer_le A hμ) hH
    (sineTest p) (isSmoothPeriodic_sineTest p) hv.1
  refine hs.trans (ENNReal.ofReal_le_ofReal ?_)
  have hΛ : 0 ≤ 1 + DGPS.interactionOscillation A / 2 := by
    have := DGPS.interactionOscillation_nonneg A
    positivity
  calc (1 + DGPS.interactionOscillation A / 2) *
        (∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂(μ : Measure (Torus d))) /
          weightedVariance μ (sineTest p)
      = (1 + DGPS.interactionOscillation A / 2) *
        ((∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂(μ : Measure (Torus d))) /
          weightedVariance μ (sineTest p)) := by ring
    _ ≤ (1 + DGPS.interactionOscillation A / 2) * (a0 * Real.exp (totalOscillation A)) :=
      mul_le_mul_of_nonneg_left hv.2 hΛ
    _ = _ := by ring

end DGPS.Structural
