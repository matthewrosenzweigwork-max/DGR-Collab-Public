import DGPS.Structural.MinimizerHessian

/-!
# Positive-rate stationary points are free-energy minimizers

This bridge uses the absolute-domain quotient defining `scalarRate`. It neither assumes nor
asserts uniqueness of the minimizer or strict coercivity of its density Hessian.
-/

open MeasureTheory
open scoped NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Vanishing of the finite scalar gap is precisely the free-energy minimum identity. -/
theorem scalarGap_eq_zero_iff_minimizer (A : InteractionData d) (ρ : AbsoluteDensity d) :
    scalarGap A ρ = 0 ↔ freeEnergy A (densityMeasure ρ) = freeEnergyMinimum A := by
  constructor
  · intro hgap
    have hreal : densityFreeEnergy A ρ = freeEnergyMinimumReal A := by
      have hz := congrArg (fun x : ℝ≥0 => (x : ℝ)) hgap
      simpa only [coe_scalarGap, NNReal.coe_zero, sub_eq_zero] using hz
    rw [← coe_densityFreeEnergy, ← coe_freeEnergyMinimumReal, hreal]
  · intro hmin
    apply NNReal.eq
    change densityFreeEnergy A ρ - freeEnergyMinimumReal A = 0
    apply sub_eq_zero.mpr
    apply EReal.coe_injective
    simpa only [coe_densityFreeEnergy, coe_freeEnergyMinimumReal] using hmin

/-- A positive scalar rate rules out a zero-dissipation competitor of positive gap. -/
theorem scalarGap_eq_zero_of_positive_scalarRate (A : InteractionData d)
    (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b) (ρ : AbsoluteDensity d)
    (hzero : scalarDissipation A b ρ = 0) : scalarGap A ρ = 0 := by
  by_contra hgap
  have hpos : 0 < scalarGap A ρ := pos_iff_ne_zero.mpr hgap
  have hle := scalarRate_le_quotient A b ρ hpos
  have hquot : scalarQuotient A b ρ = 0 := by simp [scalarQuotient, hzero]
  rw [hquot] at hle
  exact (not_le_of_gt hrate) hle

/-- Under positive scalar rate, every zero-dissipation absolute competitor is minimizing,
and every minimizing absolute competitor has zero dissipation. -/
theorem zeroDissipation_iff_minimizer_of_positive_scalarRate (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b)
    (ρ : AbsoluteDensity d) :
    scalarDissipation A b ρ = 0 ↔
      freeEnergy A (densityMeasure ρ) = freeEnergyMinimum A := by
  constructor
  · intro hzero
    exact (scalarGap_eq_zero_iff_minimizer A ρ).mp
      (scalarGap_eq_zero_of_positive_scalarRate A b hrate ρ hzero)
  · intro hmin
    exact ((DGPS.Structural.gibbsMinimizer_exists A hLip b).2.2
      (densityMeasure ρ) hmin).2.2.2 ρ rfl

/-- For positive scalar rate, the frozen Gibbs fixed points are exactly the free-energy
minimizers, including when the starting probability is not supplied as an absolute density. -/
theorem frozenFixedPoint_iff_minimizer_of_positive_scalarRate (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b)
    (μ : ProbabilityMeasure (Torus d)) :
    (μ : Measure (Torus d)) = (frozenGibbs A μ).measure ↔
      freeEnergy A μ = freeEnergyMinimum A := by
  constructor
  · intro hfix
    obtain ⟨-, ρ, hρ, hzero⟩ :=
      (DGPS.Structural.zeroDissipation_iff_frozenFixedPoint A hLip b).2 μ hfix
    rw [← hρ]
    exact (zeroDissipation_iff_minimizer_of_positive_scalarRate A hLip b hrate ρ).mp hzero
  · exact DGPS.Structural.minimizer_eq_frozenGibbs A

end DGPS.Lipschitz
