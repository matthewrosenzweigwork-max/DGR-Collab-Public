import DGPS.Lipschitz.T01PositiveEquilibrium
import DGPS.Lipschitz.T01GlobalEntropyCoercivity
import DGPS.Lipschitz.T01ReferenceEntropy

/-!
# Positive-rate equilibrium and uniform particle-reference estimates

One actual minimizing probability supplies every conclusion below. Positive scalar rate
provides uniqueness and Hessian coercivity, which provide mean-field entropy coercivity;
conditional entropy then provides the particle normalizer and density moments. The arbitrary-law
reference entropy comparison follows from the same density moment and exponent.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Positive scalar rate under direct Lipschitz data supplies the genuine equilibrium,
mean-field entropy coercivity and all uniform particle-reference estimates at the same witness. -/
theorem t01_positive_rate_reference_data {d : ℕ} (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b) :
    ∃ μ : ProbabilityMeasure (Torus d),
      DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A ∧
      (∀ ν : ProbabilityMeasure (Torus d),
        DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A → ν = μ) ∧
      IsCoerciveDensityHessian A μ ∧
      (frozenGibbs A μ).measure = (μ : Measure (Torus d)) ∧
      ∃ c C p : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < C ∧ 1 < p ∧
        (∀ ρ : ProbabilityMeasure (Torus d),
          klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ →
          c * (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤
            (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
              t01CenteredCorrection A μ ρ) ∧
        ∀ N : ℕ+,
          |Real.log (centeredParticleNormalizer A μ N)| ≤ C ∧
          (∫ X, centeredParticleDensity A μ N X ^ p
            ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) ≤ C ∧
          ∀ (ν : Measure (ParticleSpace d N)) [IsProbabilityMeasure ν],
            klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤
              ENNReal.ofReal C * (klDiv ν (particleLaw A N) + 1) := by
  obtain ⟨μ, hμ, huniq, hH⟩ := t01_unique_minimizer_and_coercive_hessian A hLip b hrate
  have hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)) :=
    (DGPS.Structural.minimizer_eq_frozenGibbs A hμ).symm
  obtain ⟨c, hc0, hc1, hco⟩ := t01_entropy_correction_coercive_of_unique_hessian A hμ huniq hH
  have hco' : ∀ ρ : ProbabilityMeasure (Torus d),
      klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ →
      c * (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤
        (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
          (1 / 2 : ℝ) * ∫ p, DGPS.centeredKernel A μ p.1 p.2
            ∂((ρ : Measure (Torus d)).prod (ρ : Measure (Torus d))) := by
    intro ρ hρ
    simpa only [t01CenteredCorrection, DGPS.Structural.centeredKernel_eq_lipschitz] using hco ρ hρ
  obtain ⟨C, p, -, hp, hN⟩ :=
    t01_reference_density_moments_of_entropy_coercivity A μ hfix hc0 hc1 hco'
  let D := (p + Real.log (max C 1)) / (p - 1)
  have hD : 0 < D := div_pos
    (by linarith [Real.log_nonneg (le_max_right C 1)]) (by linarith)
  refine ⟨μ, hμ, huniq, hH, hfix, c, max C D, p, hc0, hc1,
    hD.trans_le (le_max_right _ _), hp, hco, fun N => ?_⟩
  refine ⟨(hN N).1.trans (le_max_left _ _), (hN N).2.trans (le_max_left _ _), fun ν _ => ?_⟩
  exact (t01_reference_entropy_of_density_moment A μ hfix N hp (hN N).2 ν).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right C D)) le_rfl)

end DGPS.Lipschitz
