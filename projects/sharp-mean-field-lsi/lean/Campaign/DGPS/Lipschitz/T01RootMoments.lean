import DGPS.Lipschitz.T01SymmetricLower

/-!
# Higher moments of the actual ground-state transform

A bounded particle observable inherits its reference higher moment from the actual centered
Gibbs density moment, with the exact power and constant. No symmetry is required.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

/-- The canonical ground-state root preserves the density moment uniformly over bounded tests. -/
theorem centeredParticleRoot_higher_moment {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) {p B C : ℝ} (hp : 1 < p)
    (hB0 : 0 ≤ B) (f : ParticleSpace d N → ℝ) (hB : ∀ x, |f x| ≤ B)
    (hC : ∫ x, centeredParticleDensity A μ N x ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C) :
    ∫⁻ x, ENNReal.ofReal (|centeredParticleRoot A μ N f x| ^ (2 * p))
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
        ENNReal.ofReal (B ^ (2 * p) * C) := by
  have hp0 : 0 ≤ p := by linarith
  have hq (x : ParticleSpace d N) : 0 ≤ centeredParticleDensity A μ N x :=
    (centeredParticleDensity_pos A μ N x).le
  have hi : Integrable (fun x => centeredParticleDensity A μ N x ^ p)
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) :=
    ((Real.continuous_rpow_const hp0).comp (centeredParticleDensity_continuous A μ N)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpoint (x : ParticleSpace d N) :
      |centeredParticleRoot A μ N f x| ^ (2 * p) ≤
        B ^ (2 * p) * centeredParticleDensity A μ N x ^ p := by
    unfold centeredParticleRoot
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.mul_rpow (abs_nonneg _) (Real.sqrt_nonneg _),
      Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (hq x)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg _) (hB x) (by linarith)) (Real.rpow_nonneg (hq x) _)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (B ^ (2 * p)) *
        ENNReal.ofReal (centeredParticleDensity A μ N x ^ p)
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
      refine lintegral_mono fun x => ?_
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hB0 _)]
      exact ENNReal.ofReal_le_ofReal (hpoint x)
    _ = ENNReal.ofReal (B ^ (2 * p)) * ENNReal.ofReal
        (∫ x, centeredParticleDensity A μ N x ^ p
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal hi
          (Eventually.of_forall fun x => Real.rpow_nonneg (hq x) _)]
    _ ≤ _ := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hB0 _)]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hC)

end DGPS.Lipschitz
