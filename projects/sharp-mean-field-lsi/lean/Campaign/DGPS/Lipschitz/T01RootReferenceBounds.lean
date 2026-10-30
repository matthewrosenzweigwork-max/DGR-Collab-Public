import DGPS.Lipschitz.T01RootForceBound
import DGPS.Lipschitz.T01RootMoments
import DGPS.Lipschitz.T01ParticleReferenceBridge

/-!
# Uniform full-domain reference bounds for the actual ground-state roots

A genuine uniform centered density moment gives the same higher moment for bounded particle
observables and bounds the force contribution to their reference energy. The legacy reference
Sobolev domain and energy are identified explicitly by the particle-coordinate bridge.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

/-- The full ground-state root family has the precise bounds needed by reference comparison. -/
theorem centeredParticleRoot_uniform_reference_bounds {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ+, ∫ x, centeredParticleDensity A μ N x ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (B E0 : ℝ), 0 ≤ B → 0 ≤ E0 →
      ∀ (N : ℕ+) (f : ParticleH1 A N), (∀ x, |f x| ≤ B) → particleEnergy A N f ≤ E0 →
        SharpLSI.MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))
          (centeredParticleRoot A μ N f) ∧
        SharpLSI.FL.refEnergy (μ : Measure (Torus d)) (centeredParticleRoot A μ N f) ≤
          ENNReal.ofReal (2 * E0 + B ^ 2 * M / 2) ∧
        ∫⁻ x, ENNReal.ofReal (|centeredParticleRoot A μ N f x| ^ (2 * p))
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
            ENNReal.ofReal (B ^ (2 * p) * C) := by
  obtain ⟨gU, M, hM0, hU, hM⟩ :=
    exists_centeredParticleForce_uniform_bound A hA hd μ hμ hp hC0 hC
  refine ⟨M, hM0, fun B E0 hB0 hE0 N f hB hE => ?_⟩
  obtain ⟨gB, hgB, hgBtop⟩ := centeredParticlePotential_has_bounded_weakGradient A hA μ N
  have hgUtop : MemLp (gU N) ∞ (particleHaar d N) :=
    hgBtop.ae_eq (hgB.ae_eq (hU N))
  have hroot := centeredParticleRootGradient_isWeakGradient A μ N f (hU N) hgUtop
  obtain ⟨hmem, -, henergy⟩ := legacy_particle_reference_form (frozenGibbs A μ) hroot
  rw [hμ] at hmem henergy
  refine ⟨hmem, ?_, centeredParticleRoot_higher_moment A μ N hp hB0 f hB (hC N)⟩
  rw [henergy]
  have hS0 : ∀ x, 0 ≤ particleTangentNormSq (gU N x) :=
    fun x => particleTangentNormSq_nonneg' _
  have hSint : Integrable (fun x => particleTangentNormSq (gU N x)) (particleLaw A N) :=
    integrable_particleTangentNormSq
      ((DGPS.Particle.memLp_particleLaw_iff A N).2
        (hgUtop.mono_exponent (by simp)))
  have hforce : (∫⁻ x, ENNReal.ofReal (f x ^ 2 * particleTangentNormSq (gU N x))
      ∂particleLaw A N) ≤ ENNReal.ofReal (B ^ 2 * M) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (particleTangentNormSq (gU N x))
          ∂particleLaw A N := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg B)]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right
            (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2) (hS0 x))
      _ = ENNReal.ofReal (B ^ 2) * ENNReal.ofReal
          (∫ x, particleTangentNormSq (gU N x) ∂particleLaw A N) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← ofReal_integral_eq_lintegral_ofReal hSint (Eventually.of_forall hS0)]
      _ ≤ _ := by
        rw [ENNReal.ofReal_mul (sq_nonneg B)]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hM N))
  refine (centeredParticleRoot_reference_energy_bound A μ hμ N f (gU N)).trans ?_
  calc
    _ ≤ 2 * ENNReal.ofReal E0 + ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (B ^ 2 * M) := by
      exact add_le_add (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hE))
        (mul_le_mul' le_rfl hforce)
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end DGPS.Lipschitz
