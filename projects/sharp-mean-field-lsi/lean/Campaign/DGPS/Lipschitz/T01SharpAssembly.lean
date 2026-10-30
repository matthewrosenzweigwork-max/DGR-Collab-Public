import DGPS.Particle.ProductRecoveryLimits
import DGPS.Particle.RateEquivalences

/-!
# Consequences of particle lower limits

These helpers perform only the order-theoretic assembly.  The positive-rate lower limits
remain explicit inputs; this module does not establish the direct-Lipschitz T01 theorem.
-/

open Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- A particle-rate lower limit gives one threshold valid for every unrestricted Sobolev test.
The threshold is chosen after the subcritical rate and before the particle number and test. -/
theorem eventual_lsi_all_of_liminf (A : InteractionData d) (R : ℝ≥0∞)
    (hlim : R ≤ liminf (fun N : ℕ+ => particleRateAll A N) atTop)
    (r : ℝ) (hr : 0 < r) (hrR : ENNReal.ofReal r < R) :
    ∃ N0 : ℕ+, ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (eventually_lt_of_lt_liminf (hrR.trans_le hlim))
  refine ⟨N0, fun N hN f => ?_⟩
  simpa only [div_mul_eq_mul_div] using
    (particleRate_iff_lsi A N hr).2 (hN0 N hN).le f

/-- Symmetric counterpart, on the original particle Sobolev domain. -/
theorem eventual_lsi_sym_of_liminf (A : InteractionData d) (R : ℝ≥0∞)
    (hlim : R ≤ liminf (fun N : ℕ+ => particleRateSym A N) atTop)
    (r : ℝ) (hr : 0 < r) (hrR : ENNReal.ofReal r < R) :
    ∃ N0 : ℕ+, ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 A N,
      IsSymmetricParticleTest f →
        particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (eventually_lt_of_lt_liminf (hrR.trans_le hlim))
  refine ⟨N0, fun N hN f hs => ?_⟩
  simpa only [div_mul_eq_mul_div] using
    (particleRateSym_iff_lsi A N hr).2 (hN0 N hN).le f hs

/-- Combine actual lower-limit proofs with the established product-recovery upper limits.
No lower-limit proof is supplied by this order-theoretic helper. -/
theorem particle_limits_of_lower_bounds (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A)
    (hall : speciesRate A b ≤ liminf (fun N : ℕ+ => particleRateAll A N) atTop)
    (hsym : scalarRate A b ≤ liminf (fun N : ℕ+ => particleRateSym A N) atTop) :
    Tendsto (fun N : ℕ+ => particleRateAll A N) atTop (𝓝 (speciesRate A b)) ∧
      Tendsto (fun N : ℕ+ => particleRateSym A N) atTop (𝓝 (scalarRate A b)) := by
  obtain ⟨-, hall_upper, hsym_upper⟩ :=
    full_domain_product_recovery_and_particle_upper_limits A hLip b
  exact ⟨tendsto_of_le_liminf_of_limsup_le hall hall_upper,
    tendsto_of_le_liminf_of_limsup_le hsym hsym_upper⟩

end DGPS.Lipschitz
