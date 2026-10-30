import DGPS.Lipschitz.T01UnrestrictedLowerLimit
import DGPS.Lipschitz.T01SymmetricLowerLimit
import DGPS.Lipschitz.T01SharpAssembly
import DGPS.Lipschitz.T01Positivity
import DGPS.FiniteN.Tools.PositiveRate

/-!
# Sharp particle limits under direct Lipschitz hypotheses

T01 on the original particle Sobolev domains. The canonical drift is constructed from the
Lipschitz data. The actual lower limits are combined with full-domain product recovery;
neither a lower limit nor a comparison estimate is an input to the public theorem.
-/

open Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

/-- T01: both sharp limits, all finite-rate clauses, positivity, the zero case, and exact
eventual inequalities with one threshold before every particle number and Sobolev test. -/
theorem sharp_limits (d : ℕ) (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) :
    let b := DGPS.lipschitz_absoluteDrift A hLip
    FiniteRate (scalarRate A b) ∧
      FiniteRate (speciesRate A b) ∧
      (∀ N : ℕ+, FiniteRate (particleRateAll A N) ∧ FiniteRate (particleRateSym A N)) ∧
      Tendsto (fun N : ℕ+ => particleRateAll A N) atTop (𝓝 (speciesRate A b)) ∧
      Tendsto (fun N : ℕ+ => particleRateSym A N) atTop (𝓝 (scalarRate A b)) ∧
      (0 < scalarRate A b → 0 < speciesRate A b) ∧
      (∀ r : ℝ, 0 < r → ENNReal.ofReal r < speciesRate A b →
        ∃ N0 : ℕ+, ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 A N,
          particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f)) ∧
      (∀ r : ℝ, 0 < r → ENNReal.ofReal r < scalarRate A b →
        ∃ N0 : ℕ+, ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 A N,
          IsSymmetricParticleTest f →
            particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f)) ∧
      (scalarRate A b = 0 → speciesRate A b = 0 ∧
        Tendsto (fun N : ℕ+ => particleRateAll A N) atTop (𝓝 0) ∧
        Tendsto (fun N : ℕ+ => particleRateSym A N) atTop (𝓝 0)) := by
  let b := DGPS.lipschitz_absoluteDrift A hLip
  have hfin := rate_finiteness_single_species_inclusion_and_zero_case hd A hLip b
  have hall := t01_unrestricted_species_liminf_lower_all_rates A hLip hd b
  have hsym := t01_symmetric_scalar_liminf_lower_all_rates A hLip hd b
  have hlim := particle_limits_of_lower_bounds A hLip b hall hsym
  refine ⟨hfin.2.1, hfin.2.2.1, ?_, hlim.1, hlim.2, ?_, ?_, ?_, ?_⟩
  · intro N
    have hN := DGPS.FiniteN.rates_pos_lt_top A N hd
    exact ⟨hN.1.2.ne, hN.2.1.2.ne⟩
  · exact speciesRate_pos_of_scalarRate_pos hd A hLip b
  · intro r hr hR
    exact eventual_lsi_all_of_liminf A (speciesRate A b) hall r hr hR
  · intro r hr hR
    exact eventual_lsi_sym_of_liminf A (scalarRate A b) hsym r hr hR
  · intro h0
    obtain ⟨hms, hall0, hsym0, -, -⟩ := hfin.2.2.2.2.2 h0
    exact ⟨hms, hall0, hsym0⟩

/-- The unrestricted sharp limit on the full canonical particle domain. -/
theorem sharp_limits_all (d : ℕ) (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) :
    Tendsto (fun N : ℕ+ => particleRateAll A N) atTop
      (𝓝 (speciesRate A (DGPS.lipschitz_absoluteDrift A hLip))) := by
  exact (sharp_limits d hd A hLip).2.2.2.1

/-- The symmetric sharp limit on the original a.e. permutation-invariant domain. -/
theorem sharp_limits_sym (d : ℕ) (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) :
    Tendsto (fun N : ℕ+ => particleRateSym A N) atTop
      (𝓝 (scalarRate A (DGPS.lipschitz_absoluteDrift A hLip))) := by
  exact (sharp_limits d hd A hLip).2.2.2.2.1

/-- Positivity of the scalar rate implies positivity of the full finite-species rate. -/
theorem positive_scalar_implies_positive_species (d : ℕ) (hd : 0 < d)
    (A : InteractionData d) (hLip : LipschitzData A)
    (hrate : 0 < scalarRate A (DGPS.lipschitz_absoluteDrift A hLip)) :
    0 < speciesRate A (DGPS.lipschitz_absoluteDrift A hLip) := by
  exact (sharp_limits d hd A hLip).2.2.2.2.2.1 hrate

/-- Every positive species subrate is eventually an exact unrestricted particle LSI rate. -/
theorem eventual_lsi_all (d : ℕ) (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (r : ℝ) (hr : 0 < r)
    (hR : ENNReal.ofReal r < speciesRate A (DGPS.lipschitz_absoluteDrift A hLip)) :
    ∃ N0 : ℕ+, ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) := by
  exact (sharp_limits d hd A hLip).2.2.2.2.2.2.1 r hr hR

/-- Every positive scalar subrate is eventually an exact symmetric particle LSI rate. -/
theorem eventual_lsi_sym (d : ℕ) (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (r : ℝ) (hr : 0 < r)
    (hR : ENNReal.ofReal r < scalarRate A (DGPS.lipschitz_absoluteDrift A hLip)) :
    ∃ N0 : ℕ+, ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 A N,
      IsSymmetricParticleTest f →
        particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) := by
  exact (sharp_limits d hd A hLip).2.2.2.2.2.2.2.1 r hr hR

/-- The zero scalar-rate branch includes both sharp zero limits. -/
theorem zero_scalar_rates_and_limits (d : ℕ) (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A)
    (h0 : scalarRate A (DGPS.lipschitz_absoluteDrift A hLip) = 0) :
    speciesRate A (DGPS.lipschitz_absoluteDrift A hLip) = 0 ∧
      Tendsto (fun N : ℕ+ => particleRateAll A N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ+ => particleRateSym A N) atTop (𝓝 0) := by
  exact (sharp_limits d hd A hLip).2.2.2.2.2.2.2.2 h0

end DGPS.Lipschitz
