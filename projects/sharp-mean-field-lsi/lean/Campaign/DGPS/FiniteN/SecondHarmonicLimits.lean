import DGPS.Lipschitz.SharpLimits
import DGPS.FiniteN.SecondHarmonicStrictLSI

/-!
# Exact second-harmonic limits and global nonmonotonicity

The existing exact nonlinear rates and strict finite-particle bounds are combined with
the canonical direct-Lipschitz sharp limits. Both sequences start at the limiting rate,
drop strictly at particle number two, and return to that rate at infinity. No assertion
about eventual monotonicity or later consecutive differences is made.
-/

open Filter Topology
open scoped ENNReal

namespace DGPS.FiniteN.SecondHarmonic

open DGPS.Circle.AngularNormalization

/-- Both nonlinear rates of the exact repulsive second harmonic equal the circle rate. -/
theorem nonlinear_rates (κ : ℝ) (hκ : 0 < κ) :
    let b := DGPS.lipschitz_absoluteDrift (secondHarmonicData κ) (lipschitzData_secondHarmonic κ)
    DGPS.scalarRate (secondHarmonicData κ) b = ENNReal.ofReal a0 ∧
      DGPS.speciesRate (secondHarmonicData κ) b = ENNReal.ofReal a0 := by
  let b := DGPS.lipschitz_absoluteDrift (secondHarmonicData κ) (lipschitzData_secondHarmonic κ)
  obtain ⟨-, -, -, hscalar, hspecies⟩ :=
    second_harmonic_first_mode_recovery_and_exact_nonlinear_rates κ hκ b
  exact ⟨by simpa only [a0] using hscalar, by simpa only [a0] using hspecies⟩

/-- At one particle the interaction vanishes and both rates are the circle rate. -/
theorem particle_one (κ : ℝ) (hκ : 0 < κ) :
    DGPS.particleRateAll (secondHarmonicData κ) 1 = ENNReal.ofReal a0 ∧
      DGPS.particleRateSym (secondHarmonicData κ) 1 = ENNReal.ofReal a0 :=
  (strict_particle_lsi_and_n_one_equality κ hκ).1

/-- Every particle number at least two has the required strict symmetric dip. -/
theorem strict_dip_every_N (κ : ℝ) (hκ : 0 < κ) :
    ∀ N : ℕ+, 2 ≤ N →
      DGPS.particleRateAll (secondHarmonicData κ) N ≤
        DGPS.particleRateSym (secondHarmonicData κ) N ∧
      DGPS.particleRateSym (secondHarmonicData κ) N < ENNReal.ofReal a0 :=
  (strict_particle_lsi_and_n_one_equality κ hκ).2

/-- Both particle sequences converge on the positive integers to the exact nonlinear rate. -/
theorem particle_limits (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (DGPS.particleRateAll (secondHarmonicData κ)) atTop (𝓝 (ENNReal.ofReal a0)) ∧
      Tendsto (DGPS.particleRateSym (secondHarmonicData κ)) atTop (𝓝 (ENNReal.ofReal a0)) := by
  obtain ⟨hscalar, hspecies⟩ := nonlinear_rates κ hκ
  have hall := DGPS.Lipschitz.sharp_limits_all 1 (by decide)
    (secondHarmonicData κ) (lipschitzData_secondHarmonic κ)
  have hsym := DGPS.Lipschitz.sharp_limits_sym 1 (by decide)
    (secondHarmonicData κ) (lipschitzData_secondHarmonic κ)
  exact ⟨by simpa only [hspecies] using hall, by simpa only [hscalar] using hsym⟩

private theorem not_monotone_not_antitone_of_drop
    (f : ℕ+ → ℝ≥0∞) (L : ℝ≥0∞) (h1 : f 1 = L) (h2 : f 2 < L)
    (hlim : Tendsto f atTop (𝓝 L)) : ¬ Monotone f ∧ ¬ Antitone f := by
  constructor
  · intro hmono
    have h12 : L ≤ f 2 := by simpa only [h1] using hmono (show (1 : ℕ+) ≤ 2 by decide)
    exact (not_le_of_gt h2) h12
  · intro hanti
    have hL : L ≤ f 2 := le_of_tendsto hlim
      ((eventually_ge_atTop (2 : ℕ+)).mono fun N hN => hanti hN)
    exact (not_le_of_gt h2) hL

/-- Both positive-integer sequences fail both global order-monotonicity directions. -/
theorem neither_monotone_nor_antitone (κ : ℝ) (hκ : 0 < κ) :
    ¬ Monotone (DGPS.particleRateAll (secondHarmonicData κ)) ∧
      ¬ Antitone (DGPS.particleRateAll (secondHarmonicData κ)) ∧
      ¬ Monotone (DGPS.particleRateSym (secondHarmonicData κ)) ∧
      ¬ Antitone (DGPS.particleRateSym (secondHarmonicData κ)) := by
  obtain ⟨honeAll, honeSym⟩ := particle_one κ hκ
  obtain ⟨hleTwo, hltTwo⟩ := strict_dip_every_N κ hκ 2 (by decide)
  obtain ⟨hlimAll, hlimSym⟩ := particle_limits κ hκ
  have hall := not_monotone_not_antitone_of_drop _ _ honeAll (hleTwo.trans_lt hltTwo) hlimAll
  have hsym := not_monotone_not_antitone_of_drop _ _ honeSym hltTwo hlimSym
  exact ⟨hall.1, hall.2, hsym.1, hsym.2⟩

/-- T14: all exact rates, every strict finite-particle dip, both limits and the four
global monotonicity failures for the single fixed second-harmonic interaction. -/
theorem exact_rates_and_nonmonotone (κ : ℝ) (hκ : 0 < κ) :
    let b := DGPS.lipschitz_absoluteDrift (secondHarmonicData κ) (lipschitzData_secondHarmonic κ)
    DGPS.scalarRate (secondHarmonicData κ) b = ENNReal.ofReal a0 ∧
      DGPS.speciesRate (secondHarmonicData κ) b = ENNReal.ofReal a0 ∧
      DGPS.particleRateAll (secondHarmonicData κ) 1 = ENNReal.ofReal a0 ∧
      DGPS.particleRateSym (secondHarmonicData κ) 1 = ENNReal.ofReal a0 ∧
      (∀ N : ℕ+, 2 ≤ N →
        DGPS.particleRateAll (secondHarmonicData κ) N ≤
          DGPS.particleRateSym (secondHarmonicData κ) N ∧
        DGPS.particleRateSym (secondHarmonicData κ) N < ENNReal.ofReal a0) ∧
      Tendsto (DGPS.particleRateAll (secondHarmonicData κ)) atTop (𝓝 (ENNReal.ofReal a0)) ∧
      Tendsto (DGPS.particleRateSym (secondHarmonicData κ)) atTop (𝓝 (ENNReal.ofReal a0)) ∧
      ¬ Monotone (DGPS.particleRateAll (secondHarmonicData κ)) ∧
      ¬ Antitone (DGPS.particleRateAll (secondHarmonicData κ)) ∧
      ¬ Monotone (DGPS.particleRateSym (secondHarmonicData κ)) ∧
      ¬ Antitone (DGPS.particleRateSym (secondHarmonicData κ)) := by
  obtain ⟨hscalar, hspecies⟩ := nonlinear_rates κ hκ
  obtain ⟨honeAll, honeSym⟩ := particle_one κ hκ
  obtain ⟨hlimAll, hlimSym⟩ := particle_limits κ hκ
  obtain ⟨hnmAll, hnaAll, hnmSym, hnaSym⟩ := neither_monotone_nor_antitone κ hκ
  exact ⟨hscalar, hspecies, honeAll, honeSym, strict_dip_every_N κ hκ,
    hlimAll, hlimSym, hnmAll, hnaAll, hnmSym, hnaSym⟩

end DGPS.FiniteN.SecondHarmonic
