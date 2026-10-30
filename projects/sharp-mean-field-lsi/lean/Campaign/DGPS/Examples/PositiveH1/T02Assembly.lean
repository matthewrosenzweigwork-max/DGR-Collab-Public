import DGPS.Examples.PositiveH1.T02SharpLimits

/-!
# The fixed positive H1 example: exact sharp limits

The actual full-domain eventual inequality for the single rough model gives the lower
limit. The established first-harmonic recovery gives both upper limits. Neither a
cutoff sequence depending on particle number nor a finite-particle endpoint inequality
is asserted.
-/

open Filter Topology
open scoped ENNReal

namespace DGPS.RegularityBoundary

open DGPS.Examples.PositiveH1.Model

private theorem positive_h1_all_liminf :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤
      liminf (fun N : ℕ+ => particleRateAll positiveH1 N) atTop := by
  apply (Filter.le_liminf_iff').2
  intro y hy
  by_cases hy0 : y = 0
  · subst y
    exact Eventually.of_forall fun N => bot_le
  have hyfin : y ≠ ⊤ := ne_top_of_lt hy
  have hyr : 0 < y.toReal := ENNReal.toReal_pos hy0 hyfin
  have hya : y.toReal < 4 * Real.pi ^ 2 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp
    simpa only [ENNReal.ofReal_toReal hyfin] using hy
  filter_upwards [DGPS.Examples.PositiveH1.positive_h1_eventual_exact_lsi hyr hya] with N hN
  have hLSI : ∀ f : ParticleH1 positiveH1 N,
      particleEntropy positiveH1 N f ≤ ENNReal.ofReal
        (2 * particleEnergy positiveH1 N f / y.toReal) := by
    intro f
    convert hN f using 1 <;> congr 1 <;> ring
  simpa only [ENNReal.ofReal_toReal hyfin] using (particleRate_iff_lsi positiveH1 N hyr).mp hLSI

private theorem positive_h1_both_limits :
    Tendsto (fun N : ℕ+ => particleRateAll positiveH1 N) atTop
      (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2))) ∧
    Tendsto (fun N : ℕ+ => particleRateSym positiveH1 N) atTop
      (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2))) := by
  have hall := positive_h1_all_liminf
  have hsym : ENNReal.ofReal (4 * Real.pi ^ 2) ≤
      liminf (fun N : ℕ+ => particleRateSym positiveH1 N) atTop :=
    hall.trans (liminf_le_liminf (Eventually.of_forall fun N => particleRateAll_le_sym positiveH1 N))
  obtain ⟨hupper, hsymUpper⟩ := DGPS.Examples.PositiveH1.Recovery.both_particle_upper_limits
  exact ⟨tendsto_of_le_liminf_of_limsup_le hall (hupper.trans hsymUpper),
    tendsto_of_le_liminf_of_limsup_le hsym hsymUpper⟩

/-- Every positive strict subrate has one threshold for every original rough particle H1 test. -/
theorem positive_h1_eventual_lsi (r : ℝ) (hr : 0 < r) (hra : r < DGPS.a0) :
    ∃ N0 : ℕ+, ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 positiveH1 N,
      particleEntropy positiveH1 N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy positiveH1 N f) := by
  exact Filter.eventually_atTop.1
    (DGPS.Examples.PositiveH1.positive_h1_eventual_exact_lsi hr hra)

/-- T02 for the one fixed infinite-series model: H1 but not W1,infinity, exact nonlinear
rates, both particle limits, and full-domain eventual LSIs at every strict positive subrate. -/
theorem positive_h1_sharp_limits :
    let A := positiveH1
    let b := DGPS.Examples.PositiveH1.Nonlinear.positiveH1Drift
    MemH1 (pairFun A.W) ∧
      ¬ DGPS.Examples.PositiveH1.Regularity.W1Infinity (pairFun A.W) ∧
      scalarRate A b = ENNReal.ofReal DGPS.a0 ∧
      speciesRate A b = ENNReal.ofReal DGPS.a0 ∧
      Tendsto (fun N : ℕ+ => particleRateAll A N) atTop (𝓝 (ENNReal.ofReal DGPS.a0)) ∧
      Tendsto (fun N : ℕ+ => particleRateSym A N) atTop (𝓝 (ENNReal.ofReal DGPS.a0)) ∧
      (∀ r : ℝ, 0 < r → r < DGPS.a0 → ∃ N0 : ℕ+,
        ∀ N : ℕ+, N0 ≤ N → ∀ f : ParticleH1 A N,
          particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f)) := by
  obtain ⟨-, hH1, hnot⟩ := DGPS.Examples.PositiveH1.Regularity.positive_example_excludes_w1_infinity
  obtain ⟨hscalar, hspecies⟩ :=
    DGPS.Examples.PositiveH1.Nonlinear.exact_nonlinear_rates_for_rough_and_every_fixed_smooth_cutoff.1
      DGPS.Examples.PositiveH1.Nonlinear.positiveH1Drift
  obtain ⟨hall, hsym⟩ := positive_h1_both_limits
  exact ⟨hH1, hnot, hscalar, hspecies, hall, hsym, positive_h1_eventual_lsi⟩

end DGPS.RegularityBoundary
