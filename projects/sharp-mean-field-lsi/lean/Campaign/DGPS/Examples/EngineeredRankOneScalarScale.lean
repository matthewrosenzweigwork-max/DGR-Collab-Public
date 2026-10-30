import DGPS.Examples.EngineeredRankOneAsymptotics
import DGPS.Examples.EngineeredRankOneSineTrial
import DGPS.Foundations.RateArithmetic

/-!
# EX046 on the exact frozen engineered model

The constant-potential gauge is applied explicitly. Thus the rates here belong
to `Models.engineeredRankOne` with its internally constructed actual drift,
not merely to the normalized engine data.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Examples

open DGPS.Models DGPS.Examples.EngineeredRankOne

/-- The exact fixed-coupling scalar rate has uniform linear upper and lower
bounds. Constants are chosen before the field and the canonical rate retains
its full original absolute-density competitor class. -/
theorem engineered_scalar_linear_growth :
    ∃ c C h0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ h0 ∧ ∀ (h : ℝ) (hh : 2 ≤ h), h0 ≤ h →
      ENNReal.ofReal (c * a0 * h) ≤ scalarRate (engineeredRankOne h hh) (engineeredRankOneDrift h hh) ∧
      scalarRate (engineeredRankOne h hh) (engineeredRankOneDrift h hh) ≤ ENNReal.ofReal (C * a0 * h) := by
  obtain ⟨c, h0, hc, hh0, hlow⟩ := engineered_scalar_linear_lower_bound
  obtain ⟨C, hC, hupp⟩ := engineered_scalar_sine_upper_bound
  refine ⟨c, C, h0, hc, hC, hh0, fun h hh h0h => ?_⟩
  constructor
  · rw [← normalized_scalarRate h hh]
    exact hlow h hh h0h (normalizedDrift h hh)
  · rw [← normalized_scalarRate h hh]
    exact hupp h hh (normalizedDrift h hh)

/-- The exact scalar rate is finite for every field in the prescribed family. -/
theorem engineered_scalar_rate_finite (h : ℝ) (hh : 2 ≤ h) :
    FiniteRate (scalarRate (engineeredRankOne h hh) (engineeredRankOneDrift h hh)) := by
  obtain ⟨C, _, hupp⟩ := engineered_scalar_sine_upper_bound
  rw [← normalized_scalarRate h hh]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupp h hh (normalizedDrift h hh))

end DGPS.Examples
