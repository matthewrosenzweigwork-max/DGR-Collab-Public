import DGPS.Examples.EngineeredRankOneGauge
import DGPS.Examples.EngineeredRankOneSharpLSI

/-!
# Species-rate limit for the prescribed engineered potentials

The exact one-body potential is retained. The proved constant-potential gauge
identifies its canonical species rate with the actual ordinary reference rate.
Every real rate in the limit carries its pointwise finiteness receipt.
-/

open Filter Topology
open scoped ENNReal

namespace DGPS.Examples.EngineeredRankOne

open DGPS.Models

/-- The species rate of the exact fixed-coupling family tends to the circle rate,
through all fields at least two, with finiteness proved before taking real values. -/
theorem species_rate_limit :
    ∃ hm : ∀ h : Set.Ici (2 : ℝ),
        FiniteRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)),
      Tendsto (fun h : Set.Ici (2 : ℝ) =>
        realRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2))
          (hm h) / DGPS.a0) atTop (𝓝 1) := by
  have heq (h : Set.Ici (2 : ℝ)) :
      speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2) =
        ordinaryLSRate (engineeredModel h.1 h.2).ref :=
    (normalized_speciesRate h.1 h.2).symm.trans
      (DGPS.Examples.engineered_species_rate_equals_ordinary_lsi h.1 h.2 (normalizedDrift h.1 h.2)).1
  have hfinite (h : Set.Ici (2 : ℝ)) :
      FiniteRate (speciesRate (engineeredRankOne h.1 h.2) (engineeredRankOneDrift h.1 h.2)) := by
    rw [heq h]
    exact (DGPS.Examples.engineered_species_rate_equals_ordinary_lsi h.1 h.2
      (normalizedDrift h.1 h.2)).2.2.1.ne
  refine ⟨hfinite, ?_⟩
  simpa only [realRate, heq] using
    DGPS.Examples.engineered_sharp_one_site_limit_from_defect_removal

end DGPS.Examples.EngineeredRankOne
