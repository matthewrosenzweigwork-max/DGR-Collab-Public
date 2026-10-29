import DGPS.Structural.SmallRateCircleEquality

/-!
# T07: exact equality of nonlinear rates below the inclusive circle threshold

On the unit circle under direct Lipschitz standing hypotheses, let `M = osc V + osc W > 0`.
If `0 < r_* ≤ e^{-M} min {a₀/9, 1/(4M)}` (inclusive), then `r_ms = r_*`.

The selected target conclusion is the STR021 declaration
`DGPS.Structural.speciesRate_eq_scalarRate_of_small_circle_rate`; this module re-assembles it once
with the exact frozen T07 signature.
-/

namespace DGPS.Targets.T07

/-- **T07.** Exact frozen statement, assembled from STR021. -/
theorem speciesRate_eq_scalarRate_of_small_circle_rate (A : DGPS.InteractionData 1)
    (hLip : DGPS.LipschitzData A) (hM : 0 < DGPS.totalOscillation A)
    (hpos : 0 < DGPS.scalarRate A (DGPS.lipschitz_absoluteDrift A hLip))
    (hsmall : DGPS.scalarRate A (DGPS.lipschitz_absoluteDrift A hLip) ≤
      ENNReal.ofReal (Real.exp (-DGPS.totalOscillation A) *
        min (DGPS.a0 / 9) (1 / (4 * DGPS.totalOscillation A)))) :
    DGPS.speciesRate A (DGPS.lipschitz_absoluteDrift A hLip) =
      DGPS.scalarRate A (DGPS.lipschitz_absoluteDrift A hLip) :=
  DGPS.Structural.speciesRate_eq_scalarRate_of_small_circle_rate A hLip hM hpos hsmall

end DGPS.Targets.T07
