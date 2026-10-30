import DGPS.Structural.HarmonicRateComparison
import DGPS.Variational.BasicRateBounds

/-!
# Positive scalar rate implies positive species rate

The direct-Lipschitz harmonic-mean comparison and the finite positive frozen one-body rate
give this implication without equilibrium uniqueness or a Hessian assumption.
-/

open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The positivity implication required by T01, for any actual weak-drift provider. -/
theorem speciesRate_pos_of_scalarRate_pos (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (hr : 0 < scalarRate A b) :
    0 < speciesRate A b := by
  have hrf : scalarRate A b ≠ ⊤ := scalarRate_ne_top hd A hLip b
  obtain ⟨hl0, hlle, hltop⟩ := Structural.frozenLSRateInf_ge_lowerBound hd A
  have hrpos : 0 < (scalarRate A b).toReal := ENNReal.toReal_pos hr.ne' hrf
  have hlpos : 0 < (frozenLSRateInf A).toReal :=
    ENNReal.toReal_pos ((ENNReal.ofReal_pos.2 hl0).trans_le hlle).ne' hltop.ne
  have hmean : 0 < ENNReal.ofReal
      ((scalarRate A b).toReal * (frozenLSRateInf A).toReal /
        ((scalarRate A b).toReal + (frozenLSRateInf A).toReal)) :=
    ENNReal.ofReal_pos.2 (div_pos (mul_pos hrpos hlpos) (add_pos hrpos hlpos))
  exact hmean.trans_le
    (Structural.speciesRate_ge_harmonicMean_frozenLS hd A hLip b hr hrf).1

end DGPS.Lipschitz
