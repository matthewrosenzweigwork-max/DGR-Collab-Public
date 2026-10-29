import DGRHS.Gaussian.PeriodicD1EntropyEnergy

/-! UNCOMPILED CANDIDATE (Claude complete physical d1 return, 2026-10-03).
The actual campaign global-minimization temperature set of the uniform phase in
dimension one is exactly `[0, 2)`, and its supremum, the source `β_gm(1)`
(eq:betaGmDef, line 2995; asserted at line 3087), equals 2.

The upper bound `β_gm(1) ≤ 2` is the definitional range `β < 2·d`; it does not
use the collision divergence. The lower bound uses the all-law comparison
`periodicD1_entropy_energy_extended`, which carries the full universal
quantifier over probability laws. -/
noncomputable section
open MeasureTheory InformationTheory Set
namespace DGRHS.Periodic

theorem periodicD1_globalMinimizerTemperatures :
    periodicGlobalMinimizerTemperatures (Fin 1) = Ico 0 2 := by
  ext β
  simp only [periodicGlobalMinimizerTemperatures, mem_setOf_eq, mem_Ico,
    Fintype.card_fin, Nat.cast_one, mul_one]
  constructor
  · rintro ⟨h0, h2, -⟩
    exact ⟨h0, h2⟩
  · rintro ⟨h0, h2⟩
    refine ⟨h0, h2, fun μ hμ _ => ?_⟩
    haveI := hμ
    exact periodicD1_entropy_energy_extended β h0 h2 μ

/-- **Source β_gm(1) = 2.** -/
theorem periodicD1_globalMinimizationThreshold :
    periodicGlobalMinimizationThreshold (Fin 1) = 2 := by
  unfold periodicGlobalMinimizationThreshold
  rw [periodicD1_globalMinimizerTemperatures]
  exact csSup_Ico (by norm_num)

/-- Every subcritical temperature belongs to the set (membership form). -/
theorem periodicD1_mem_globalMinimizerTemperatures {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 2) :
    β ∈ periodicGlobalMinimizerTemperatures (Fin 1) := by
  rw [periodicD1_globalMinimizerTemperatures]
  exact ⟨hβ0, hβ⟩

end DGRHS.Periodic
