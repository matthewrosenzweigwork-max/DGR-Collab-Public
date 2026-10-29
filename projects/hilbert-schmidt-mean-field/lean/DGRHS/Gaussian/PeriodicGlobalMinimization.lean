import DGRHS.Gaussian.PeriodicGreenExtended
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Full absolutely continuous law formulation of the source threshold.

The displayed source L2 pairing is extended to the actual signed Green
integral. Global minimality is expressed as entropy >= beta/2 times energy,
so simultaneous infinite entropy and energy do not require an infinity-minus-
infinity convention. The full universal probability-law quantifier is retained.
The Green negative part is finite by `periodicGreen_negativePart_integrable`.
Agreement with the proper centered source expression is proved for the literal
dimension-eleven trial in the successor file. -/
noncomputable section
open MeasureTheory InformationTheory Set
open scoped ENNReal
namespace DGRHS.Periodic
universe u
variable (ι : Type u) [Fintype ι] [Nonempty ι]

def periodicGlobalMinimizerTemperatures : Set ℝ :=
  {β | 0≤β ∧ β<2*(Fintype.card ι:ℝ) ∧
    ∀ μ : Measure (PeriodicTorus ι),IsProbabilityMeasure μ → μ ≪ periodicHaar ι →
      ((β/2:ℝ):EReal)*periodicGreenEnergyExtended μ≤(klDiv μ (periodicHaar ι)).toEReal}

def periodicGlobalMinimizationThreshold : ℝ := sSup (periodicGlobalMinimizerTemperatures ι)

lemma periodicGlobalMinimizerTemperatures_zero : 0∈periodicGlobalMinimizerTemperatures ι := by
  refine ⟨le_rfl,by positivity,?_⟩
  intro μ hμ hac
  simp only [zero_div,EReal.coe_zero,zero_mul]
  change (0:EReal)≤(klDiv μ (periodicHaar ι):EReal)
  exact EReal.coe_ennreal_nonneg _

lemma periodicGlobalMinimizerTemperatures_bddAbove :
    BddAbove (periodicGlobalMinimizerTemperatures ι) :=
  ⟨2*(Fintype.card ι:ℝ),fun _ h => h.2.1.le⟩

lemma periodicGlobalMinimizationThreshold_nonneg : 0≤periodicGlobalMinimizationThreshold ι :=
  le_csSup (periodicGlobalMinimizerTemperatures_bddAbove ι) (periodicGlobalMinimizerTemperatures_zero ι)

end DGRHS.Periodic
#check @DGRHS.Periodic.periodicGlobalMinimizerTemperatures
#check @DGRHS.Periodic.periodicGlobalMinimizationThreshold
#print axioms DGRHS.Periodic.periodicGlobalMinimizerTemperatures_zero
#print axioms DGRHS.Periodic.periodicGlobalMinimizationThreshold_nonneg
