/- Global measurability of the actual finite source energy, needed for
probability competitors not absolutely continuous against the iid source.
No source-a.e. measurability is substituted for this global statement. -/
import DGRHS.CLT.SourceExponentCLT
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.CLT

theorem stronglyMeasurable_sourceCanonicalModulatedEnergy {S : Type*} [MeasurableSpace S]
    (h : S×S→ℝ) (F : S→ℝ) (I : ℝ) (hh : StronglyMeasurable h)
    (hF : StronglyMeasurable F) (N : ℕ) :
    StronglyMeasurable (sourceCanonicalModulatedEnergy h F I N) := by
  classical
  have hs : Measurable (fun x : Fin N→S=>
      ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag,h (x p.1,x p.2)) :=
    Finset.measurable_sum _ (fun p _=>hh.measurable.comp
      ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)))
  have hf : Measurable (fun x : Fin N→S=>∑ i : Fin N,F (x i)) :=
    Finset.measurable_sum _ (fun i _=>hF.measurable.comp (measurable_pi_apply i))
  unfold sourceCanonicalModulatedEnergy DGRHS.CanonicalVariance.normalizedOffDiagonalSum
    DGRHS.CanonicalVariance.offDiagonalSum
  exact (measurable_const.mul (((measurable_const.mul hs).div_const 2).sub
    (measurable_const.mul hf) |>.add measurable_const)).stronglyMeasurable

end DGRHS.CLT
#check @DGRHS.CLT.stronglyMeasurable_sourceCanonicalModulatedEnergy
#print axioms DGRHS.CLT.stronglyMeasurable_sourceCanonicalModulatedEnergy
