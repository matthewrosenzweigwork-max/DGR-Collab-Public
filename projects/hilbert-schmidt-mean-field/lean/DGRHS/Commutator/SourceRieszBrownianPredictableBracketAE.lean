import DGRHS.Commutator.SourceRieszBrownianPredictableBracket
import DGRHS.Commutator.SourceRieszBrownianCompensatedSquareAE

/-! A predictable version of the actual scalar energy, and the corresponding
native compensated-square martingale. Its common all-time equality with the
literal energy and its almost-sure continuity and monotonicity are proved.
No bracket-identification or compensator assumption is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
variable (hBc : ∀ᵐ ω ∂P,Continuous (fun r=>B r ω))

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_predictable_compensator_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (fun t ω=>(sourceRieszBrownianContinuousProcess P F T B g t ω)^2-
      sourceRieszBrownianBracket P F T g t ω) F P := by
  have hm := sourceRieszBrownianContinuousProcess_compensated_square_of_ae_continuous P F T B hB hBa hind hBc g
  have hM := sourceRieszBrownianContinuousProcess_adapted_no_continuity P F T B hB hBa hind g
  have hQ := (sourceRieszBrownianBracket_predictable P F T g).stronglyAdapted
  apply hm.congr (fun t=>(hM t).pow 2 |>.sub (hQ t))
  intro t
  filter_upwards [sourceRieszBrownianBracket_eq_energy P F T g] with ω hω
  simp only [Pi.sub_apply,Pi.pow_apply]
  rw [hω t]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_predictable_compensator_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_predictable_compensator_of_ae_continuous
