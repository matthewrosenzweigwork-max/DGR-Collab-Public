import DGRHS.Commutator.SourceRieszPredictableVersion

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

def sourceRieszBrownianBracket (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ℝ≥0→Ω→ℝ := sourceRieszPredictableVersion F (sourceRieszBrownianEnergy P F T g)
      (sourceRieszBrownianEnergy_adapted P F T g)

lemma sourceRieszBrownianBracket_predictable
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    IsStronglyPredictable F (sourceRieszBrownianBracket P F T g) :=
  sourceRieszPredictableVersion_predictable _ _ _

lemma sourceRieszBrownianBracket_eq_energy
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianBracket P F T g t ω=sourceRieszBrownianEnergy P F T g t ω :=
  sourceRieszPredictableVersion_ae_eq P F _ _ (sourceRieszBrownianEnergy_ae_continuous P F T g)

lemma sourceRieszBrownianBracket_zero
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (ω : Ω) :
    sourceRieszBrownianBracket P F T g 0 ω=0 := by
  exact (sourceRieszPredictableVersion_bot F _ _ ω).trans (sourceRieszBrownianEnergy_zero P F T g ω)

lemma sourceRieszBrownianBracket_integrable
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    Integrable (sourceRieszBrownianBracket P F T g t) P :=
  (sourceRieszBrownianEnergy_integrable P F T g t).congr
    ((sourceRieszBrownianBracket_eq_energy P F T g).mono (fun ω hω=>(hω t).symm))

lemma sourceRieszBrownianBracket_ae_regular
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∀ᵐ ω ∂P,Continuous (fun t=>sourceRieszBrownianBracket P F T g t ω) ∧
      Monotone (fun t=>sourceRieszBrownianBracket P F T g t ω) := by
  filter_upwards [sourceRieszBrownianBracket_eq_energy P F T g,
    sourceRieszBrownianEnergy_ae_continuous P F T g,
    (sourceRieszBrownianEnergy_product_integrable P F T g).prod_left_ae] with ω he hc hi
  have he' : (fun t=>sourceRieszBrownianBracket P F T g t ω)=
      (fun t=>sourceRieszBrownianEnergy P F T g t ω) := funext he
  rw [he']
  refine ⟨hc,?_⟩
  intro s t hst
  exact setIntegral_mono_set hi.integrableOn (ae_of_all _ fun r=>sq_nonneg _)
    (ae_of_all _ fun r hr=>⟨hr.1,hr.2.trans hst⟩)

variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
variable (hBc : ∀ ω,Continuous (fun r=>B r ω))

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_predictable_compensator
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (fun t ω=>(sourceRieszBrownianContinuousProcess P F T B g t ω)^2-
      sourceRieszBrownianBracket P F T g t ω) F P := by
  have hm := sourceRieszBrownianContinuousProcess_compensated_square P F T B hB hBa hind hBc g
  have hM := sourceRieszBrownianContinuousProcess_adapted P F T B hB hBa hind hBc g
  have hQ := (sourceRieszBrownianBracket_predictable P F T g).stronglyAdapted
  apply hm.congr (fun t=>(hM t).pow 2 |>.sub (hQ t))
  intro t
  filter_upwards [sourceRieszBrownianBracket_eq_energy P F T g] with ω hω
  simp only [Pi.sub_apply,Pi.pow_apply]
  rw [hω t]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianBracket
#print axioms DGRHS.Commutator.sourceRieszBrownianBracket
#check @DGRHS.Commutator.sourceRieszBrownianBracket_predictable
#print axioms DGRHS.Commutator.sourceRieszBrownianBracket_predictable
#check @DGRHS.Commutator.sourceRieszBrownianBracket_eq_energy
#print axioms DGRHS.Commutator.sourceRieszBrownianBracket_eq_energy
#check @DGRHS.Commutator.sourceRieszBrownianBracket_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianBracket_zero
#check @DGRHS.Commutator.sourceRieszBrownianBracket_integrable
#print axioms DGRHS.Commutator.sourceRieszBrownianBracket_integrable
#check @DGRHS.Commutator.sourceRieszBrownianBracket_ae_regular
#print axioms DGRHS.Commutator.sourceRieszBrownianBracket_ae_regular
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_predictable_compensator
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_predictable_compensator
