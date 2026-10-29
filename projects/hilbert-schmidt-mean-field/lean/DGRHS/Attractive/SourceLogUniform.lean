/- Outside proof: literal attractive source instance, to check after A8 review.
Original singular pair-L1 uses singularAbsLog finite, not Real.log0 alone.
The finite row hypothesis is extended-valued; its supremum stays outside
the integral, and this theorem adds no bounded-density hypothesis. -/
import DGRHS.Attractive.SourceUniform
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

def attractiveLogInteraction (x y : E) : ℝ := Real.log ‖x-y‖

theorem attractiveLog_source_uniform (μ : Measure E) [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p,DGRHS.Gaussian.singularAbsLog p ∂μ.prod μ)<∞)
    (C β : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ p : ℕ,1 ≤ p → ∀ y,
      (∫⁻ x,ENNReal.ofReal
        (|DGRHS.centeredKernel μ attractiveLogInteraction x y|^p) ∂μ) ≤
          ENNReal.ofReal (C^p*(p.factorial : ℝ)))
    (hβ : 0 ≤ β) (hsmall : β*(attractiveMomentConstant*C)<1)
    (htail : Integrable
      (fun x => Real.exp (2*β*DGRHS.potential μ attractiveLogInteraction x)) μ) :
    ∀ N : ℕ,0<N →
    Integrable (fun x : Fin N → E => Real.exp (-β*(N : ℝ)*
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ attractiveLogInteraction p.1 p.2)
        (DGRHS.potential μ attractiveLogInteraction)
        (DGRHS.interactionEnergy μ attractiveLogInteraction) N x))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → E,Real.exp (-β*(N : ℝ)*
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ attractiveLogInteraction p.1 p.2)
        (DGRHS.potential μ attractiveLogInteraction)
        (DGRHS.interactionEnergy μ attractiveLogInteraction) N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (β*|DGRHS.interactionEnergy μ attractiveLogInteraction|)*
        Real.sqrt (2/(1-(β*(attractiveMomentConstant*C))^2))*
        Real.sqrt (∫ x,Real.exp
          (2*β*DGRHS.potential μ attractiveLogInteraction x) ∂μ) := by
  have hsign : Function.uncurry (attractiveLogInteraction (E := E)) =
      -DGRHS.Gaussian.logPhysicalPair := by
    funext p
    simp only [Function.uncurry,attractiveLogInteraction,Pi.neg_apply,
      DGRHS.Gaussian.logPhysicalPair,neg_neg]
  have hWi : Integrable (Function.uncurry (attractiveLogInteraction (E := E))) (μ.prod μ) := by
    rw [hsign]
    exact ((DGRHS.Gaussian.singularAbsLog_finite_iff μ).mp hpair).1.neg
  have hWm : StronglyMeasurable (Function.uncurry (attractiveLogInteraction (E := E))) := by
    rw [hsign]
    exact (DGRHS.Gaussian.measurable_logPhysicalPair (E := E)).neg.stronglyMeasurable
  have hs : ∀ x y : E,attractiveLogInteraction x y=attractiveLogInteraction y x := by
    intro x y
    unfold attractiveLogInteraction
    rw [norm_sub_rev]
  have hm := (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ
    (Function.uncurry attractiveLogInteraction) hWm).measurable
  have hr := rowFactorialMoments_of_lintegral μ
    (fun p : E × E => DGRHS.centeredKernel μ attractiveLogInteraction p.1 p.2) hm C hC hrow
  intro N hN
  exact source_uniform_partition attractiveLogInteraction hWm hWi hs C β hr hβ hsmall htail N hN

end DGRHS.Attractive
#check @DGRHS.Attractive.attractiveLog_source_uniform
#print axioms DGRHS.Attractive.attractiveLog_source_uniform
