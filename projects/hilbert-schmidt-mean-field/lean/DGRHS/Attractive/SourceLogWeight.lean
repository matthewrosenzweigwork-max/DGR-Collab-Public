/- Outside proof pending exact reviewed A8 integration/source uniform checks.
For beta>0 the attractive singular Boltzmann weight is infinite at a particle
collision. Beta=0 is separately defined to be one. The original pair-L1
assumption proves this extended weight agrees AE with its proper real version. -/
import DGRHS.Attractive.SourceLogUniform
import DGRHS.Gaussian.SingularLogSamples
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

def attractiveLogSingularWeight (μ : Measure E) (β : ℝ) (N : ℕ) (x : Fin N → E) : ℝ≥0∞ := by
  classical
  exact if β=0 then 1 else
    if ∀ i j : Fin N,i ≠ j → x i ≠ x j then
      ENNReal.ofReal (Real.exp (-β*(N : ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ attractiveLogInteraction p.1 p.2)
        (DGRHS.potential μ attractiveLogInteraction)
        (DGRHS.interactionEnergy μ attractiveLogInteraction) N x))
    else ∞

theorem attractiveLogSingularWeight_ae (μ : Measure E) [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p,DGRHS.Gaussian.singularAbsLog p ∂μ.prod μ)<∞)
    (β : ℝ) (N : ℕ) :
    attractiveLogSingularWeight μ β N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => ENNReal.ofReal (Real.exp (-β*(N : ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ attractiveLogInteraction p.1 p.2)
        (DGRHS.potential μ attractiveLogInteraction)
        (DGRHS.interactionEnergy μ attractiveLogInteraction) N x))) := by
  filter_upwards [DGRHS.Gaussian.singularAbsLog_iid_collision_free μ hpair N] with x hx
  by_cases hb : β=0
  · simp [attractiveLogSingularWeight,hb]
  · simp only [attractiveLogSingularWeight,if_neg hb,if_pos hx]

end DGRHS.Attractive
#check @DGRHS.Attractive.attractiveLogSingularWeight_ae
#print axioms DGRHS.Attractive.attractiveLogSingularWeight_ae
