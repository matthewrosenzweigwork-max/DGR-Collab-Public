import DGRHS.Commutator.SourceMovingLawIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! UNCOMPILED and outside the proposed first check. The bounded joint
continuous temporal derivative yields a continuous unit-time average. A
narrowly continuous moving probability law can then be integrated against
that average. These are analytic ingredients, not a desired mean-field
endpoint identity. For finite source horizons the supplied derivative is
extended by constant endpoint clamping before this generic lemma is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace DGRHS.Commutator
variable {E : Type*} [MetricSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

def sourceUnitTimeAverage (δ : ℝ × E → ℝ) (r h : ℝ) (x : E) : ℝ :=
  ∫ u in (0:ℝ)..1, δ (r + u*h,x)

lemma continuous_sourceUnitTimeAverage
    (δ : ℝ × E → ℝ) (hδ : Continuous δ)
    (C : ℝ) (hC : ∀ p, |δ p| ≤ C) (r : ℝ) :
    Continuous (fun p : ℝ × E => sourceUnitTimeAverage δ r p.1 p.2) := by
  unfold sourceUnitTimeAverage
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => C)
  · intro p
    exact (hδ.comp ((continuous_const.add (continuous_id.mul continuous_const)).prodMk
      continuous_const)).measurable.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall (fun u _ => by simpa only [Real.norm_eq_abs] using hC (r+u*p.1,p.2))
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun u _ =>
      hδ.comp ((continuous_const.add (continuous_const.mul continuous_fst)).prodMk continuous_snd))

lemma sourceUnitTimeAverage_bound
    (δ : ℝ × E → ℝ) (C : ℝ) (hC : ∀ p, |δ p| ≤ C)
    (r h : ℝ) (x : E) : |sourceUnitTimeAverage δ r h x| ≤ C := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := C) (f := fun u => δ (r+u*h,x))
    (fun u _ => by simpa only [Real.norm_eq_abs] using hC (r+u*h,x))
  simpa [sourceUnitTimeAverage] using hb

lemma tendsto_integral_sourceUnitTimeAverage
    (μ : ℝ → ProbabilityMeasure E) (hμ : Continuous μ)
    (δ : ℝ × E → ℝ) (hδ : Continuous δ)
    (C : ℝ) (hC : ∀ p, |δ p| ≤ C) (r : ℝ) :
    Tendsto (fun h => ∫ x, sourceUnitTimeAverage δ r h x ∂(μ (r+h) : Measure E))
      (𝓝 0) (𝓝 (∫ x, δ (r,x) ∂(μ r : Measure E))) := by
  have hc := continuous_integral_moving_probability (fun h : ℝ => h) continuous_id
    (fun h => μ (r+h)) (hμ.comp (continuous_const.add continuous_id))
    (fun p : ℝ × E => sourceUnitTimeAverage δ r p.1 p.2)
    (continuous_sourceUnitTimeAverage δ hδ C hC r) C
    (fun p => sourceUnitTimeAverage_bound δ C hC r p.1 p.2)
  simpa [sourceUnitTimeAverage] using hc.tendsto 0

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceUnitTimeAverage
#print axioms DGRHS.Commutator.sourceUnitTimeAverage
#check @DGRHS.Commutator.continuous_sourceUnitTimeAverage
#print axioms DGRHS.Commutator.continuous_sourceUnitTimeAverage
#check @DGRHS.Commutator.sourceUnitTimeAverage_bound
#print axioms DGRHS.Commutator.sourceUnitTimeAverage_bound
#check @DGRHS.Commutator.tendsto_integral_sourceUnitTimeAverage
#print axioms DGRHS.Commutator.tendsto_integral_sourceUnitTimeAverage
