import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Prod

/-! UNCOMPILED draft. A bounded jointly continuous moving test against a
narrowly continuous law is continuous. The proof is an application of native
weak continuity of product laws to the time Dirac measure. It imposes no
uniform-in-space continuity of time difference quotients. This adapter does
not itself prove narrow continuity from a static weak PDE. -/
noncomputable section
open MeasureTheory Set
open scoped Topology BoundedContinuousFunction
namespace DGRHS.Commutator

variable {P X Y : Type*} [TopologicalSpace P]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

lemma continuous_integral_moving_probability_bcf
    (a : P → X) (ha : Continuous a) (μ : P → ProbabilityMeasure Y)
    (hμ : Continuous μ) (q : (X × Y) →ᵇ ℝ) :
    Continuous (fun p => ∫ y, q (a p, y) ∂(μ p : Measure Y)) := by
  have hprod : Continuous (fun p => (diracProba (a p)).prod (μ p)) :=
    ProbabilityMeasure.continuous_prod.comp ((continuous_diracProba.comp ha).prodMk hμ)
  have h := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction q).comp hprod
  have he (p : P) :
      (∫ z, q z ∂((diracProba (a p)).prod (μ p) : Measure (X × Y))) =
        ∫ y, q (a p, y) ∂(μ p : Measure Y) := by
    change (∫ z, q z ∂(Measure.dirac (a p)).prod (μ p : Measure Y)) = _
    rw [integral_prod _ (q.integrable _)]
    simp
  simpa only [Function.comp_def, he] using h

lemma continuous_integral_moving_probability
    (a : P → X) (ha : Continuous a) (μ : P → ProbabilityMeasure Y)
    (hμ : Continuous μ) (q : X × Y → ℝ) (hq : Continuous q)
    (C : ℝ) (hC : ∀ z, |q z| ≤ C) :
    Continuous (fun p => ∫ y, q (a p, y) ∂(μ p : Measure Y)) := by
  let q' : (X × Y) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨q, hq⟩ (2*C)
    (fun x y => (dist_le_norm_add_norm (q x) (q y)).trans (by
      simpa only [Real.norm_eq_abs, two_mul] using add_le_add (hC x) (hC y)))
  exact continuous_integral_moving_probability_bcf a ha μ hμ q'

lemma continuous_integral_moving_probability_pair
    (a : P → X) (ha : Continuous a) (μ : P → ProbabilityMeasure Y)
    (hμ : Continuous μ) (q : X × (Y × Y) → ℝ) (hq : Continuous q)
    (C : ℝ) (hC : ∀ z, |q z| ≤ C) :
    Continuous (fun p => ∫ y, ∫ z, q (a p, (y,z))
      ∂(μ p : Measure Y) ∂(μ p : Measure Y)) := by
  have hp : Continuous (fun p => (μ p).prod (μ p)) :=
    ProbabilityMeasure.continuous_prod.comp (hμ.prodMk hμ)
  have h := continuous_integral_moving_probability a ha (fun p => (μ p).prod (μ p))
    hp q hq C hC
  have he (p : P) :
      (∫ yz, q (a p, yz) ∂((μ p).prod (μ p) : Measure (Y × Y))) =
        ∫ y, ∫ z, q (a p, (y,z)) ∂(μ p : Measure Y) ∂(μ p : Measure Y) := by
    change (∫ yz, q (a p, yz) ∂(μ p : Measure Y).prod (μ p : Measure Y)) = _
    apply integral_prod
    exact Integrable.mono' (integrable_const C)
      ((hq.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun yz => by simpa only [Real.norm_eq_abs] using hC (a p,yz)))
  simpa only [he] using h

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.continuous_integral_moving_probability_bcf
#print axioms DGRHS.Commutator.continuous_integral_moving_probability_bcf
#check @DGRHS.Commutator.continuous_integral_moving_probability
#print axioms DGRHS.Commutator.continuous_integral_moving_probability
#check @DGRHS.Commutator.continuous_integral_moving_probability_pair
#print axioms DGRHS.Commutator.continuous_integral_moving_probability_pair
