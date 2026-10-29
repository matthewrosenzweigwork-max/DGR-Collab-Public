import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! UNCOMPILED draft. Native Levy continuity turns continuity of the real
and imaginary Fourier test pairings into narrow continuity of a probability
curve. Applying this to a static Cb2 weak PDE still requires the elementary
Cb2 bounds for those fixed tests. No continuity of the density in L1 is used. -/
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology RealInnerProductSpace
namespace DGRHS.Commutator
variable {P E : Type*} [TopologicalSpace P] [SequentialSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma continuous_probability_of_continuous_charFun
    (μ : P → ProbabilityMeasure E)
    (h : ∀ ξ : E, Continuous (fun p => charFun (μ p) ξ)) : Continuous μ := by
  apply continuous_iff_seqContinuous.mpr
  intro u p hu
  exact ProbabilityMeasure.tendsto_of_tendsto_charFun
    (fun ξ => ((h ξ).tendsto p).comp hu)

lemma continuous_probability_of_continuous_character_tests
    (μ : P → ProbabilityMeasure E)
    (hre : ∀ ξ : E, Continuous (fun p =>
      ∫ x, (innerProbChar ξ x).re ∂(μ p : Measure E)))
    (him : ∀ ξ : E, Continuous (fun p =>
      ∫ x, (innerProbChar ξ x).im ∂(μ p : Measure E))) : Continuous μ := by
  apply continuous_probability_of_continuous_charFun μ
  intro ξ
  have he (p : P) : charFun (μ p) ξ =
      (∫ x, (innerProbChar ξ x).re ∂(μ p : Measure E) : ℝ) +
        (∫ x, (innerProbChar ξ x).im ∂(μ p : Measure E) : ℝ) * Complex.I := by
    rw [charFun_eq_integral_innerProbChar]
    exact (integral_re_add_im ((innerProbChar ξ).integrable (μ p))).symm
  simp_rw [he]
  exact (Complex.continuous_ofReal.comp (hre ξ)).add
    ((Complex.continuous_ofReal.comp (him ξ)).mul continuous_const)

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.continuous_probability_of_continuous_charFun
#print axioms DGRHS.Commutator.continuous_probability_of_continuous_charFun
#check @DGRHS.Commutator.continuous_probability_of_continuous_character_tests
#print axioms DGRHS.Commutator.continuous_probability_of_continuous_character_tests
