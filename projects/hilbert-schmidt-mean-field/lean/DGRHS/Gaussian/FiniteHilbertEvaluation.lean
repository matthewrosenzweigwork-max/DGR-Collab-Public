import DGRHS.Gaussian.FiniteEvaluation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
The finite feature evaluation instantiated on an actual finite Hilbert basis.
This adapter preserves the feature norm as the Gaussian variance. Its basis
parameter is a finite supporting construction, not an extra premise in a paper
result. The infinite-dimensional jointly measurable representative remains open.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace DGRHS.Gaussian

variable {ι H X : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X]

/-- Finite Parseval identity from the actual Hilbert basis expansion. -/
theorem finiteBasis_sum_sq_inner (b : HilbertBasis ι ℝ H) (v : H) :
    (∑ i, (inner ℝ (b i) v) ^ 2) = ‖v‖ ^ 2 := by
  classical
  have he : (∑ i, (inner ℝ (b i) v) • b i) = v := by
    simpa only [tsum_fintype, b.repr_apply_apply] using (b.hasSum_repr v).tsum_eq
  calc
    (∑ i, (inner ℝ (b i) v) ^ 2) = inner ℝ (∑ i, (inner ℝ (b i) v) • b i) v := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      simp [inner_smul_left, pow_two]
    _ = inner ℝ v v := by rw [he]
    _ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v

noncomputable def finiteHilbertEvaluation (b : HilbertBasis ι ℝ H) (k : X → H)
    (x : X) (z : ι → ℝ) : ℝ :=
  finiteFeatureEvaluation (fun x i => inner ℝ (b i) (k x)) x z

/-- Explicit jointly measurable evaluation, derived from measurable features. -/
theorem measurable_finiteHilbertEvaluation [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ι ℝ H) {k : X → H} (hk : Measurable k) :
    Measurable (fun p : X × (ι → ℝ) => finiteHilbertEvaluation b k p.1 p.2) := by
  apply measurable_finiteFeatureEvaluation
  apply measurable_pi_lambda
  intro i
  exact (continuous_const.inner continuous_id).measurable.comp hk

theorem hasGaussianLaw_finiteHilbertEvaluation (b : HilbertBasis ι ℝ H)
    (k : X → H) (x : X) :
    HasGaussianLaw (finiteHilbertEvaluation b k x) (finiteStandardGaussian ι) :=
  hasGaussianLaw_finiteFeatureEvaluation (fun x i => inner ℝ (b i) (k x)) x

/-- Source variance D(x) equals the actual feature norm squared. -/
theorem variance_finiteHilbertEvaluation (b : HilbertBasis ι ℝ H)
    (k : X → H) (x : X) :
    Var[finiteHilbertEvaluation b k x; finiteStandardGaussian ι] = ‖k x‖ ^ 2 := by
  unfold finiteHilbertEvaluation
  rw [variance_finiteFeatureEvaluation, finiteBasis_sum_sq_inner]

/-- Mean zero under the actual Gaussian sample law. -/
theorem integral_finiteHilbertEvaluation_eq_zero_gaussian (b : HilbertBasis ι ℝ H)
    (k : X → H) (x : X) :
    ∫ z, finiteHilbertEvaluation b k x z ∂finiteStandardGaussian ι = 0 :=
  integral_finiteFeatureEvaluation_eq_zero_gaussian (fun x i => inner ℝ (b i) (k x)) x

/-- The exact scalar Gaussian law has the actual feature norm as its variance. -/
theorem map_finiteHilbertEvaluation_eq_gaussianReal (b : HilbertBasis ι ℝ H)
    (k : X → H) (x : X) :
    (finiteStandardGaussian ι).map (finiteHilbertEvaluation b k x) =
      gaussianReal 0 (Real.toNNReal (‖k x‖ ^ 2)) := by
  unfold finiteHilbertEvaluation
  rw [map_finiteFeatureEvaluation_eq_gaussianReal, finiteBasis_sum_sq_inner]

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.finiteBasis_sum_sq_inner
#print axioms DGRHS.Gaussian.measurable_finiteHilbertEvaluation
#print axioms DGRHS.Gaussian.hasGaussianLaw_finiteHilbertEvaluation
#print axioms DGRHS.Gaussian.variance_finiteHilbertEvaluation

#print axioms DGRHS.Gaussian.integral_finiteHilbertEvaluation_eq_zero_gaussian
#print axioms DGRHS.Gaussian.map_finiteHilbertEvaluation_eq_gaussianReal

#check DGRHS.Gaussian.finiteBasis_sum_sq_inner
#check DGRHS.Gaussian.finiteHilbertEvaluation
#check DGRHS.Gaussian.measurable_finiteHilbertEvaluation
#check DGRHS.Gaussian.hasGaussianLaw_finiteHilbertEvaluation
#check DGRHS.Gaussian.variance_finiteHilbertEvaluation
#check DGRHS.Gaussian.integral_finiteHilbertEvaluation_eq_zero_gaussian
#check DGRHS.Gaussian.map_finiteHilbertEvaluation_eq_gaussianReal
