import DGRHS.Gaussian.FeatureOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
Actual feature synthesis is the adjoint of the checked feature readout.
Its Bochner representation and the covariance formula are proved for the given
square-integrable feature, with no boundedness or finite-dimensional premise.
This supplies the integral/positivity portion of preserved DGR TeX1926–1935;
compactness, trace, spectrum and determinant identification are separate tasks.
-/

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

namespace DGRHS.Gaussian
noncomputable section

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The synthesis map is the actual Hilbert-space adjoint of the readout. -/
def featureSynthesis (k : X → H) (hk2 : MemLp k 2 μ) : Lp ℝ 2 μ →L[ℝ] H :=
  (featureReadout k hk2).adjoint

/-- The actual covariance operator of the given feature. -/
def featureCovariance (k : X → H) (hk2 : MemLp k 2 μ) : H →L[ℝ] H :=
  (featureSynthesis k hk2).comp (featureReadout k hk2)

theorem integrable_featureSynthesis_integrand (k : X → H) (hk2 : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) : Integrable (fun x => f x • k x) μ := by
  have h : MemLp (fun x => f x • k x) 1 μ := (Lp.memLp f).smul hk2
  exact h.integrable (by norm_num)

theorem featureSynthesis_eq_integral (k : X → H) (hk2 : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) : featureSynthesis k hk2 f = ∫ x, f x • k x ∂μ := by
  apply ext_inner_left ℝ
  intro v
  change inner ℝ v ((featureReadout k hk2).adjoint f) = _
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def,
    ← integral_inner (integrable_featureSynthesis_integrand k hk2 f) v]
  apply integral_congr_ae
  filter_upwards [coeFn_featureReadout k hk2 v] with x hx
  rw [hx, inner_smul_right]
  change f x * inner ℝ (k x) v = f x * inner ℝ v (k x)
  rw [real_inner_comm (k x) v]

theorem integrable_featureCovariance_integrand (k : X → H) (hk2 : MemLp k 2 μ)
    (v : H) : Integrable (fun x => inner ℝ (k x) v • k x) μ := by
  apply (integrable_featureSynthesis_integrand k hk2 (featureReadout k hk2 v)).congr
  filter_upwards [coeFn_featureReadout k hk2 v] with x hx
  rw [hx]

theorem featureCovariance_eq_integral (k : X → H) (hk2 : MemLp k 2 μ)
    (v : H) : featureCovariance k hk2 v = ∫ x, inner ℝ (k x) v • k x ∂μ := by
  change featureSynthesis k hk2 (featureReadout k hk2 v) = _
  rw [featureSynthesis_eq_integral]
  apply integral_congr_ae
  filter_upwards [coeFn_featureReadout k hk2 v] with x hx
  rw [hx]

theorem featureCovariance_isSymmetric (k : X → H) (hk2 : MemLp k 2 μ) :
    (featureCovariance k hk2).IsSymmetric := by
  intro v w
  change inner ℝ ((featureReadout k hk2).adjoint (featureReadout k hk2 v)) w =
    inner ℝ v ((featureReadout k hk2).adjoint (featureReadout k hk2 w))
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

theorem inner_featureCovariance_self (k : X → H) (hk2 : MemLp k 2 μ) (v : H) :
    inner ℝ (featureCovariance k hk2 v) v = ‖featureReadout k hk2 v‖ ^ 2 := by
  change inner ℝ ((featureReadout k hk2).adjoint (featureReadout k hk2 v)) v = _
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]

theorem featureCovariance_nonneg (k : X → H) (hk2 : MemLp k 2 μ) (v : H) :
    0 ≤ inner ℝ (featureCovariance k hk2 v) v := by
  rw [inner_featureCovariance_self]
  exact sq_nonneg _

end
end DGRHS.Gaussian

#check DGRHS.Gaussian.featureSynthesis
#print axioms DGRHS.Gaussian.featureSynthesis
#check DGRHS.Gaussian.featureCovariance
#print axioms DGRHS.Gaussian.featureCovariance
#check DGRHS.Gaussian.integrable_featureSynthesis_integrand
#print axioms DGRHS.Gaussian.integrable_featureSynthesis_integrand
#check DGRHS.Gaussian.featureSynthesis_eq_integral
#print axioms DGRHS.Gaussian.featureSynthesis_eq_integral
#check DGRHS.Gaussian.integrable_featureCovariance_integrand
#print axioms DGRHS.Gaussian.integrable_featureCovariance_integrand
#check DGRHS.Gaussian.featureCovariance_eq_integral
#print axioms DGRHS.Gaussian.featureCovariance_eq_integral
#check DGRHS.Gaussian.featureCovariance_isSymmetric
#print axioms DGRHS.Gaussian.featureCovariance_isSymmetric
#check DGRHS.Gaussian.inner_featureCovariance_self
#print axioms DGRHS.Gaussian.inner_featureCovariance_self
#check DGRHS.Gaussian.featureCovariance_nonneg
#print axioms DGRHS.Gaussian.featureCovariance_nonneg
