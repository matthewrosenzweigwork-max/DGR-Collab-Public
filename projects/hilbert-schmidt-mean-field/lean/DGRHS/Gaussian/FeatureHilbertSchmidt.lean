import DGRHS.Gaussian.FeatureSynthesis
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Concrete square summability of the actual feature readout and the covariance
quadratic-form sum, from finite Bessel and complete-basis Parseval with Tonelli.
DGR source1931: the integral of the squared feature norm is the covariance
basis sum. No nominal trace-class, compactness, eigenbasis or spectral premise.
The countable index may be empty or finite, and features need not be bounded.
-/

open MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace

namespace DGRHS.Gaussian
noncomputable section

variable {ι H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

private theorem integrable_readout_coefficient_sq (k : X → H) (hk2 : MemLp k 2 μ)
    (v : H) : Integrable (fun x => (inner ℝ (k x) v) ^ 2) μ := by
  have h : MemLp (fun x => inner ℝ (k x) v) 2 μ :=
    (memLp_congr_ae (coeFn_featureReadout k hk2 v)).1 (Lp.memLp (featureReadout k hk2 v))
  exact h.integrable_sq

theorem norm_featureReadout_basis_sq (k : X → H) (hk2 : MemLp k 2 μ)
    (b : HilbertBasis ι ℝ H) (i : ι) :
    ‖featureReadout k hk2 (b i)‖ ^ 2 = ∫ x, (inner ℝ (k x) (b i)) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_featureReadout_apply_apply]
  simp only [pow_two]

theorem sum_norm_featureReadout_basis_sq_le (k : X → H) (hk2 : MemLp k 2 μ)
    (b : HilbertBasis ι ℝ H) (s : Finset ι) :
    (∑ i ∈ s, ‖featureReadout k hk2 (b i)‖ ^ 2) ≤ ∫ x, ‖k x‖ ^ 2 ∂μ := by
  classical
  simp_rw [norm_featureReadout_basis_sq]
  rw [← integral_finsetSum s (fun i _ => integrable_readout_coefficient_sq k hk2 (b i))]
  apply integral_mono (integrable_finsetSum s
    (fun i _ => integrable_readout_coefficient_sq k hk2 (b i)))
    ((memLp_two_iff_integrable_sq_norm hk2.aestronglyMeasurable).1 hk2)
  intro x
  calc
    (∑ i ∈ s, (inner ℝ (k x) (b i)) ^ 2) =
        ∑ i ∈ s, ‖inner ℝ (b i) (k x)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_comm (k x) (b i), Real.norm_eq_abs, sq_abs]
    _ ≤ ‖k x‖ ^ 2 := b.orthonormal.sum_inner_products_le (k x) (s := s)

theorem summable_norm_featureReadout_basis_sq (k : X → H) (hk2 : MemLp k 2 μ)
    (b : HilbertBasis ι ℝ H) : Summable (fun i => ‖featureReadout k hk2 (b i)‖ ^ 2) := by
  apply summable_of_sum_le (fun i => sq_nonneg _) (c := ∫ x, ‖k x‖ ^ 2 ∂μ)
  exact sum_norm_featureReadout_basis_sq_le k hk2 b

theorem tsum_norm_featureReadout_basis_sq [Countable ι] (k : X → H)
    (hk2 : MemLp k 2 μ) (b : HilbertBasis ι ℝ H) :
    (∑' i, ‖featureReadout k hk2 (b i)‖ ^ 2) = ∫ x, ‖k x‖ ^ 2 ∂μ := by
  have hi (i : ι) : Integrable (fun x => (inner ℝ (k x) (b i)) ^ 2) μ :=
    integrable_readout_coefficient_sq k hk2 (b i)
  have hs : Summable (fun i => ∫ x, ‖(inner ℝ (k x) (b i)) ^ 2‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (sq_nonneg _), norm_featureReadout_basis_sq] using
      summable_norm_featureReadout_basis_sq k hk2 b
  have hp (x : X) : (∑' i, (inner ℝ (k x) (b i)) ^ 2) = ‖k x‖ ^ 2 := by
    have h := b.tsum_inner_mul_inner (k x) (k x)
    rw [real_inner_self_eq_norm_sq] at h
    convert h using 1
    congr 1
    funext i
    rw [real_inner_comm (b i) (k x)]
    ring
  calc
    (∑' i, ‖featureReadout k hk2 (b i)‖ ^ 2) =
        ∑' i, ∫ x, (inner ℝ (k x) (b i)) ^ 2 ∂μ := by
      simp_rw [norm_featureReadout_basis_sq]
    _ = ∫ x, (∑' i, (inner ℝ (k x) (b i)) ^ 2) ∂μ :=
      integral_tsum_of_summable_integral_norm hi hs
    _ = ∫ x, ‖k x‖ ^ 2 ∂μ := integral_congr_ae (Filter.Eventually.of_forall hp)

theorem tsum_inner_featureCovariance_basis [Countable ι] (k : X → H)
    (hk2 : MemLp k 2 μ) (b : HilbertBasis ι ℝ H) :
    (∑' i, inner ℝ (featureCovariance k hk2 (b i)) (b i)) = ∫ x, ‖k x‖ ^ 2 ∂μ := by
  simp_rw [inner_featureCovariance_self]
  exact tsum_norm_featureReadout_basis_sq k hk2 b

end
end DGRHS.Gaussian

#check DGRHS.Gaussian.norm_featureReadout_basis_sq
#print axioms DGRHS.Gaussian.norm_featureReadout_basis_sq
#check DGRHS.Gaussian.sum_norm_featureReadout_basis_sq_le
#print axioms DGRHS.Gaussian.sum_norm_featureReadout_basis_sq_le
#check DGRHS.Gaussian.summable_norm_featureReadout_basis_sq
#print axioms DGRHS.Gaussian.summable_norm_featureReadout_basis_sq
#check DGRHS.Gaussian.tsum_norm_featureReadout_basis_sq
#print axioms DGRHS.Gaussian.tsum_norm_featureReadout_basis_sq
#check DGRHS.Gaussian.tsum_inner_featureCovariance_basis
#print axioms DGRHS.Gaussian.tsum_inner_featureCovariance_basis
