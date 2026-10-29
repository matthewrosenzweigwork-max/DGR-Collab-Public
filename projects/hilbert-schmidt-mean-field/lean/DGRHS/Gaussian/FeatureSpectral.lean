/- Actual feature-kernel eigenvalue trace from the readout/adjoint and two
complete Hilbert bases. Development draft pending actual Lean diagnostics.
No eigenvalue summability, positive spectrum or trace is assumed in the factory. -/
import DGRHS.Gaussian.FeatureKernel
import DGRHS.Gaussian.FeatureHilbertSchmidt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace DGRHS.Gaussian
universe u v
variable {H : Type v} {X : Type u} {ι κ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

private lemma parseval_sq {E j : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis j ℝ E) (z : E) :
    (∑' i, (inner ℝ z (b i))^2) = ‖z‖^2 := by
  have h := b.tsum_inner_mul_inner z z
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  congr 1
  funext i
  rw [real_inner_comm (b i) z]
  ring

private lemma summable_parseval_sq {E j : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis j ℝ E) (z : E) :
    Summable (fun i ↦ (inner ℝ z (b i))^2) := by
  apply (b.summable_inner_mul_inner z z).congr
  intro i
  rw [real_inner_comm (b i) z]
  ring

/-- The synthesis square sum is the same actual feature second moment. -/
theorem featureSynthesis_hilbertSchmidt [Countable κ] [Countable ι]
    (k : X → H) (hk2 : MemLp k 2 μ)
    (b : HilbertBasis κ ℝ H) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    Summable (fun i ↦ ‖featureSynthesis k hk2 (e i)‖^2) ∧
      (∑' i, ‖featureSynthesis k hk2 (e i)‖^2) = ∫ x, ‖k x‖^2 ∂μ := by
  let m : κ → ι → ℝ := fun j i ↦ (inner ℝ (featureReadout k hk2 (b j)) (e i))^2
  have hrow (j : κ) : (∑' i, m j i) = ‖featureReadout k hk2 (b j)‖^2 :=
    parseval_sq e (featureReadout k hk2 (b j))
  have hcoef (j : κ) (i : ι) : m j i = (inner ℝ (featureSynthesis k hk2 (e i)) (b j))^2 := by
    dsimp [m]
    rw [real_inner_comm (e i) (featureReadout k hk2 (b j))]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hcol (i : ι) : (∑' j, m j i) = ‖featureSynthesis k hk2 (e i)‖^2 := by
    simp_rw [hcoef]
    exact parseval_sq b (featureSynthesis k hk2 (e i))
  have hprod : Summable (Function.uncurry m) := by
    apply (summable_prod_of_nonneg (fun p ↦ sq_nonneg _)).2
    constructor
    · intro j
      exact summable_parseval_sq e (featureReadout k hk2 (b j))
    · exact (summable_norm_featureReadout_basis_sq k hk2 b).congr (fun j ↦ (hrow j).symm)
  constructor
  · exact hprod.prod_symm.prod.congr hcol
  · calc
      (∑' i, ‖featureSynthesis k hk2 (e i)‖^2) = ∑' i, ∑' j, m j i :=
        tsum_congr (fun i ↦ (hcol i).symm)
      _ = ∑' j, ∑' i, m j i := hprod.tsum_comm
      _ = ∑' j, ‖featureReadout k hk2 (b j)‖^2 := tsum_congr hrow
      _ = ∫ x, ‖k x‖^2 ∂μ := tsum_norm_featureReadout_basis_sq k hk2 b

lemma norm_featureSynthesis_eigenbasis_sq (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) (e i) = eig i • e i) (i : ι) :
    ‖featureSynthesis k hk2 (e i)‖^2 = eig i := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (featureSynthesis k hk2 (e i)) ((featureReadout k hk2).adjoint (e i)) = eig i
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (((featureReadout k hk2).comp (featureSynthesis k hk2)) (e i)) (e i) = eig i
  rw [← integralOperator_featureKernel_eq k hk hk2, he i, real_inner_smul_left,
    real_inner_self_eq_norm_sq, e.orthonormal.1 i, one_pow, mul_one]

lemma featureCovariance_synthesis_eigenvector (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) (e i) = eig i • e i) (i : ι) :
    featureCovariance k hk2 (featureSynthesis k hk2 (e i)) =
      eig i • featureSynthesis k hk2 (e i) := by
  have h := congrArg (featureSynthesis k hk2) (he i)
  rw [integralOperator_featureKernel_eq k hk hk2] at h
  simpa only [featureCovariance, ContinuousLinearMap.comp_apply, map_smul] using h

/-- All actual eigenvalues of the Gram integral operator have finite positive trace. -/
theorem featureKernel_spectral_trace [Countable κ] [Countable ι]
    (k : X → H) (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ)
    (b : HilbertBasis κ ℝ H) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) (e i) = eig i • e i) :
    (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖^2 ∂μ := by
  obtain ⟨hs, ht⟩ := featureSynthesis_hilbertSchmidt k hk2 b e
  have hn := norm_featureSynthesis_eigenbasis_sq k hk hk2 eig e he
  refine ⟨fun i ↦ ?_, hs.congr hn, ?_⟩
  · rw [← hn i]
    exact sq_nonneg _
  · calc
      (∑' i, eig i) = ∑' i, ‖featureSynthesis k hk2 (e i)‖^2 := tsum_congr (fun i ↦ (hn i).symm)
      _ = ∫ x, ‖k x‖^2 ∂μ := ht

/-- Countable positive spectral trace is constructed from the actual source hypotheses. -/
theorem exists_featureKernel_spectral_trace [TopologicalSpace.SeparableSpace H]
    [MeasurableSpace.CountablyGenerated X] (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (hmean : (∫ x, k x ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator (featureKernel k) (memLp_featureKernel k hk hk2)
        (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖^2 ∂μ ∧
      ∀ i, eig i ≠ 0 → (∫ x, e i x ∂μ) = 0 := by
  classical
  obtain ⟨j, b, _⟩ := exists_hilbertBasis ℝ H
  letI : Countable j := HilbertBasis.countable_of_separable_index b
  have hsym : ∀ᵐ p ∂μ.prod μ, featureKernel k p.swap = featureKernel k p :=
    Filter.Eventually.of_forall (featureKernel_symmetric k)
  obtain ⟨ι, eig, e, hi, he⟩ := DGRHS.Kernel.exists_integralOperator_eigenbasis
    (featureKernel k) (memLp_featureKernel k hk hk2) hsym
  letI : Countable ι := hi
  obtain ⟨hp, hs, ht⟩ := featureKernel_spectral_trace k hk hk2 b eig e he
  refine ⟨ι, eig, e, hi, he, hp, hs, ht, ?_⟩
  intro i hne
  apply DGRHS.Kernel.integral_eigenfunction_eq_zero (featureKernel k)
    (memLp_featureKernel k hk hk2) hsym
    (Filter.Eventually.of_forall (integral_featureKernel_right k hk2 hmean)) (e i) hne (he i)
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.featureSynthesis_hilbertSchmidt
#print axioms DGRHS.Gaussian.featureKernel_spectral_trace
#print axioms DGRHS.Gaussian.exists_featureKernel_spectral_trace
#print axioms DGRHS.Gaussian.featureCovariance_synthesis_eigenvector
#check DGRHS.Gaussian.featureSynthesis_hilbertSchmidt
#check DGRHS.Gaussian.featureKernel_spectral_trace
#check DGRHS.Gaussian.exists_featureKernel_spectral_trace
