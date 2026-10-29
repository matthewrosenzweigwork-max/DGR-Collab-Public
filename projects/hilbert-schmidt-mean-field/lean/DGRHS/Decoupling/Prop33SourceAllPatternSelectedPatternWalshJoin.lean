import DGRHS.Decoupling.Prop33MixedPatternConditionalPrefix
import DGRHS.Decoupling.Prop33FixedTupleSelectorExpansion
import DGRHS.Decoupling.Prop33OrderedTupleMaskCoefficientAggregation
import DGRHS.Decoupling.Prop33AllPatternSwapInvariant
import DGRHS.Decoupling.Prop33HeterogeneousPairSwap

/-!
Checked (AWS development build, P10; one repaired step in
`selected_pattern_eq_source_swapped_argument`). It is rebased on the current checked
Prop. 3.3 ordered-tuple alias and the checked tuple-faithful coefficient
aggregation. It uses the cleaned 573 API and corrected 0a94 pointwise swap
API. Those candidates still require their own registered checks and ROOT
integration before this module is submitted. It proves only a pointwise
finite-cube source expansion and the c6 event bound; it includes no
probability-space event or Tonelli step.
-/

noncomputable section
open DGRHS.Decoupling.FiniteCube

namespace DGRHS.Decoupling.Prop33.SourceAllPatternSelectedPatternWalshJoin

abbrev OrderedTuple (n k : ℕ) :=
  DGRHS.Decoupling.Prop33.OrderedTuple n k

/-- The tuple-dependent source kernel evaluated on the two-copy slot pattern. -/
def sourceKernelSelectorValues {S E : Type*} {n k : ℕ}
    [AddCommMonoid E] [Module ℝ E]
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) : OrderedTuple n k → Cube k → E :=
  fun t j =>
    f t (DGRHS.Decoupling.Prop33.CopySwap.sourcePatternArgument z t j)

/-- The selector label from the fixed-tuple identity is exactly the copy label
seen after the `true = keep`, `false = swap` coordinatewise pair map. -/
theorem selected_pattern_eq_source_swapped_argument
    {S E : Type*} {n k : ℕ}
    [AddCommMonoid E] [Module ℝ E]
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (σ : Cube n) (ell : Cube k)
    (t : OrderedTuple n k) :
    sourceKernelSelectorValues f z t
        (fun q =>
          DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectedLabel
            σ ell t q) =
      f t (DGRHS.Decoupling.Prop33.CopySwap.sourcePatternArgument
        (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected σ z) t ell) := by
  apply congrArg (f t)
  exact (DGRHS.Decoupling.Prop33.CopySwap.sourcePatternArgument_swap_eq_relabel
      σ z t ell).symm

/-- Summing the selected kernel values over ordered tuples gives the source
copy-pattern statistic at the swapped pair array. -/
theorem selected_pattern_sum_eq_swapped_copy_pattern
    {S E : Type*} {n k : ℕ}
    [AddCommMonoid E] [Module ℝ E]
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (σ : Cube n) (ell : Cube k) :
    (∑ t : OrderedTuple n k,
      sourceKernelSelectorValues f z t
        (fun q =>
          DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectedLabel
            σ ell t q)) =
      DGRHS.Decoupling.Prop33.CopySwap.sourceCopyPatternStatistic f
        (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected σ z) ell := by
  unfold DGRHS.Decoupling.Prop33.CopySwap.sourceCopyPatternStatistic
  apply Finset.sum_congr rfl
  intro t ht
  exact selected_pattern_eq_source_swapped_argument f z σ ell t

/-- The all-copy-pattern constant in the fixed-tuple expansion is exactly the
source all-pattern statistic `T(z)`. -/
theorem source_kernel_constant_eq_all_pattern
    {S E : Type*} {n k : ℕ}
    [AddCommMonoid E] [Module ℝ E]
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) :
    (∑ t : OrderedTuple n k, ∑ j : Cube k,
      sourceKernelSelectorValues f z t j) =
      DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic f z := by
  classical
  unfold sourceKernelSelectorValues
    DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic
    DGRHS.Decoupling.Prop33.CopySwap.sourceCopyPatternStatistic
  rw [Finset.sum_comm]

/-- Pointwise source expansion: scaling the selected source copy-pattern sum by
`2^k` gives `T(z)` plus a Walsh polynomial supported in degrees `1,…,k`.
The following scalarization theorem records its mean-zero property. The
coefficient map retains the full ordered-tuple dependence. -/
theorem source_copy_pattern_selector_expansion
    {S E : Type*} {n k : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (σ : Cube n) (ell : Cube k) :
    (2 : ℝ)^k •
        DGRHS.Decoupling.Prop33.CopySwap.sourceCopyPatternStatistic f
          (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected σ z) ell =
      DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic f z +
        sourceBanachWalshPolynomial
          (DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient
            ell (sourceKernelSelectorValues f z)) σ := by
  calc
    _ = (2 : ℝ)^k •
        (∑ t : OrderedTuple n k,
          sourceKernelSelectorValues f z t
            (fun q =>
              DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectedLabel
                σ ell t q)) := by
      congr 1
      exact (selected_pattern_sum_eq_swapped_copy_pattern f z σ ell).symm
    _ = (∑ t : OrderedTuple n k, ∑ j : Cube k,
          sourceKernelSelectorValues f z t j) +
        sourceBanachWalshPolynomial
          (DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient
            ell (sourceKernelSelectorValues f z)) σ :=
      DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.summed_fixed_tuple_selector_identity
        ell (sourceKernelSelectorValues f z) σ
    _ = _ := by rw [source_kernel_constant_eq_all_pattern]

/-- The all-pattern constant is invariant under the coordinatewise pair map.
This is the finite relabeling identity from the 573 source-map candidate. -/
theorem source_all_pattern_constant_swap_invariant
    {S E : Type*} {n k : ℕ}
    [AddCommMonoid E]
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (σ : Cube n) :
    DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic f
        (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected σ z) =
      DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic f z := by
  exact DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic_swap_invariant
    f σ z

/-- Every nonzero coefficient of the remainder has Walsh degree in `[1,k]`. -/
theorem source_copy_pattern_remainder_degree_bounds
    {S E : Type*} {n k : ℕ}
    [AddCommMonoid E] [Module ℝ E]
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (ell : Cube k) (s : Cube n)
    (hs : DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient
      ell (sourceKernelSelectorValues f z) s ≠ 0) :
    1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k := by
  exact DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient_degree_bounds
    ell (sourceKernelSelectorValues f z) s hs

/-- Scalarization of the remainder has zero finite-cube mean. Together with the
preceding degree bound, this records the mean-zero Walsh qualification. -/
theorem source_copy_pattern_remainder_scalar_mean_zero
    {S E : Type*} {n k : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hk : 0 < k)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (ell : Cube k)
    (φ : StrongDual ℝ E) :
    cubeAvg (fun σ =>
      φ (sourceBanachWalshPolynomial
        (DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient
          ell (sourceKernelSelectorValues f z)) σ)) = 0 := by
  let v := DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient
    ell (sourceKernelSelectorValues f z)
  let c : Cube n → ℝ := fun s => φ (v s)
  have hc : ∀ s, c s ≠ 0 →
      1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k := by
    intro s hs
    have hv : v s ≠ 0 := by
      intro hz
      apply hs
      simp [c, v, hz]
    exact DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient_degree_bounds
      ell (sourceKernelSelectorValues f z) s hv
  have hmean :=
    (source_scalar_mixed_degree_moments hk c hc).1
  have hpoly :
      (fun σ =>
        φ (sourceBanachWalshPolynomial v σ)) = cubeWalshPolynomial c := by
    funext σ
    exact sourceBanachWalshPolynomial_apply v φ σ
  simpa [v, c, hpoly] using hmean

/-- The source pointwise selector small-ball bound, with exact source cost
`c_k=4*sourceMixedDegreeWeight k`. No probability-space event is formed here. -/
theorem source_copy_pattern_selector_smallball
    {S E : Type*} {n k : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hk : 0 < k)
    (f : OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (ell : Cube k) :
    cubeAvg (fun σ =>
      if ‖(2 : ℝ)^k •
          DGRHS.Decoupling.Prop33.CopySwap.sourceCopyPatternStatistic f
            (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected σ z) ell‖ ≥
        ‖DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic f z‖
      then (1 : ℝ) else 0) ≥
        1 / (4 * sourceMixedDegreeWeight k) := by
  simpa only [source_copy_pattern_selector_expansion] using
    DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregate_translated_cube_norm_event
      hk ell (sourceKernelSelectorValues f z)
      (DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic f z)

#print DGRHS.Decoupling.Prop33.SourceAllPatternSelectedPatternWalshJoin.source_copy_pattern_selector_expansion
#print DGRHS.Decoupling.Prop33.SourceAllPatternSelectedPatternWalshJoin.source_copy_pattern_selector_smallball
#print axioms DGRHS.Decoupling.Prop33.SourceAllPatternSelectedPatternWalshJoin.source_copy_pattern_selector_expansion
#print axioms DGRHS.Decoupling.Prop33.SourceAllPatternSelectedPatternWalshJoin.source_copy_pattern_selector_smallball

end DGRHS.Decoupling.Prop33.SourceAllPatternSelectedPatternWalshJoin
