/- Positive quadratic forms are closed under actual operator convergence.
The quantitative physical cutoff estimates must supply that convergence. -/
import DGRHS.Kernel.Operator
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.Kernel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem nonnegative_operator_of_tendsto (T : H →L[ℝ] H) (A : ℕ → H →L[ℝ] H)
    (hA : Tendsto A atTop (𝓝 T))
    (hp : ∀ N v, 0 ≤ inner ℝ v (A N v)) :
    ∀ v, 0 ≤ inner ℝ v (T v) := by
  intro v
  have hc : Continuous (fun B : H →L[ℝ] H => inner ℝ v (B v)) := by fun_prop
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ((hc.tendsto T).comp hA)
    (Eventually.of_forall (fun N => hp N v))

theorem integralOperator_nonnegative_of_toLp_limit {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (a : ℕ → S × S → ℝ)
    (ha : ∀ N, MemLp (a N) 2 (μ.prod μ))
    (hc : Tendsto (fun N => (ha N).toLp (a N)) atTop (𝓝 (hh.toLp h)))
    (hp : ∀ N v, 0 ≤ inner ℝ v (integralOperator (a N) (ha N) v)) :
    ∀ v, 0 ≤ inner ℝ v (integralOperator h hh v) := by
  apply nonnegative_operator_of_tendsto _ _ _ hp
  exact (Operator.l2KernelOp.continuous.tendsto (hh.toLp h)).comp hc
end DGRHS.Kernel
#print axioms DGRHS.Kernel.nonnegative_operator_of_tendsto
#print axioms DGRHS.Kernel.integralOperator_nonnegative_of_toLp_limit
#check @DGRHS.Kernel.nonnegative_operator_of_tendsto
