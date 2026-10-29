import DGRHS.Decoupling.HeterogeneousProduct
/-!
Records-only, uncompiled Lean candidate: coordinatewise swapping of the two
replicas under a heterogeneous finite product law. This is the source-faithful
analogue of `DGRHS.Decoupling.swapSelected_measurePreserving`; the marginal
may depend on the sample-coordinate index.
-/

noncomputable section
open MeasureTheory

namespace DGRHS.Decoupling.Heterogeneous

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
variable (μ : ι → Measure S) [∀ i, IsProbabilityMeasure (μ i)]

/-- Swap the two replicas at precisely the coordinates selected by `s`. -/
def heterogeneousSwapSelected (s : ι → Bool) (z : ι → S × S) : ι → S × S :=
  fun i => if s i then z i else (z i).swap

/-- Every fixed coordinatewise replica swap preserves the heterogeneous
product law `∏ i, (μ i × μ i)`. No equality between the coordinate marginals
is assumed. -/
theorem heterogeneousSwapSelected_measurePreserving (s : ι → Bool) :
    MeasurePreserving (heterogeneousSwapSelected s)
      (heterogeneousPairSamples μ) (heterogeneousPairSamples μ) := by
  unfold heterogeneousSwapSelected heterogeneousPairSamples
  apply measurePreserving_pi
    (fun i : ι => (μ i).prod (μ i))
    (fun i : ι => (μ i).prod (μ i))
    (f := fun i z => if s i then z else z.swap)
  intro i
  cases hs : s i
  · simpa only [hs, Bool.false_eq_true, ↓reduceIte] using
      (Measure.measurePreserving_swap (μ := μ i) (ν := μ i))
  · convert MeasurePreserving.id ((μ i).prod (μ i)) using 1
    ext z <;> simp [hs]

end DGRHS.Decoupling.Heterogeneous

#check @DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected_measurePreserving
#print axioms DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected_measurePreserving
