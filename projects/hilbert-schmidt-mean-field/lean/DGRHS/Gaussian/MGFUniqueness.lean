/- Pinned Mathlib complex-MGF uniqueness, applied on the full real integrability
set. This helper does not posit a Gaussian law from a totalized MGF alone. -/
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Distributions.Gaussian.Real
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace DGRHS.Gaussian
variable {S : Type*} [MeasurableSpace S]

lemma map_eq_gaussianReal_of_all_real_mgf (μ : Measure S) [IsProbabilityMeasure μ]
    (X : S → ℝ) (hm : AEMeasurable X μ) (q : ℝ) (hq : 0 ≤ q)
    (hi : ∀ t : ℝ, Integrable (fun x => Real.exp (t*X x)) μ)
    (he : ∀ t : ℝ, mgf X μ t = Real.exp (q*t^2/2)) :
    μ.map X = gaussianReal 0 (Real.toNNReal q) := by
  have hmgf : mgf X μ = mgf id (gaussianReal 0 (Real.toNNReal q)) := by
    funext t
    rw [mgf_id_gaussianReal, he t]
    simp only [Real.coe_toNNReal q hq, zero_mul, zero_add]
  have hset : integrableExpSet X μ = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hi t
  have hc := eqOn_complexMGF_of_mgf hmgf
  have hfun : complexMGF X μ = complexMGF id (gaussianReal 0 (Real.toNNReal q)) := by
    funext z
    apply hc
    simp [hset]
  simpa using Measure.ext_of_complexMGF_eq hm aemeasurable_id hfun
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.map_eq_gaussianReal_of_all_real_mgf
#check @DGRHS.Gaussian.map_eq_gaussianReal_of_all_real_mgf
