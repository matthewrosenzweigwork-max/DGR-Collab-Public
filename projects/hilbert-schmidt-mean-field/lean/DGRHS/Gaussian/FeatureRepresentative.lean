import DGRHS.Gaussian.IndexedGaussianLaw
import DGRHS.Gaussian.JointRepresentative

/-!
The actual feature readouts instantiate the joint-representative adapter.
The product-limit hypothesis remains explicit: this file does not yet construct
that limit from square integrability of k. The fibers are identified with the
constructed Gaussian-coordinate map, so their covariance is not postulated.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology InnerProductSpace

namespace DGRHS.Gaussian

variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- A real product-L2 limit of the actual truncations gives a joint representative
with the exact centered scalar Gaussian feature laws on a single μ-full set. -/
theorem exists_featureGaussian_representative_of_product_limit
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    {k : X → H} (hk : Measurable k) {ss : ℕ → Finset ι}
    (hss : Tendsto ss atTop atTop)
    (Z : Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hprod : TendstoInMeasure (μ.prod IsonormalProcess.iidStdGaussian)
      (fun n (p : X × (ℕ → ℝ)) => indexedPartialEvaluation b f k (ss n) p.1 p.2)
      atTop (Z : X × (ℕ → ℝ) → ℝ)) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      g =ᵐ[μ.prod IsonormalProcess.iidStdGaussian] (Z : X × (ℕ → ℝ) → ℝ) ∧
      (∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      ∀ᵐ x ∂μ, IsonormalProcess.iidStdGaussian.map (fun ω => g (x, ω)) =
        gaussianReal 0 (Real.toNNReal (‖k x‖ ^ 2)) := by
  obtain ⟨g, hg, hZ, hW⟩ := exists_joint_representative_of_product_limit Z
    (fun n => measurable_indexedPartialEvaluation b f hk (ss n)) hprod
    (fun x => tendstoInMeasure_indexedPartialEvaluation b f hf k x hss)
  refine ⟨g, hg, hZ, hW, ?_⟩
  filter_upwards [hW] with x hx
  exact (Measure.map_congr hx).trans (map_indexedGaussianIsometry_eq_gaussianReal b f hf (k x))

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.exists_featureGaussian_representative_of_product_limit
#check DGRHS.Gaussian.exists_featureGaussian_representative_of_product_limit
