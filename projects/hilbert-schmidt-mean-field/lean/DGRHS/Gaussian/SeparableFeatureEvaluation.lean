import DGRHS.Gaussian.FeatureCentering
import DGRHS.Gaussian.IndexedGaussianTuple

/-!
The Gaussian feature prerequisites under the manuscript's actual abstract
Hilbert-space hypotheses. A genuine Hilbert basis is obtained from Mathlib;
separability proves its index countable. Finite and zero dimensions are included.
No standard Gaussian measure on the Hilbert space is introduced.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology InnerProductSpace

namespace DGRHS.Gaussian

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- Joint Gaussian evaluation of an actual centered square-integrable feature.
All exceptional sets are stated explicitly. -/
theorem exists_separable_centered_featureGaussian_representative
    {k : X → H} (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ)
    (hmean : (∫ x, k x ∂μ) = 0) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ, IsonormalProcess.iidStdGaussian.map (fun ω => g (x, ω)) =
        gaussianReal 0 (Real.toNNReal (‖k x‖ ^ 2))) ∧
      (∀ᵐ x ∂μ, (∫ ω, g (x, ω) ∂IsonormalProcess.iidStdGaussian) = 0) ∧
      (∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (∫ ω, g (x, ω) * g (y, ω) ∂IsonormalProcess.iidStdGaussian) =
        inner ℝ (k x) (k y)) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x, ω)) μ) ∧
      ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x, ω) ∂μ) = 0 := by
  classical
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℝ H
  letI : Countable s := HilbertBasis.countable_of_separable_index b
  let f : s ↪ ℕ := countableGaussianIndex
  obtain ⟨g, hg, hg2, hW, hG, hI, hC⟩ :=
    exists_centered_featureGaussian_representative b f f.injective hk.measurable hk2 hmean
  exact ⟨g, hg, hg2, hG, ae_featureGaussian_sample_mean_zero b f f.injective k g hW,
    ae_featureGaussian_covariance b f f.injective k g hW, hI, hC⟩

/-- The manuscript's weighted fourth moment directly supplies the feature-L2
hypothesis for the constructed evaluation. -/
theorem exists_separable_centered_featureGaussian_of_exponential_moment
    {k : X → H} (hk : StronglyMeasurable k) {β : ℝ} (hβ : 0 ≤ β)
    (hM : Integrable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) *
      (1 + (‖k x‖ ^ 2) ^ 4)) μ) (hmean : (∫ x, k x ∂μ) = 0) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ, IsonormalProcess.iidStdGaussian.map (fun ω => g (x, ω)) =
        gaussianReal 0 (Real.toNNReal (‖k x‖ ^ 2))) ∧
      (∀ᵐ x ∂μ, (∫ ω, g (x, ω) ∂IsonormalProcess.iidStdGaussian) = 0) ∧
      (∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (∫ ω, g (x, ω) * g (y, ω) ∂IsonormalProcess.iidStdGaussian) =
        inner ℝ (k x) (k y)) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x, ω)) μ) ∧
      ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x, ω) ∂μ) = 0 :=
  exists_separable_centered_featureGaussian_representative hk
    (memLp_feature_of_exponential_fourth_moment hk hβ hM) hmean

end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.exists_separable_centered_featureGaussian_representative
#print axioms DGRHS.Gaussian.exists_separable_centered_featureGaussian_of_exponential_moment
#check DGRHS.Gaussian.exists_separable_centered_featureGaussian_representative
#check DGRHS.Gaussian.exists_separable_centered_featureGaussian_of_exponential_moment
