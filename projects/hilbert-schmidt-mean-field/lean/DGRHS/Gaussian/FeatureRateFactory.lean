import DGRHS.Gaussian.FeatureRatePhysical
import DGRHS.Gaussian.SeparableFeatureEvaluation

/-! The positive feature rate with an actually constructed Gaussian field.
The lower centered representative is selected once, and its exact isometry
witness is used throughout the physical partition-function rate proof. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} {j : Type*}
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace.CountablyGenerated X]

/-- The representative and the physical rate are obtained in one construction;
no Gaussian field, spectral identity, moment bound or limit is assumed. -/
theorem exists_featureParticleInteraction_rate_with_representative [Countable j]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      (∀ᵐ x ∂μ, IsonormalProcess.iidStdGaussian.map (fun ω => g (x, ω)) =
        ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖k x‖ ^ 2))) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x, ω)) μ) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x, ω) ∂μ) = 0) ∧
      ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (memLp_feature_of_exponential_moment β hβ k hk hM)) (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  obtain ⟨g, hg, hg2, hW, hG, hI, hC⟩ :=
    exists_centered_featureGaussian_representative b f hf hk.measurable
      (memLp_feature_of_exponential_moment β hβ k hk hM) hmean
  exact ⟨g, hg, hg2, hW, hG, hI, hC,
    exists_featureParticleInteraction_rate b f hf β hβ k hk hM hmean g hg hW⟩

/-- The positive feature partition-function rate under the actual separable
Hilbert-space hypotheses, including finite and zero dimensional spaces. -/
theorem exists_separable_featureParticleInteraction_rate
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (memLp_feature_of_exponential_moment β hβ k hk hM)) (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  classical
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℝ H
  letI : Countable s := HilbertBasis.countable_of_separable_index b
  let f : s ↪ ℕ := countableGaussianIndex
  obtain ⟨g, hg, hg2, hW, hG, hI, hC, hRate⟩ :=
    exists_featureParticleInteraction_rate_with_representative b f f.injective β hβ k hk hM hmean
  exact hRate

end DGRHS.Gaussian

#check DGRHS.Gaussian.exists_featureParticleInteraction_rate_with_representative
#print axioms DGRHS.Gaussian.exists_featureParticleInteraction_rate_with_representative
#check DGRHS.Gaussian.exists_separable_featureParticleInteraction_rate
#print axioms DGRHS.Gaussian.exists_separable_featureParticleInteraction_rate
