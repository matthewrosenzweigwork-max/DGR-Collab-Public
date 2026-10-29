/- UNCHECKED outside proof. SAME-field parity; final use must derive integrability
of the actual weighted cubic from M_beta, not assume it at the rate endpoint. -/
import DGRHS.Gaussian.FeatureReflection
import DGRHS.Gaussian.FeatureQuadraticLaplace
open MeasureTheory ProbabilityTheory
namespace DGRHS.Gaussian
noncomputable section

def featureRateB {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    (μ : Measure X) (β : ℝ) (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) : ℝ :=
  β / 2 * ((∫ x, ‖k x‖ ^ 2 ∂μ) - ∫ x, g (x,ω) ^ 2 ∂μ)

def featureRateR {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    (μ : Measure X) (β : ℝ) (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) : ℝ :=
  β * Real.sqrt β * ∫ x, ‖k x‖ ^ 2 * g (x,ω) / 2 - g (x,ω) ^ 3 / 6 ∂μ

variable {ι H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma ae_featureRateB_reflection (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      featureRateB μ β k g (gaussianReflection ω) = featureRateB μ β k g ω := by
  filter_upwards [ae_featureGaussian_reflection_sections b f hf k g hg hW] with ω hω
  unfold featureRateB
  congr 2
  apply integral_congr_ae
  filter_upwards [hω] with x hx
  rw [hx, neg_sq]

lemma ae_featureRateR_reflection (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      featureRateR μ β k g (gaussianReflection ω) = -featureRateR μ β k g ω := by
  filter_upwards [ae_featureGaussian_reflection_sections b f hf k g hg hW] with ω hω
  have hi : (∫ x, ‖k x‖ ^ 2 * g (x,gaussianReflection ω) / 2 -
      g (x,gaussianReflection ω) ^ 3 / 6 ∂μ) =
      -(∫ x, ‖k x‖ ^ 2 * g (x,ω) / 2 - g (x,ω) ^ 3 / 6 ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hω] with x hx
    rw [hx]
    ring
  unfold featureRateR
  rw [hi]
  ring

lemma integral_featureRate_weighted_cubic_zero (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (hi : Integrable (fun ω => Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω)
      IsonormalProcess.iidStdGaussian) :
    (∫ ω, Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω
      ∂IsonormalProcess.iidStdGaussian) = 0 := by
  apply integral_zero_of_gaussianReflection_odd _ hi
  filter_upwards [ae_featureRateB_reflection b f hf β k g hg hW,
    ae_featureRateR_reflection b f hf β k g hg hW] with ω hB hR
  rw [hB, hR]
  ring

end
end DGRHS.Gaussian

#check DGRHS.Gaussian.featureRateB
#print axioms DGRHS.Gaussian.featureRateB
#check DGRHS.Gaussian.featureRateR
#print axioms DGRHS.Gaussian.featureRateR
#check DGRHS.Gaussian.ae_featureRateB_reflection
#print axioms DGRHS.Gaussian.ae_featureRateB_reflection
#check DGRHS.Gaussian.ae_featureRateR_reflection
#print axioms DGRHS.Gaussian.ae_featureRateR_reflection
#check DGRHS.Gaussian.integral_featureRate_weighted_cubic_zero
#print axioms DGRHS.Gaussian.integral_featureRate_weighted_cubic_zero
