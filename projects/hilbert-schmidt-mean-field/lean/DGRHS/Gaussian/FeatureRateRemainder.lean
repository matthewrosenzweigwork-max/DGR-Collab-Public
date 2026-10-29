import DGRHS.Gaussian.FeatureRateRemainderEnvelope
import DGRHS.Gaussian.FeatureTaylor
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def featureScalarRemainder (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (t : ℝ) (p : X × (ℕ → ℝ)) : ℂ :=
  Complex.exp (((t ^ 2 * β * ‖k p.1‖ ^ 2 / 2 : ℝ) : ℂ) +
    Complex.I * (t * Real.sqrt β * g p : ℝ)) -
  (cubicExpPolynomial (Complex.I * (t * Real.sqrt β * g p : ℝ)) +
    (t ^ 2 * β * ‖k p.1‖ ^ 2 / 2 : ℝ) *
      (1 + Complex.I * (t * Real.sqrt β * g p : ℝ)))

def featureIntegratedRemainder (μ : Measure X) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (t : ℝ) (ω : ℕ → ℝ) : ℂ :=
  ∫ x, featureScalarRemainder β k g t (x,ω) ∂μ

lemma stronglyMeasurable_featureScalarRemainder (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (t : ℝ) : StronglyMeasurable (featureScalarRemainder β k g t) := by
  let u : X × (ℕ → ℝ) → ℂ := fun p => (t ^ 2 * β * ‖k p.1‖ ^ 2 / 2 : ℝ)
  let z : X × (ℕ → ℝ) → ℂ := fun p => Complex.I * (t * Real.sqrt β * g p : ℝ)
  have hu : StronglyMeasurable u := by
    apply Complex.continuous_ofReal.comp_stronglyMeasurable
    simp only [div_eq_mul_inv]
    exact (((hk.comp_measurable measurable_fst).norm.pow 2).const_mul (t ^ 2 * β)).mul_const _
  have hz : StronglyMeasurable z :=
    (Complex.continuous_ofReal.comp_stronglyMeasurable (hg.const_mul (t * Real.sqrt β))).const_mul _
  have hp : StronglyMeasurable (fun p => cubicExpPolynomial (z p)) := by
    unfold cubicExpPolynomial
    simp only [div_eq_mul_inv]
    exact ((stronglyMeasurable_const.add hz).add ((hz.pow 2).mul_const _)).add ((hz.pow 3).mul_const _)
  change StronglyMeasurable (fun p => Complex.exp (u p + z p) -
    (cubicExpPolynomial (z p) + u p * (1 + z p)))
  exact (Complex.continuous_exp.comp_stronglyMeasurable (hu.add hz)).sub
    (hp.add (hu.mul (stronglyMeasurable_const.add hz)))

lemma norm_featureScalarRemainder_le (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (p : X × (ℕ → ℝ)) :
    ‖featureScalarRemainder β k g t p‖ ≤ t ^ 4 * β ^ 2 * featureRemainderEnvelope β k g p := by
  have hi := norm_feature_scalar_remainder β (‖k p.1‖ ^ 2) t (g p) hβ (sq_nonneg _) ht0 ht1
  unfold featureScalarRemainder featureRemainderEnvelope
  convert hi using 1 <;> ring

lemma integrable_featureScalarRemainder
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (featureScalarRemainder β k g t) (μ.prod IsonormalProcess.iidStdGaussian) := by
  apply ((integrable_featureRemainderEnvelope b f hf β k hk hM g hg hW).const_mul
    (t ^ 4 * β ^ 2)).mono' (stronglyMeasurable_featureScalarRemainder β k hk g hg t).aestronglyMeasurable
  filter_upwards [] with p
  exact norm_featureScalarRemainder_le β hβ k g t ht0 ht1 p

lemma integral_norm_featureScalarRemainder_le
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ p, ‖featureScalarRemainder β k g t p‖ ∂μ.prod IsonormalProcess.iidStdGaussian) ≤
      14 * t ^ 4 * β ^ 2 * ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  have hr := integrable_featureScalarRemainder b f hf β hβ k hk hM g hg hW t ht0 ht1
  have he := integrable_featureRemainderEnvelope b f hf β k hk hM g hg hW
  calc
    _ ≤ ∫ p, t ^ 4 * β ^ 2 * featureRemainderEnvelope β k g p
        ∂μ.prod IsonormalProcess.iidStdGaussian :=
      integral_mono hr.norm (he.const_mul _) (norm_featureScalarRemainder_le β hβ k g t ht0 ht1)
    _ = t ^ 4 * β ^ 2 * ∫ p, featureRemainderEnvelope β k g p
        ∂μ.prod IsonormalProcess.iidStdGaussian := integral_const_mul _ _
    _ ≤ t ^ 4 * β ^ 2 * (14 * ∫ x, featureExponentialMomentWeight β k x ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_featureRemainderEnvelope_le_moment b f hf β k hk hM g hg hW)
        (by positivity)
    _ = _ := by ring

lemma stronglyMeasurable_featureIntegratedRemainder (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (t : ℝ) : StronglyMeasurable (featureIntegratedRemainder μ β k g t) :=
  (stronglyMeasurable_featureScalarRemainder β k hk g hg t).integral_prod_left'

lemma integrable_featureIntegratedRemainder
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (featureIntegratedRemainder μ β k g t) IsonormalProcess.iidStdGaussian :=
  (integrable_featureScalarRemainder b f hf β hβ k hk hM g hg hW t ht0 ht1).integral_prod_right

lemma integral_norm_featureIntegratedRemainder_le
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ ω, ‖featureIntegratedRemainder μ β k g t ω‖ ∂IsonormalProcess.iidStdGaussian) ≤
      14 * t ^ 4 * β ^ 2 * ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  have hr := integrable_featureScalarRemainder b f hf β hβ k hk hM g hg hW t ht0 ht1
  calc
    _ ≤ ∫ ω, ∫ x, ‖featureScalarRemainder β k g t (x,ω)‖ ∂μ
        ∂IsonormalProcess.iidStdGaussian :=
      integral_mono hr.integral_prod_right.norm hr.norm.integral_prod_right
        (fun ω => norm_integral_le_integral_norm _)
    _ = ∫ p, ‖featureScalarRemainder β k g t p‖ ∂μ.prod IsonormalProcess.iidStdGaussian :=
      (integral_prod_symm _ hr.norm).symm
    _ ≤ _ := integral_norm_featureScalarRemainder_le b f hf β hβ k hk hM g hg hW t ht0 ht1

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureScalarRemainder
#print axioms DGRHS.Gaussian.featureScalarRemainder

#check DGRHS.Gaussian.featureIntegratedRemainder
#print axioms DGRHS.Gaussian.featureIntegratedRemainder

#check DGRHS.Gaussian.stronglyMeasurable_featureScalarRemainder
#print axioms DGRHS.Gaussian.stronglyMeasurable_featureScalarRemainder

#check DGRHS.Gaussian.norm_featureScalarRemainder_le
#print axioms DGRHS.Gaussian.norm_featureScalarRemainder_le

#check DGRHS.Gaussian.integrable_featureScalarRemainder
#print axioms DGRHS.Gaussian.integrable_featureScalarRemainder

#check DGRHS.Gaussian.integral_norm_featureScalarRemainder_le
#print axioms DGRHS.Gaussian.integral_norm_featureScalarRemainder_le

#check DGRHS.Gaussian.stronglyMeasurable_featureIntegratedRemainder
#print axioms DGRHS.Gaussian.stronglyMeasurable_featureIntegratedRemainder

#check DGRHS.Gaussian.integrable_featureIntegratedRemainder
#print axioms DGRHS.Gaussian.integrable_featureIntegratedRemainder

#check DGRHS.Gaussian.integral_norm_featureIntegratedRemainder_le
#print axioms DGRHS.Gaussian.integral_norm_featureIntegratedRemainder_le
