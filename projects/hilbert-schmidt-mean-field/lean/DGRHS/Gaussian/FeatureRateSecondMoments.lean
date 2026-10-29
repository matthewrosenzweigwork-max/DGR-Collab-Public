import DGRHS.Gaussian.FeatureRateMoments
import DGRHS.Gaussian.FeatureRateEnvelope
import DGRHS.Gaussian.FeatureRateParity

/- Actual spatial fourth-moment/Jensen estimates for the SAME field. Every
product/section integrability assertion precedes the square-mean estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma integrable_feature_fourth_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun p => g p ^ 4) (μ.prod IsonormalProcess.iidStdGaussian) := by
  have hi : Integrable (fun x => (1 : ℝ) * ‖k x‖ ^ 4) μ := by
    simpa only [one_mul, ← pow_mul] using
      integrable_feature_moment_power β hβ k hk hM 2 (by norm_num)
  simpa only [one_mul] using integrable_weighted_feature_fourth b f hf k g hg hW
    (fun _ => 1) measurable_const (by intro x; norm_num) hi

lemma integrable_feature_quadratic_sq_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun ω => (∫ x, g (x,ω) ^ 2 ∂μ) ^ 2) IsonormalProcess.iidStdGaussian := by
  have h4 := integrable_feature_fourth_of_exponential_moment b f hf β hβ k hk hM g hg hW
  apply h4.integral_prod_right.mono' ((hg.pow 2).integral_prod_left'.pow 2).aestronglyMeasurable
  filter_upwards [hg2.integrable_sq.prod_left_ae, h4.prod_left_ae] with ω hω2 hω4
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hω4' : Integrable (fun x => (g (x,ω) ^ 2) ^ 2) μ := by
    simpa only [← pow_mul] using hω4
  simpa only [← pow_mul, Pi.pow_apply] using
    integral_sq_mean_le (fun x => g (x,ω) ^ 2) hω2 hω4'

lemma integral_feature_quadratic_sq_le_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ ω, (∫ x, g (x,ω) ^ 2 ∂μ) ^ 2 ∂IsonormalProcess.iidStdGaussian) ≤
      3 * ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  have h4 := integrable_feature_fourth_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hQ := integrable_feature_quadratic_sq_of_exponential_moment b f hf β hβ k hk hM g hg hg2 hW
  have hi : Integrable (fun x => (1 : ℝ) * ‖k x‖ ^ 4) μ := by
    simpa only [one_mul, ← pow_mul] using
      integrable_feature_moment_power β hβ k hk hM 2 (by norm_num)
  calc
    _ ≤ ∫ ω, ∫ x, g (x,ω) ^ 4 ∂μ ∂IsonormalProcess.iidStdGaussian := by
      apply integral_mono_ae hQ h4.integral_prod_right
      filter_upwards [hg2.integrable_sq.prod_left_ae, h4.prod_left_ae] with ω hω2 hω4
      have hω4' : Integrable (fun x => (g (x,ω) ^ 2) ^ 2) μ := by
        simpa only [← pow_mul] using hω4
      simpa only [← pow_mul] using
        integral_sq_mean_le (fun x => g (x,ω) ^ 2) hω2 hω4'
    _ = ∫ p, g p ^ 4 ∂μ.prod IsonormalProcess.iidStdGaussian := (integral_prod_symm _ h4).symm
    _ = 3 * ∫ x, ‖k x‖ ^ 4 ∂μ := by
      simpa only [one_mul] using integral_weighted_feature_fourth b f hf k g hg hW
        (fun _ => 1) measurable_const (by intro x; norm_num) hi
    _ ≤ _ := by
      have hb := integral_feature_moment_power_le β hβ k hk hM 2 (by norm_num)
      simp only [← pow_mul] at hb
      exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma featureRateB_sq_le (β : ℝ) (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) :
    featureRateB μ β k g ω ^ 2 ≤ β ^ 2 / 2 *
      ((∫ x, ‖k x‖ ^ 2 ∂μ) ^ 2 + (∫ x, g (x,ω) ^ 2 ∂μ) ^ 2) := by
  have hs : ((∫ x, ‖k x‖ ^ 2 ∂μ) - ∫ x, g (x,ω) ^ 2 ∂μ) ^ 2 ≤
      2 * (∫ x, ‖k x‖ ^ 2 ∂μ) ^ 2 + 2 * (∫ x, g (x,ω) ^ 2 ∂μ) ^ 2 := by
    nlinarith [sq_nonneg ((∫ x, ‖k x‖ ^ 2 ∂μ) + ∫ x, g (x,ω) ^ 2 ∂μ)]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (β / 2))
  unfold featureRateB
  convert hm using 1 <;> ring

lemma integrable_featureRateB_sq_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun ω => featureRateB μ β k g ω ^ 2) IsonormalProcess.iidStdGaussian := by
  have hQ := integrable_feature_quadratic_sq_of_exponential_moment b f hf β hβ k hk hM g hg hg2 hW
  have hB : StronglyMeasurable (featureRateB μ β k g) := by
    unfold featureRateB
    exact (stronglyMeasurable_const.sub (hg.pow 2).integral_prod_left').const_mul (β / 2)
  apply (((integrable_const ((∫ x, ‖k x‖ ^ 2 ∂μ) ^ 2)).add hQ).const_mul (β ^ 2 / 2)).mono'
    (hB.pow 2).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact featureRateB_sq_le β k g ω

lemma integral_featureRateB_sq_le_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ ω, featureRateB μ β k g ω ^ 2 ∂IsonormalProcess.iidStdGaussian) ≤
      2 * β ^ 2 * ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  have hQ := integrable_feature_quadratic_sq_of_exponential_moment b f hf β hβ k hk hM g hg hg2 hW
  have hB := integrable_featureRateB_sq_of_exponential_moment b f hf β hβ k hk hM g hg hg2 hW
  have hd : (∫ x, ‖k x‖ ^ 2 ∂μ) ^ 2 ≤ ∫ x, featureExponentialMomentWeight β k x ∂μ := by
    apply (integral_sq_mean_le _
      (by simpa using integrable_feature_moment_power β hβ k hk hM 1 (by norm_num))
      (integrable_feature_moment_power β hβ k hk hM 2 (by norm_num))).trans
    exact integral_feature_moment_power_le β hβ k hk hM 2 (by norm_num)
  have hq := integral_feature_quadratic_sq_le_of_exponential_moment b f hf β hβ k hk hM g hg hg2 hW
  calc
    _ ≤ ∫ ω, β ^ 2 / 2 * ((∫ x, ‖k x‖ ^ 2 ∂μ) ^ 2 + (∫ x, g (x,ω) ^ 2 ∂μ) ^ 2)
        ∂IsonormalProcess.iidStdGaussian := by
      apply integral_mono hB (((integrable_const _).add hQ).const_mul _)
      exact featureRateB_sq_le β k g
    _ = β ^ 2 / 2 * ((∫ x, ‖k x‖ ^ 2 ∂μ) ^ 2 +
        ∫ ω, (∫ x, g (x,ω) ^ 2 ∂μ) ^ 2 ∂IsonormalProcess.iidStdGaussian) := by
      rw [integral_const_mul, integral_add (integrable_const _) hQ]
      simp
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left (add_le_add hd hq) (show 0 ≤ β ^ 2 / 2 by positivity)
      nlinarith

end DGRHS.Gaussian

#check DGRHS.Gaussian.integrable_feature_fourth_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_feature_fourth_of_exponential_moment
#check DGRHS.Gaussian.integrable_feature_quadratic_sq_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_feature_quadratic_sq_of_exponential_moment
#check DGRHS.Gaussian.integral_feature_quadratic_sq_le_of_exponential_moment
#print axioms DGRHS.Gaussian.integral_feature_quadratic_sq_le_of_exponential_moment
#check DGRHS.Gaussian.featureRateB_sq_le
#print axioms DGRHS.Gaussian.featureRateB_sq_le
#check DGRHS.Gaussian.integrable_featureRateB_sq_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_featureRateB_sq_of_exponential_moment
#check DGRHS.Gaussian.integral_featureRateB_sq_le_of_exponential_moment
#print axioms DGRHS.Gaussian.integral_featureRateB_sq_le_of_exponential_moment
