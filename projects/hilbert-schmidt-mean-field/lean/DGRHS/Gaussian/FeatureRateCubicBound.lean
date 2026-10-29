import DGRHS.Gaussian.FeatureRateCubicMoment
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma integral_feature_sixth_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ p, g p ^ 6 ∂μ.prod IsonormalProcess.iidStdGaussian) = 15 * ∫ x, ‖k x‖ ^ 6 ∂μ := by
  rw [integral_prod _ (integrable_feature_sixth_of_exponential_moment b f hf β hβ k hk hM g hg hW),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_feature_second_and_sixth_moments b f hf k g hW] with x hx
  exact hx.2.2

lemma integral_feature_mixed_square_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ p, ‖k p.1‖ ^ 4 * g p ^ 2 ∂μ.prod IsonormalProcess.iidStdGaussian) = ∫ x, ‖k x‖ ^ 6 ∂μ := by
  rw [integral_prod _ (integrable_feature_mixed_square_of_exponential_moment b f hf β hβ k hk hM g hg hW)]
  apply integral_congr_ae
  filter_upwards [ae_feature_second_and_sixth_moments b f hf k g hW] with x hx
  rw [integral_const_mul, hx.1.2]
  ring

lemma integral_featureCubicIntegrand_sq_le_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ p, featureCubicIntegrand k g p ^ 2 ∂μ.prod IsonormalProcess.iidStdGaussian) ≤
      (4 / 3 : ℝ) * ∫ x, ‖k x‖ ^ 6 ∂μ := by
  have hr := integrable_featureCubicIntegrand_sq_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hm := integrable_feature_mixed_square_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have h6 := integrable_feature_sixth_of_exponential_moment b f hf β hβ k hk hM g hg hW
  calc
    _ ≤ ∫ p, ‖k p.1‖ ^ 4 * g p ^ 2 / 2 + g p ^ 6 / 18
        ∂μ.prod IsonormalProcess.iidStdGaussian :=
      integral_mono hr ((hm.div_const 2).add (h6.div_const 18)) (featureCubicIntegrand_sq_le k g)
    _ = _ := by
      rw [integral_add (hm.div_const 2) (h6.div_const 18)]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_mul_const,
        integral_feature_mixed_square_of_exponential_moment b f hf β hβ k hk hM g hg hW,
        integral_feature_sixth_of_exponential_moment b f hf β hβ k hk hM g hg hW]
      ring

lemma integral_featureRateR_sq_le_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ ω, featureRateR μ β k g ω ^ 2 ∂IsonormalProcess.iidStdGaussian) ≤
      (4 / 3 : ℝ) * β ^ 3 * ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  have hr := memLp_featureCubicIntegrand_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hri := hr.integrable (by norm_num)
  have hR := integrable_featureRateR_sq_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hs : (β * Real.sqrt β) ^ 2 = β ^ 3 := by rw [mul_pow, Real.sq_sqrt hβ]; ring
  calc
    _ ≤ ∫ ω, β ^ 3 * ∫ x, featureCubicIntegrand k g (x,ω) ^ 2 ∂μ
        ∂IsonormalProcess.iidStdGaussian := by
      apply integral_mono_ae hR (hr.integrable_sq.integral_prod_right.const_mul (β ^ 3))
      filter_upwards [hri.prod_left_ae, hr.integrable_sq.prod_left_ae] with ω hω hω2
      change (β * Real.sqrt β * ∫ x, featureCubicIntegrand k g (x,ω) ∂μ) ^ 2 ≤ _
      rw [mul_pow, hs]
      exact mul_le_mul_of_nonneg_left (integral_sq_mean_le _ hω hω2) (pow_nonneg hβ 3)
    _ = β ^ 3 * ∫ p, featureCubicIntegrand k g p ^ 2 ∂μ.prod IsonormalProcess.iidStdGaussian := by
      rw [integral_const_mul, ← integral_prod_symm _ hr.integrable_sq]
    _ ≤ β ^ 3 * ((4 / 3 : ℝ) * ∫ x, ‖k x‖ ^ 6 ∂μ) :=
      mul_le_mul_of_nonneg_left
        (integral_featureCubicIntegrand_sq_le_of_exponential_moment b f hf β hβ k hk hM g hg hW)
        (pow_nonneg hβ 3)
    _ ≤ _ := by
      have hm := integral_feature_moment_power_le β hβ k hk hM 3 (by norm_num)
      simp only [← pow_mul] at hm
      have hb := mul_le_mul_of_nonneg_left hm (show 0 ≤ (4 / 3 : ℝ) * β ^ 3 by positivity)
      nlinarith

lemma exp_featureRateB_le (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) :
    Real.exp (featureRateB μ β k g ω) ≤ Real.exp (β * (∫ x, ‖k x‖ ^ 2 ∂μ) / 2) := by
  apply Real.exp_le_exp.mpr
  have hQ : 0 ≤ ∫ x, g (x,ω) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hm := mul_nonneg hβ hQ
  unfold featureRateB
  nlinarith

lemma integrable_featureRate_weighted_cubic_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun ω => Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω)
      IsonormalProcess.iidStdGaussian := by
  have hR : StronglyMeasurable (featureRateR μ β k g) :=
    (stronglyMeasurable_featureCubicIntegrand k hk g hg).integral_prod_left'.const_mul _
  have hB : StronglyMeasurable (featureRateB μ β k g) := by
    unfold featureRateB
    exact (stronglyMeasurable_const.sub (hg.pow 2).integral_prod_left').const_mul _
  have hr := (memLp_two_iff_integrable_sq hR.aestronglyMeasurable).2
    (integrable_featureRateR_sq_of_exponential_moment b f hf β hβ k hk hM g hg hW)
  have hi := hr.integrable (by norm_num)
  apply (hi.norm.const_mul (Real.exp (β * (∫ x, ‖k x‖ ^ 2 ∂μ) / 2))).mono' (by fun_prop)
  filter_upwards [] with ω
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (exp_featureRateB_le β hβ k g ω) (norm_nonneg _)

lemma integral_featureRate_weighted_cubic_zero_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ ω, Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω
      ∂IsonormalProcess.iidStdGaussian) = 0 :=
  integral_featureRate_weighted_cubic_zero b f hf β k g hg hW
    (integrable_featureRate_weighted_cubic_of_exponential_moment b f hf β hβ k hk hM g hg hW)

end DGRHS.Gaussian

#check DGRHS.Gaussian.integral_feature_sixth_of_exponential_moment
#print axioms DGRHS.Gaussian.integral_feature_sixth_of_exponential_moment
#check DGRHS.Gaussian.integral_feature_mixed_square_of_exponential_moment
#print axioms DGRHS.Gaussian.integral_feature_mixed_square_of_exponential_moment
#check DGRHS.Gaussian.integral_featureCubicIntegrand_sq_le_of_exponential_moment
#print axioms DGRHS.Gaussian.integral_featureCubicIntegrand_sq_le_of_exponential_moment
#check DGRHS.Gaussian.integral_featureRateR_sq_le_of_exponential_moment
#print axioms DGRHS.Gaussian.integral_featureRateR_sq_le_of_exponential_moment
#check DGRHS.Gaussian.exp_featureRateB_le
#print axioms DGRHS.Gaussian.exp_featureRateB_le
#check DGRHS.Gaussian.integrable_featureRate_weighted_cubic_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_featureRate_weighted_cubic_of_exponential_moment
#check DGRHS.Gaussian.integral_featureRate_weighted_cubic_zero_of_exponential_moment
#print axioms DGRHS.Gaussian.integral_featureRate_weighted_cubic_zero_of_exponential_moment
