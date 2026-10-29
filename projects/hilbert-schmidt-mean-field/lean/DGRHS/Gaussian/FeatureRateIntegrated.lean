import DGRHS.Gaussian.FeatureRatePower
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def featureCenteredPowerError (μ : Measure X) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℂ :=
  featureOscillatoryFactor μ β k g N ω ^ N - (Real.exp (featureRateB μ β k g ω) : ℝ) -
    Complex.I * (Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω /
      Real.sqrt (N : ℝ) : ℝ)

lemma integrable_featureRateB_exponential (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) :
    Integrable (fun ω => Real.exp (featureRateB μ β k g ω)) IsonormalProcess.iidStdGaussian := by
  have hB : StronglyMeasurable (featureRateB μ β k g) := by
    unfold featureRateB
    exact (stronglyMeasurable_const.sub (hg.pow 2).integral_prod_left').const_mul _
  apply (integrable_const (featureExponentialFactor μ β k)).mono'
    (Real.continuous_exp.comp_stronglyMeasurable hB).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_featureRateB_le_fullFactor β hβ k hk hM g ω

lemma integrable_featureCenteredPowerError
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (N : ℕ) (hN : 1 ≤ N) :
    Integrable (featureCenteredPowerError μ β k g N) IsonormalProcess.iidStdGaussian := by
  have hA := integrable_featureOscillatoryFactor_pow β hβ k hk hM g hg N hN
  have hB : Integrable (fun ω => (Real.exp (featureRateB μ β k g ω) : ℂ)) IsonormalProcess.iidStdGaussian := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp
      (integrable_featureRateB_exponential β hβ k hk hM g hg)
  have hR := (integrable_featureRate_weighted_cubic_of_exponential_moment b f hf β hβ k hk hM g hg hW).div_const
    (Real.sqrt (N : ℝ))
  have hRc : Integrable (fun ω => ((Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω /
      Real.sqrt (N : ℝ) : ℝ) : ℂ)) IsonormalProcess.iidStdGaussian := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hR
  exact (hA.sub hB).sub (hRc.const_mul Complex.I)

lemma ae_norm_featureCenteredPowerError_le
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      ‖featureCenteredPowerError μ β k g N ω‖ ≤
        featureExponentialFactor μ β k / (N : ℝ) * (‖featureRateRemainder μ β k g N ω‖ +
          6 * featureRateB μ β k g ω ^ 2 + 9 * featureRateR μ β k g ω ^ 2) := by
  filter_upwards [ae_featureOscillatoryFactor_expansion b f hf β hβ k hk hM hmean g hg hW N hN] with ω hω
  exact feature_rate_norm_power_centered_bound _ _ _ _ _ _
    (one_le_featurePositiveFactor β hβ k hk hM N hN) (norm_featureOscillatoryFactor_le β k g N ω)
    N hN (featurePositiveFactor_pow_le β hβ k hk hM N hN)
    (exp_featureRateB_div_le_positiveFactor β hβ k hk hM g N hN ω)
    (exp_featureRateB_le_fullFactor β hβ k hk hM g ω) hω

lemma integral_norm_featureCenteredPowerError_le
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (N : ℕ) (hN : 1 ≤ N) :
    (∫ ω, ‖featureCenteredPowerError μ β k g N ω‖ ∂IsonormalProcess.iidStdGaussian) ≤
      (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  let M := ∫ x, featureExponentialMomentWeight β k x ∂μ
  let A := featureExponentialFactor μ β k
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hA0 : 0 ≤ A := by
    apply integral_nonneg
    intro x
    exact (Real.exp_pos _).le
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_integral_featureExponentialMomentWeight β hβ k hM)
  have hE := (integrable_featureRateRemainder b f hf β hβ k hk hM g hg hW N hN).norm
  have hg2 := memLp_featureGaussian_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hB := integrable_featureRateB_sq_of_exponential_moment b f hf β hβ k hk hM g hg hg2 hW
  have hR := integrable_featureRateR_sq_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hSum : Integrable (fun ω => ‖featureRateRemainder μ β k g N ω‖ +
      6 * featureRateB μ β k g ω ^ 2 + 9 * featureRateR μ β k g ω ^ 2) IsonormalProcess.iidStdGaussian :=
    (hE.add (hB.const_mul 6)).add (hR.const_mul 9)
  have ha := integral_add (hE.add (hB.const_mul 6)) (hR.const_mul 9)
  have hb := integral_add hE (hB.const_mul 6)
  dsimp only [Pi.add_apply] at ha hb
  calc
    _ ≤ ∫ ω, A / (N : ℝ) * (‖featureRateRemainder μ β k g N ω‖ +
        6 * featureRateB μ β k g ω ^ 2 + 9 * featureRateR μ β k g ω ^ 2)
        ∂IsonormalProcess.iidStdGaussian :=
      integral_mono_ae (integrable_featureCenteredPowerError b f hf β hβ k hk hM g hg hW N hN).norm
        (hSum.const_mul _) (ae_norm_featureCenteredPowerError_le b f hf β hβ k hk hM hmean g hg hW N hN)
    _ = A / (N : ℝ) * ((∫ ω, ‖featureRateRemainder μ β k g N ω‖ ∂IsonormalProcess.iidStdGaussian) +
        6 * (∫ ω, featureRateB μ β k g ω ^ 2 ∂IsonormalProcess.iidStdGaussian) +
        9 * (∫ ω, featureRateR μ β k g ω ^ 2 ∂IsonormalProcess.iidStdGaussian)) := by
      rw [integral_const_mul, ha, hb, integral_const_mul, integral_const_mul]
    _ ≤ A / (N : ℝ) * (14 * β ^ 2 * M + 6 * (2 * β ^ 2 * M) + 9 * ((4 / 3 : ℝ) * β ^ 3 * M)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hA0 hNp.le)
      exact add_le_add (add_le_add (integral_norm_featureRateRemainder_le b f hf β hβ k hk hM g hg hW N hN)
        (mul_le_mul_of_nonneg_left (integral_featureRateB_sq_le_of_exponential_moment b f hf β hβ k hk hM g hg hg2 hW) (by norm_num)))
        (mul_le_mul_of_nonneg_left (integral_featureRateR_sq_le_of_exponential_moment b f hf β hβ k hk hM g hg hW) (by norm_num))
    _ = (26 * β ^ 2 + 12 * β ^ 3) * A * M / (N : ℝ) := by ring
    _ ≤ _ := by
      have hAM : A ≤ M := featureExponentialFactor_le_moment β k hk hM
      change _ ≤ (26 * β ^ 2 + 12 * β ^ 3) * M ^ 2 / (N : ℝ)
      rw [pow_two]
      apply div_le_div_of_nonneg_right _ hNp.le
      simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAM (show 0 ≤ 26 * β ^ 2 + 12 * β ^ 3 by positivity)) hM0

lemma integral_featureCenteredPowerError
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (N : ℕ) (hN : 1 ≤ N) :
    (∫ ω, featureCenteredPowerError μ β k g N ω ∂IsonormalProcess.iidStdGaussian) =
      (∫ ω, featureOscillatoryFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian) -
      (∫ ω, Real.exp (featureRateB μ β k g ω) ∂IsonormalProcess.iidStdGaussian : ℝ) := by
  have hA := integrable_featureOscillatoryFactor_pow β hβ k hk hM g hg N hN
  have hB : Integrable (fun ω => (Real.exp (featureRateB μ β k g ω) : ℂ)) IsonormalProcess.iidStdGaussian := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp
      (integrable_featureRateB_exponential β hβ k hk hM g hg)
  have hDiff : Integrable (fun ω => featureOscillatoryFactor μ β k g N ω ^ N -
      (Real.exp (featureRateB μ β k g ω) : ℂ)) IsonormalProcess.iidStdGaussian := hA.sub hB
  have hR := (integrable_featureRate_weighted_cubic_of_exponential_moment b f hf β hβ k hk hM g hg hW).div_const
    (Real.sqrt (N : ℝ))
  have hRc : Integrable (fun ω => ((Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω /
      Real.sqrt (N : ℝ) : ℝ) : ℂ)) IsonormalProcess.iidStdGaussian := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hR
  have hzero : (∫ ω, Complex.I * ((Real.exp (featureRateB μ β k g ω) * featureRateR μ β k g ω /
      Real.sqrt (N : ℝ) : ℝ) : ℂ) ∂IsonormalProcess.iidStdGaussian) = 0 := by
    rw [integral_const_mul, integral_complex_ofReal]
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, integral_featureRate_weighted_cubic_zero_of_exponential_moment b f hf β hβ k hk hM g hg hW]
    simp
  unfold featureCenteredPowerError
  rw [integral_sub hDiff (hRc.const_mul Complex.I), integral_sub hA hB, hzero, sub_zero,
    integral_complex_ofReal]

lemma norm_integral_featureOscillatoryFactor_pow_sub_laplace_le
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(∫ ω, featureOscillatoryFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian) -
      (∫ ω, Real.exp (featureRateB μ β k g ω) ∂IsonormalProcess.iidStdGaussian : ℝ)‖ ≤
      (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  rw [← integral_featureCenteredPowerError b f hf β hβ k hk hM g hg hW N hN]
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_featureCenteredPowerError_le b f hf β hβ k hk hM hmean g hg hW N hN)

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureCenteredPowerError
#print axioms DGRHS.Gaussian.featureCenteredPowerError

#check DGRHS.Gaussian.integrable_featureRateB_exponential
#print axioms DGRHS.Gaussian.integrable_featureRateB_exponential

#check DGRHS.Gaussian.integrable_featureCenteredPowerError
#print axioms DGRHS.Gaussian.integrable_featureCenteredPowerError

#check DGRHS.Gaussian.ae_norm_featureCenteredPowerError_le
#print axioms DGRHS.Gaussian.ae_norm_featureCenteredPowerError_le

#check DGRHS.Gaussian.integral_norm_featureCenteredPowerError_le
#print axioms DGRHS.Gaussian.integral_norm_featureCenteredPowerError_le

#check DGRHS.Gaussian.integral_featureCenteredPowerError
#print axioms DGRHS.Gaussian.integral_featureCenteredPowerError

#check DGRHS.Gaussian.norm_integral_featureOscillatoryFactor_pow_sub_laplace_le
#print axioms DGRHS.Gaussian.norm_integral_featureOscillatoryFactor_pow_sub_laplace_le
