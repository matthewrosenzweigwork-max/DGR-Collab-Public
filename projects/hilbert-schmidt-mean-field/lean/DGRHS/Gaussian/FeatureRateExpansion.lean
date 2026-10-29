import DGRHS.Gaussian.FeatureRateRemainder
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def featureCubicPolynomial (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (t : ℝ) (p : X × (ℕ → ℝ)) : ℂ :=
  cubicExpPolynomial (Complex.I * (t * Real.sqrt β * g p : ℝ)) +
    (t ^ 2 * β * ‖k p.1‖ ^ 2 / 2 : ℝ) * (1 + Complex.I * (t * Real.sqrt β * g p : ℝ))

lemma featureCubicPolynomial_eq (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (t : ℝ) (p : X × (ℕ → ℝ)) :
    featureCubicPolynomial β k g t p =
      1 + Complex.I * (t * Real.sqrt β * g p : ℝ) +
        (t ^ 2 * β / 2 * (‖k p.1‖ ^ 2 - g p ^ 2) : ℝ) +
        Complex.I * (t ^ 3 * β * Real.sqrt β * featureCubicIntegrand k g p : ℝ) := by
  have hsv : (t * Real.sqrt β * g p) ^ 2 = t ^ 2 * β * g p ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hβ]
  have hz2 : (Complex.I * (t * Real.sqrt β * g p : ℝ)) ^ 2 = -(t ^ 2 * β * g p ^ 2 : ℝ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, neg_one_mul, hsv]
  have hz3 : (Complex.I * (t * Real.sqrt β * g p : ℝ)) ^ 3 =
      -Complex.I * (t ^ 3 * β * Real.sqrt β * g p ^ 3 : ℝ) := by
    rw [pow_succ, hz2]
    push_cast
    ring
  unfold featureCubicPolynomial cubicExpPolynomial featureCubicIntegrand
  rw [hz2, hz3]
  push_cast
  ring

private lemma integrable_rate_complex_ofReal {z : X → ℝ} (hz : Integrable z μ) :
    Integrable (fun x => (z x : ℂ)) μ := by
  simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hz

lemma integrable_featureCubicPolynomial_section (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (t : ℝ) (ω : ℕ → ℝ)
    (hd : Integrable (fun x => ‖k x‖ ^ 2) μ)
    (h1 : Integrable (fun x => g (x,ω)) μ)
    (h2 : Integrable (fun x => g (x,ω) ^ 2) μ)
    (hr : Integrable (fun x => featureCubicIntegrand k g (x,ω)) μ) :
    Integrable (fun x => featureCubicPolynomial β k g t (x,ω)) μ := by
  have hl := (integrable_rate_complex_ofReal (h1.const_mul (t * Real.sqrt β))).const_mul Complex.I
  have hq : Integrable (fun x => (t ^ 2 * β / 2 * (‖k x‖ ^ 2 - g (x,ω) ^ 2) : ℝ) : X → ℂ) μ :=
    integrable_rate_complex_ofReal ((hd.sub h2).const_mul (t ^ 2 * β / 2))
  have hc := (integrable_rate_complex_ofReal (hr.const_mul (t ^ 3 * β * Real.sqrt β))).const_mul Complex.I
  simp_rw [featureCubicPolynomial_eq β hβ]
  exact (((integrable_const (1 : ℂ)).add hl).add hq).add hc

lemma integral_featureCubicPolynomial_of_mean_zero (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (t : ℝ) (ω : ℕ → ℝ)
    (hd : Integrable (fun x => ‖k x‖ ^ 2) μ)
    (h1 : Integrable (fun x => g (x,ω)) μ)
    (h2 : Integrable (fun x => g (x,ω) ^ 2) μ)
    (hr : Integrable (fun x => featureCubicIntegrand k g (x,ω)) μ)
    (hzero : (∫ x, g (x,ω) ∂μ) = 0) :
    (∫ x, featureCubicPolynomial β k g t (x,ω) ∂μ) =
      1 + (t ^ 2 * featureRateB μ β k g ω : ℝ) +
        Complex.I * (t ^ 3 * featureRateR μ β k g ω : ℝ) := by
  have hl := (integrable_rate_complex_ofReal (h1.const_mul (t * Real.sqrt β))).const_mul Complex.I
  have hq : Integrable (fun x => (t ^ 2 * β / 2 * (‖k x‖ ^ 2 - g (x,ω) ^ 2) : ℝ) : X → ℂ) μ :=
    integrable_rate_complex_ofReal ((hd.sub h2).const_mul (t ^ 2 * β / 2))
  have hc := (integrable_rate_complex_ofReal (hr.const_mul (t ^ 3 * β * Real.sqrt β))).const_mul Complex.I
  have ha := integral_add (((integrable_const (1 : ℂ)).add hl).add hq) hc
  have hb := integral_add ((integrable_const (1 : ℂ)).add hl) hq
  have hd' := integral_add (integrable_const (1 : ℂ)) hl
  dsimp only [Pi.add_apply, Pi.sub_apply] at ha hb hd'
  simp_rw [featureCubicPolynomial_eq β hβ]
  rw [ha, hb, hd', integral_const_mul, integral_complex_ofReal, integral_const_mul, hzero]
  rw [integral_complex_ofReal, integral_const_mul, integral_sub hd h2,
    integral_const_mul, integral_complex_ofReal, integral_const_mul]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, Complex.ofReal_zero, mul_zero, add_zero]
  unfold featureRateB featureRateR featureCubicIntegrand
  push_cast
  ring

lemma memLp_featureGaussian_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) := by
  have hd : Integrable (fun x => ‖k x‖ ^ 2) μ := by
    simpa only [pow_one] using integrable_feature_moment_power β hβ k hk hM 1 (by norm_num)
  have h2 := integrable_weighted_feature_second b f hf k g hg hW (fun _ => 1)
    measurable_const (fun _ => by norm_num) (by simpa only [one_mul] using hd)
  apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2
  simpa only [one_mul, Real.norm_eq_abs, sq_abs] using h2

lemma ae_feature_phase_expansion_of_exponential_moment
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      (∫ x, Complex.exp (((t ^ 2 * β * ‖k x‖ ^ 2 / 2 : ℝ) : ℂ) +
        Complex.I * (t * Real.sqrt β * g (x,ω) : ℝ)) ∂μ) =
      1 + (t ^ 2 * featureRateB μ β k g ω : ℝ) +
        Complex.I * (t ^ 3 * featureRateR μ β k g ω : ℝ) +
        featureIntegratedRemainder μ β k g t ω := by
  have hk2 := memLp_feature_of_exponential_moment β hβ k hk hM
  have hg2 := memLp_featureGaussian_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hcenter := ae_feature_spatial_mean_zero_of_same_process b f hf k hk.measurable hk2 hmean g hg hW
  have hri := (memLp_featureCubicIntegrand_of_exponential_moment b f hf β hβ k hk hM g hg hW).integrable (by norm_num)
  have hrem := integrable_featureScalarRemainder b f hf β hβ k hk hM g hg hW t ht0 ht1
  have hd : Integrable (fun x => ‖k x‖ ^ 2) μ := by
    simpa only [pow_one] using integrable_feature_moment_power β hβ k hk hM 1 (by norm_num)
  filter_upwards [hg2.integrable (by norm_num) |>.prod_left_ae,
    hg2.integrable_sq.prod_left_ae, hri.prod_left_ae, hrem.prod_left_ae, hcenter.2] with ω h1 h2 hr hremω hzero
  have hp := integrable_featureCubicPolynomial_section β hβ k g t ω hd h1 h2 hr
  have he : (fun x => Complex.exp (((t ^ 2 * β * ‖k x‖ ^ 2 / 2 : ℝ) : ℂ) +
      Complex.I * (t * Real.sqrt β * g (x,ω) : ℝ))) =
      (fun x => featureCubicPolynomial β k g t (x,ω) + featureScalarRemainder β k g t (x,ω)) := by
    funext x
    unfold featureCubicPolynomial featureScalarRemainder
    ring
  rw [he]
  have ha := integral_add hp hremω
  rw [ha, integral_featureCubicPolynomial_of_mean_zero β hβ k g t ω hd h1 h2 hr hzero]
  rfl

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureCubicPolynomial
#print axioms DGRHS.Gaussian.featureCubicPolynomial

#check DGRHS.Gaussian.featureCubicPolynomial_eq
#print axioms DGRHS.Gaussian.featureCubicPolynomial_eq

#check DGRHS.Gaussian.integrable_featureCubicPolynomial_section
#print axioms DGRHS.Gaussian.integrable_featureCubicPolynomial_section

#check DGRHS.Gaussian.integral_featureCubicPolynomial_of_mean_zero
#print axioms DGRHS.Gaussian.integral_featureCubicPolynomial_of_mean_zero

#check DGRHS.Gaussian.memLp_featureGaussian_of_exponential_moment
#print axioms DGRHS.Gaussian.memLp_featureGaussian_of_exponential_moment

#check DGRHS.Gaussian.ae_feature_phase_expansion_of_exponential_moment
#print axioms DGRHS.Gaussian.ae_feature_phase_expansion_of_exponential_moment
