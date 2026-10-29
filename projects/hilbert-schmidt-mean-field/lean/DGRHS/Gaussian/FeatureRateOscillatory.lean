import DGRHS.Gaussian.FeatureRateJensen
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X} [IsProbabilityMeasure μ]

def featureOscillatoryIntegrand (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : X × (ℕ → ℝ)) : ℂ :=
  Complex.exp ((β * ‖k p.1‖ ^ 2 / (2 * (N : ℝ)) : ℝ) +
    Complex.I * (Real.sqrt (β / (N : ℝ)) * g p : ℝ))

def featureOscillatoryFactor (μ : Measure X) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℂ :=
  ∫ x, featureOscillatoryIntegrand β k g N (x,ω) ∂μ

lemma norm_featureOscillatoryIntegrand (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : X × (ℕ → ℝ)) :
    ‖featureOscillatoryIntegrand β k g N p‖ =
      Real.exp (β * ‖k p.1‖ ^ 2 / (2 * (N : ℝ))) := by
  unfold featureOscillatoryIntegrand
  rw [Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

lemma stronglyMeasurable_featureOscillatoryIntegrand (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (N : ℕ) : StronglyMeasurable (featureOscillatoryIntegrand β k g N) := by
  unfold featureOscillatoryIntegrand
  apply Complex.continuous_exp.comp_stronglyMeasurable
  apply StronglyMeasurable.add
  · apply Complex.continuous_ofReal.comp_stronglyMeasurable
    simp only [div_eq_mul_inv]
    exact (((hk.comp_measurable measurable_fst).norm.pow 2).const_mul β).mul_const _
  · apply StronglyMeasurable.const_mul
    apply Complex.continuous_ofReal.comp_stronglyMeasurable
    exact hg.const_mul _

lemma integrable_featureOscillatoryIntegrand_section (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) (N : ℕ) (hN : 1 ≤ N)
    (ω : ℕ → ℝ) : Integrable (fun x => featureOscillatoryIntegrand β k g N (x,ω)) μ := by
  apply (integrable_feature_small_exponential β hβ k hk hM N hN).mono'
    ((stronglyMeasurable_featureOscillatoryIntegrand β k hk g hg N).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with x
  exact le_of_eq (norm_featureOscillatoryIntegrand β k g N (x,ω))

lemma integrable_featureOscillatoryIntegrand (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (featureOscillatoryIntegrand β k g N) (μ.prod IsonormalProcess.iidStdGaussian) := by
  have he := (measurePreserving_fst (μ := μ) (ν := IsonormalProcess.iidStdGaussian)).integrable_comp_of_integrable
    (integrable_feature_small_exponential β hβ k hk hM N hN)
  apply he.mono' (stronglyMeasurable_featureOscillatoryIntegrand β k hk g hg N).aestronglyMeasurable
  filter_upwards [] with p
  exact le_of_eq (norm_featureOscillatoryIntegrand β k g N p)

lemma stronglyMeasurable_featureOscillatoryFactor (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (N : ℕ) : StronglyMeasurable (featureOscillatoryFactor μ β k g N) :=
  (stronglyMeasurable_featureOscillatoryIntegrand β k hk g hg N).integral_prod_left'

lemma norm_featureOscillatoryFactor_le (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    ‖featureOscillatoryFactor μ β k g N ω‖ ≤ featurePositiveFactor μ β k N := by
  calc
    _ ≤ ∫ x, ‖featureOscillatoryIntegrand β k g N (x,ω)‖ ∂μ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_featureOscillatoryIntegrand, featurePositiveFactor]

lemma norm_featureOscillatoryFactor_pow_le (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (hN : 1 ≤ N) (ω : ℕ → ℝ) :
    ‖featureOscillatoryFactor μ β k g N ω ^ N‖ ≤ featureExponentialFactor μ β k := by
  rw [norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_featureOscillatoryFactor_le β k g N ω) N).trans
    (featurePositiveFactor_pow_le β hβ k hk hM N hN)

lemma integrable_featureOscillatoryFactor_pow (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun ω => featureOscillatoryFactor μ β k g N ω ^ N)
      IsonormalProcess.iidStdGaussian := by
  apply (integrable_const (featureExponentialFactor μ β k)).mono'
    ((stronglyMeasurable_featureOscillatoryFactor β k hk g hg N).pow N).aestronglyMeasurable
  filter_upwards [] with ω
  exact norm_featureOscillatoryFactor_pow_le β hβ k hk hM g N hN ω

lemma exp_featureRateB_div_le_positiveFactor (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (hN : 1 ≤ N) (ω : ℕ → ℝ) :
    Real.exp (featureRateB μ β k g ω / (N : ℝ)) ≤ featurePositiveFactor μ β k N := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hN)
  have hq : 0 ≤ ∫ x, g (x,ω) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  apply (Real.exp_le_exp.mpr ?_).trans (exp_feature_mean_le_positiveFactor β hβ k hk hM N hN)
  unfold featureRateB
  apply (div_le_iff₀ hNp).2
  have hm := mul_nonneg hβ hq
  field_simp
  nlinarith

lemma exp_featureRateB_le_fullFactor (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) :
    Real.exp (featureRateB μ β k g ω) ≤ featureExponentialFactor μ β k := by
  simpa only [Nat.cast_one, div_one, featurePositiveFactor, featureExponentialFactor, mul_one] using
    exp_featureRateB_div_le_positiveFactor β hβ k hk hM g 1 (by norm_num) ω

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureOscillatoryIntegrand
#print axioms DGRHS.Gaussian.featureOscillatoryIntegrand

#check DGRHS.Gaussian.featureOscillatoryFactor
#print axioms DGRHS.Gaussian.featureOscillatoryFactor

#check DGRHS.Gaussian.norm_featureOscillatoryIntegrand
#print axioms DGRHS.Gaussian.norm_featureOscillatoryIntegrand

#check DGRHS.Gaussian.stronglyMeasurable_featureOscillatoryIntegrand
#print axioms DGRHS.Gaussian.stronglyMeasurable_featureOscillatoryIntegrand

#check DGRHS.Gaussian.integrable_featureOscillatoryIntegrand_section
#print axioms DGRHS.Gaussian.integrable_featureOscillatoryIntegrand_section

#check DGRHS.Gaussian.integrable_featureOscillatoryIntegrand
#print axioms DGRHS.Gaussian.integrable_featureOscillatoryIntegrand

#check DGRHS.Gaussian.stronglyMeasurable_featureOscillatoryFactor
#print axioms DGRHS.Gaussian.stronglyMeasurable_featureOscillatoryFactor

#check DGRHS.Gaussian.norm_featureOscillatoryFactor_le
#print axioms DGRHS.Gaussian.norm_featureOscillatoryFactor_le

#check DGRHS.Gaussian.norm_featureOscillatoryFactor_pow_le
#print axioms DGRHS.Gaussian.norm_featureOscillatoryFactor_pow_le

#check DGRHS.Gaussian.integrable_featureOscillatoryFactor_pow
#print axioms DGRHS.Gaussian.integrable_featureOscillatoryFactor_pow

#check DGRHS.Gaussian.exp_featureRateB_div_le_positiveFactor
#print axioms DGRHS.Gaussian.exp_featureRateB_div_le_positiveFactor

#check DGRHS.Gaussian.exp_featureRateB_le_fullFactor
#print axioms DGRHS.Gaussian.exp_featureRateB_le_fullFactor
