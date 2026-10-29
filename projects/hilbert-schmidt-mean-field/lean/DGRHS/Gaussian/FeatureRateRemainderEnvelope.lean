import DGRHS.Gaussian.FeatureRateOscillatory
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma integrable_weighted_feature_second
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw2 : Integrable (fun x => w x * ‖k x‖ ^ 2) μ) :
    Integrable (fun p : X × (ℕ → ℝ) => w p.1 * g p ^ 2)
      (μ.prod IsonormalProcess.iidStdGaussian) := by
  have hm : StronglyMeasurable (fun p : X × (ℕ → ℝ) => w p.1 * g p ^ 2) :=
    (hw.comp measurable_fst).stronglyMeasurable.mul (hg.pow 2)
  have hs := ae_feature_second_and_sixth_moments b f hf k g hW
  have hn : (fun x => ∫ ω, ‖w x * g (x,ω) ^ 2‖ ∂IsonormalProcess.iidStdGaussian)
      =ᵐ[μ] fun x => w x * ‖k x‖ ^ 2 := by
    filter_upwards [hs] with x hx
    calc
      _ = ∫ ω, w x * g (x,ω) ^ 2 ∂IsonormalProcess.iidStdGaussian := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
      _ = _ := by rw [integral_const_mul, hx.1.2]
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [hs] with x hx
    exact hx.1.1.const_mul (w x)
  · exact hw2.congr hn.symm

lemma integral_weighted_feature_second
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw2 : Integrable (fun x => w x * ‖k x‖ ^ 2) μ) :
    (∫ p, w p.1 * g p ^ 2 ∂μ.prod IsonormalProcess.iidStdGaussian) =
      ∫ x, w x * ‖k x‖ ^ 2 ∂μ := by
  rw [integral_prod _ (integrable_weighted_feature_second b f hf k g hg hW w hw hw0 hw2)]
  apply integral_congr_ae
  filter_upwards [ae_feature_second_and_sixth_moments b f hf k g hW] with x hx
  rw [integral_const_mul, hx.1.2]

lemma feature_exponential_power_le_weight (β : ℝ) (k : X → H)
    (x : X) (p : ℕ) (hp : p ≤ 4) :
    Real.exp (β * ‖k x‖ ^ 2 / 2) * (‖k x‖ ^ 2) ^ p ≤ featureExponentialMomentWeight β k x := by
  exact mul_le_mul_of_nonneg_left
    (nonnegative_power_le_one_add_fourth (‖k x‖ ^ 2) (sq_nonneg _) p hp) (Real.exp_pos _).le

lemma integrable_feature_exponential_power (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (p : ℕ) (hp : p ≤ 4) :
    Integrable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * (‖k x‖ ^ 2) ^ p) μ := by
  apply hM.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact feature_exponential_power_le_weight β k x p hp

def featureRemainderEnvelope (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (p : X × (ℕ → ℝ)) : ℝ :=
  4 * (Real.exp (β * ‖k p.1‖ ^ 2 / 2) * g p ^ 4) +
  (3 / 2 : ℝ) * (Real.exp (β * ‖k p.1‖ ^ 2 / 2) * ‖k p.1‖ ^ 2 * g p ^ 2) +
  (1 / 2 : ℝ) * (Real.exp (β * ‖k p.1‖ ^ 2 / 2) * (‖k p.1‖ ^ 2) ^ 2)

lemma featureRemainderEnvelope_nonneg (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (p : X × (ℕ → ℝ)) :
    0 ≤ featureRemainderEnvelope β k g p := by
  unfold featureRemainderEnvelope
  positivity

private lemma remainder_weight_integrable (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ) :
    Integrable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * ‖k x‖ ^ 4) μ := by
  simpa only [← pow_mul] using integrable_feature_exponential_power β k hk hM 2 (by norm_num)

lemma integrable_featureRemainderEnvelope
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (featureRemainderEnvelope β k g) (μ.prod IsonormalProcess.iidStdGaussian) := by
  have hw : Measurable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2)) := by
    have hd : Measurable (fun x => ‖k x‖ ^ 2) := (hk.norm.pow 2).measurable
    fun_prop
  have hw0 (x : X) : 0 ≤ Real.exp (β * ‖k x‖ ^ 2 / 2) := (Real.exp_pos _).le
  have h4 := integrable_weighted_feature_fourth b f hf k g hg hW _ hw hw0
    (remainder_weight_integrable β k hk hM)
  have hwD : Measurable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * ‖k x‖ ^ 2) :=
    hw.mul ((hk.norm.pow 2).measurable)
  have hwD2 : Integrable (fun x => (Real.exp (β * ‖k x‖ ^ 2 / 2) * ‖k x‖ ^ 2) * ‖k x‖ ^ 2) μ := by
    convert integrable_feature_exponential_power β k hk hM 2 (by norm_num) using 1
    ext x
    ring
  have h2 := integrable_weighted_feature_second b f hf k g hg hW _ hwD (fun x => by positivity) hwD2
  have hc : Integrable (fun p : X × (ℕ → ℝ) => Real.exp (β * ‖k p.1‖ ^ 2 / 2) * (‖k p.1‖ ^ 2) ^ 2)
      (μ.prod IsonormalProcess.iidStdGaussian) := by
    simpa only [Function.comp_def] using
      (measurePreserving_fst (μ := μ) (ν := IsonormalProcess.iidStdGaussian)).integrable_comp_of_integrable
        (integrable_feature_exponential_power β k hk hM 2 (by norm_num))
  exact ((h4.const_mul 4).add (h2.const_mul (3 / 2 : ℝ))).add (hc.const_mul (1 / 2 : ℝ))

lemma integral_featureRemainderEnvelope
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ p, featureRemainderEnvelope β k g p ∂μ.prod IsonormalProcess.iidStdGaussian) =
      14 * ∫ x, Real.exp (β * ‖k x‖ ^ 2 / 2) * (‖k x‖ ^ 2) ^ 2 ∂μ := by
  have hw : Measurable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2)) := by
    have hd : Measurable (fun x => ‖k x‖ ^ 2) := (hk.norm.pow 2).measurable
    fun_prop
  have hw0 (x : X) : 0 ≤ Real.exp (β * ‖k x‖ ^ 2 / 2) := (Real.exp_pos _).le
  have h4 := integrable_weighted_feature_fourth b f hf k g hg hW _ hw hw0
    (remainder_weight_integrable β k hk hM)
  have hwD : Measurable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * ‖k x‖ ^ 2) :=
    hw.mul ((hk.norm.pow 2).measurable)
  have hwD2 : Integrable (fun x => (Real.exp (β * ‖k x‖ ^ 2 / 2) * ‖k x‖ ^ 2) * ‖k x‖ ^ 2) μ := by
    convert integrable_feature_exponential_power β k hk hM 2 (by norm_num) using 1
    ext x
    ring
  have h2 := integrable_weighted_feature_second b f hf k g hg hW _ hwD (fun x => by positivity) hwD2
  have hc : Integrable (fun p : X × (ℕ → ℝ) => Real.exp (β * ‖k p.1‖ ^ 2 / 2) * (‖k p.1‖ ^ 2) ^ 2)
      (μ.prod IsonormalProcess.iidStdGaussian) := by
    simpa only [Function.comp_def] using
      (measurePreserving_fst (μ := μ) (ν := IsonormalProcess.iidStdGaussian)).integrable_comp_of_integrable
        (integrable_feature_exponential_power β k hk hM 2 (by norm_num))
  have hcInt : (∫ p : X × (ℕ → ℝ), Real.exp (β * ‖k p.1‖ ^ 2 / 2) * (‖k p.1‖ ^ 2) ^ 2
      ∂μ.prod IsonormalProcess.iidStdGaussian) =
      ∫ x, Real.exp (β * ‖k x‖ ^ 2 / 2) * (‖k x‖ ^ 2) ^ 2 ∂μ := by
    rw [integral_prod _ hc]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  unfold featureRemainderEnvelope
  have hadd := integral_add ((h4.const_mul 4).add (h2.const_mul (3 / 2 : ℝ))) (hc.const_mul (1 / 2 : ℝ))
  have hadd2 := integral_add (h4.const_mul 4) (h2.const_mul (3 / 2 : ℝ))
  simp only [Pi.add_apply] at hadd hadd2
  rw [hadd, hadd2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_weighted_feature_fourth b f hf k g hg hW _ hw hw0
      (remainder_weight_integrable β k hk hM),
    integral_weighted_feature_second b f hf k g hg hW _ hwD (fun x => by positivity) hwD2, hcInt]
  have he1 : (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * ‖k x‖ ^ 4) =
      (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * (‖k x‖ ^ 2) ^ 2) := by ext x; ring
  have he2 : (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * ‖k x‖ ^ 2 * ‖k x‖ ^ 2) =
      (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * (‖k x‖ ^ 2) ^ 2) := by ext x; ring
  rw [he1, he2]
  ring

lemma integral_featureRemainderEnvelope_le_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ p, featureRemainderEnvelope β k g p ∂μ.prod IsonormalProcess.iidStdGaussian) ≤
      14 * ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  rw [integral_featureRemainderEnvelope b f hf β k hk hM g hg hW]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact integral_mono (integrable_feature_exponential_power β k hk hM 2 (by norm_num)) hM
    (fun x => feature_exponential_power_le_weight β k x 2 (by norm_num))

end DGRHS.Gaussian

#check DGRHS.Gaussian.integrable_weighted_feature_second
#print axioms DGRHS.Gaussian.integrable_weighted_feature_second

#check DGRHS.Gaussian.integral_weighted_feature_second
#print axioms DGRHS.Gaussian.integral_weighted_feature_second

#check DGRHS.Gaussian.feature_exponential_power_le_weight
#print axioms DGRHS.Gaussian.feature_exponential_power_le_weight

#check DGRHS.Gaussian.integrable_feature_exponential_power
#print axioms DGRHS.Gaussian.integrable_feature_exponential_power

#check DGRHS.Gaussian.featureRemainderEnvelope
#print axioms DGRHS.Gaussian.featureRemainderEnvelope

#check DGRHS.Gaussian.featureRemainderEnvelope_nonneg
#print axioms DGRHS.Gaussian.featureRemainderEnvelope_nonneg

#check DGRHS.Gaussian.integrable_featureRemainderEnvelope
#print axioms DGRHS.Gaussian.integrable_featureRemainderEnvelope

#check DGRHS.Gaussian.integral_featureRemainderEnvelope
#print axioms DGRHS.Gaussian.integral_featureRemainderEnvelope

#check DGRHS.Gaussian.integral_featureRemainderEnvelope_le_moment
#print axioms DGRHS.Gaussian.integral_featureRemainderEnvelope_le_moment
