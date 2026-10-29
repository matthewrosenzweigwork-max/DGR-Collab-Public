import DGRHS.Gaussian.FeatureRateSecondMoments

/- Actual sixth moments and mixed D²g² integrability for the SAME process.
These furnish the product-L2 cubic needed for proper source R expectations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

private lemma integrable_pow_six_indexed (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (v : H) :
    Integrable (fun ω => indexedGaussianIsometry b f hf v ω ^ 6) IsonormalProcess.iidStdGaussian := by
  have hmmap : MemLp id 6 (IsonormalProcess.iidStdGaussian.map (indexedGaussianIsometry b f hf v)) := by
    rw [map_indexedGaussianIsometry_eq_gaussianReal b f hf v]
    exact memLp_id_gaussianReal' 6 (by norm_num)
  have hm : MemLp (indexedGaussianIsometry b f hf v : (ℕ → ℝ) → ℝ) 6
      IsonormalProcess.iidStdGaussian := by
    simpa only [Function.comp_def, id_eq] using hmmap.comp_of_map
      (Lp.aestronglyMeasurable (indexedGaussianIsometry b f hf v)).aemeasurable
  have hi := hm.integrable_norm_pow (by decide : (6 : ℕ) ≠ 0)
  simpa only [Real.norm_eq_abs, show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs] using hi

private lemma integral_pow_six_indexed (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (v : H) :
    (∫ ω, indexedGaussianIsometry b f hf v ω ^ 6 ∂IsonormalProcess.iidStdGaussian) =
      15 * ‖v‖ ^ 6 := by
  have hi := integral_map (Lp.aestronglyMeasurable (indexedGaussianIsometry b f hf v)).aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => x ^ 6)
      (IsonormalProcess.iidStdGaussian.map (indexedGaussianIsometry b f hf v)) by fun_prop)
  rw [map_indexedGaussianIsometry_eq_gaussianReal b f hf v] at hi
  rw [← hi, integral_pow_six_gaussianReal_sq]

lemma ae_feature_second_and_sixth_moments
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ x ∂μ,
      (Integrable (fun ω => g (x,ω) ^ 2) IsonormalProcess.iidStdGaussian ∧
        (∫ ω, g (x,ω) ^ 2 ∂IsonormalProcess.iidStdGaussian) = ‖k x‖ ^ 2) ∧
      (Integrable (fun ω => g (x,ω) ^ 6) IsonormalProcess.iidStdGaussian ∧
        (∫ ω, g (x,ω) ^ 6 ∂IsonormalProcess.iidStdGaussian) = 15 * ‖k x‖ ^ 6) := by
  filter_upwards [hW] with x hx
  have hp (n : ℕ) : (fun ω => g (x,ω) ^ n) =ᵐ[IsonormalProcess.iidStdGaussian]
      fun ω => indexedGaussianIsometry b f hf (k x) ω ^ n := by
    filter_upwards [hx] with ω hω
    rw [hω]
  constructor
  · constructor
    · exact ((Lp.memLp (indexedGaussianIsometry b f hf (k x))).integrable_sq).congr (hp 2).symm
    · rw [integral_congr_ae (hp 2)]
      simp only [pow_two, indexedGaussianIsometry_cov, real_inner_self_eq_norm_sq]
  · constructor
    · exact (integrable_pow_six_indexed b f hf (k x)).congr (hp 6).symm
    · rw [integral_congr_ae (hp 6)]
      exact integral_pow_six_indexed b f hf (k x)

lemma integrable_feature_sixth_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun p => g p ^ 6) (μ.prod IsonormalProcess.iidStdGaussian) := by
  have h6 := ae_feature_second_and_sixth_moments b f hf k g hW
  have hk6 : Integrable (fun x => ‖k x‖ ^ 6) μ := by
    simpa only [← pow_mul] using integrable_feature_moment_power β hβ k hk hM 3 (by norm_num)
  have hn : (fun x => ∫ ω, ‖g (x,ω) ^ 6‖ ∂IsonormalProcess.iidStdGaussian)
      =ᵐ[μ] fun x => 15 * ‖k x‖ ^ 6 := by
    filter_upwards [h6] with x hx
    calc
      _ = ∫ ω, g (x,ω) ^ 6 ∂IsonormalProcess.iidStdGaussian := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ g (x,ω) ^ 6)]
      _ = _ := hx.2.2
  apply (integrable_prod_iff (hg.pow 6).aestronglyMeasurable).2
  exact ⟨h6.mono (fun x hx => hx.2.1), (hk6.const_mul 15).congr hn.symm⟩

lemma integrable_feature_mixed_square_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun p => ‖k p.1‖ ^ 4 * g p ^ 2) (μ.prod IsonormalProcess.iidStdGaussian) := by
  have h2 := ae_feature_second_and_sixth_moments b f hf k g hW
  have hk6 : Integrable (fun x => ‖k x‖ ^ 6) μ := by
    simpa only [← pow_mul] using integrable_feature_moment_power β hβ k hk hM 3 (by norm_num)
  have hm : StronglyMeasurable (fun p : X × (ℕ → ℝ) => ‖k p.1‖ ^ 4 * g p ^ 2) :=
    ((hk.norm.pow 4).comp_measurable measurable_fst).mul (hg.pow 2)
  have hn : (fun x => ∫ ω, ‖‖k x‖ ^ 4 * g (x,ω) ^ 2‖ ∂IsonormalProcess.iidStdGaussian)
      =ᵐ[μ] fun x => ‖k x‖ ^ 6 := by
    filter_upwards [h2] with x hx
    calc
      _ = ∫ ω, ‖k x‖ ^ 4 * g (x,ω) ^ 2 ∂IsonormalProcess.iidStdGaussian := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖k x‖ ^ 4 * g (x,ω) ^ 2)]
      _ = _ := by rw [integral_const_mul, hx.1.2]; ring
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [h2] with x hx
    exact hx.1.1.const_mul (‖k x‖ ^ 4)
  · exact hk6.congr hn.symm

def featureCubicIntegrand (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (p : X × (ℕ → ℝ)) : ℝ :=
  ‖k p.1‖ ^ 2 * g p / 2 - g p ^ 3 / 6

lemma featureCubicIntegrand_sq_le (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (p : X × (ℕ → ℝ)) :
    featureCubicIntegrand k g p ^ 2 ≤ ‖k p.1‖ ^ 4 * g p ^ 2 / 2 + g p ^ 6 / 18 := by
  unfold featureCubicIntegrand
  nlinarith [sq_nonneg (‖k p.1‖ ^ 2 * g p / 2 + g p ^ 3 / 6)]

lemma stronglyMeasurable_featureCubicIntegrand (k : X → H) (hk : StronglyMeasurable k)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) :
    StronglyMeasurable (featureCubicIntegrand k g) := by
  unfold featureCubicIntegrand
  fun_prop

lemma integrable_featureCubicIntegrand_sq_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun p => featureCubicIntegrand k g p ^ 2) (μ.prod IsonormalProcess.iidStdGaussian) := by
  have hm := integrable_feature_mixed_square_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have h6 := integrable_feature_sixth_of_exponential_moment b f hf β hβ k hk hM g hg hW
  apply ((hm.div_const 2).add (h6.div_const 18)).mono'
    ((stronglyMeasurable_featureCubicIntegrand k hk g hg).pow 2).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact featureCubicIntegrand_sq_le k g p

lemma memLp_featureCubicIntegrand_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    MemLp (featureCubicIntegrand k g) 2 (μ.prod IsonormalProcess.iidStdGaussian) :=
  (memLp_two_iff_integrable_sq (stronglyMeasurable_featureCubicIntegrand k hk g hg).aestronglyMeasurable).2
    (integrable_featureCubicIntegrand_sq_of_exponential_moment b f hf β hβ k hk hM g hg hW)

lemma integrable_featureRateR_sq_of_exponential_moment
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    Integrable (fun ω => featureRateR μ β k g ω ^ 2) IsonormalProcess.iidStdGaussian := by
  have hr := memLp_featureCubicIntegrand_of_exponential_moment b f hf β hβ k hk hM g hg hW
  have hri := hr.integrable (by norm_num)
  have hR : StronglyMeasurable (featureRateR μ β k g) := by
    exact (stronglyMeasurable_featureCubicIntegrand k hk g hg).integral_prod_left'.const_mul _
  apply (hr.integrable_sq.integral_prod_right.const_mul (β ^ 3)).mono' (hR.pow 2).aestronglyMeasurable
  filter_upwards [hri.prod_left_ae, hr.integrable_sq.prod_left_ae] with ω hω hω2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hs : (β * Real.sqrt β) ^ 2 = β ^ 3 := by rw [mul_pow, Real.sq_sqrt hβ]; ring
  change (β * Real.sqrt β * ∫ x, featureCubicIntegrand k g (x,ω) ∂μ) ^ 2 ≤ _
  rw [mul_pow, hs]
  exact mul_le_mul_of_nonneg_left (integral_sq_mean_le _ hω hω2) (pow_nonneg hβ 3)

end DGRHS.Gaussian

#check DGRHS.Gaussian.ae_feature_second_and_sixth_moments
#print axioms DGRHS.Gaussian.ae_feature_second_and_sixth_moments
#check DGRHS.Gaussian.integrable_feature_sixth_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_feature_sixth_of_exponential_moment
#check DGRHS.Gaussian.integrable_feature_mixed_square_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_feature_mixed_square_of_exponential_moment
#check DGRHS.Gaussian.featureCubicIntegrand
#print axioms DGRHS.Gaussian.featureCubicIntegrand
#check DGRHS.Gaussian.featureCubicIntegrand_sq_le
#print axioms DGRHS.Gaussian.featureCubicIntegrand_sq_le
#check DGRHS.Gaussian.stronglyMeasurable_featureCubicIntegrand
#print axioms DGRHS.Gaussian.stronglyMeasurable_featureCubicIntegrand
#check DGRHS.Gaussian.integrable_featureCubicIntegrand_sq_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_featureCubicIntegrand_sq_of_exponential_moment
#check DGRHS.Gaussian.memLp_featureCubicIntegrand_of_exponential_moment
#print axioms DGRHS.Gaussian.memLp_featureCubicIntegrand_of_exponential_moment
#check DGRHS.Gaussian.integrable_featureRateR_sq_of_exponential_moment
#print axioms DGRHS.Gaussian.integrable_featureRateR_sq_of_exponential_moment
