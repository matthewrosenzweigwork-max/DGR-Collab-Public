import DGRHS.Gaussian.FeatureRateExpansion
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def featureRateScale (N : ℕ) : ℝ := Real.sqrt (N : ℝ)⁻¹

lemma featureRateScale_nonneg (N : ℕ) : 0 ≤ featureRateScale N := Real.sqrt_nonneg _

lemma featureRateScale_le_one (N : ℕ) (hN : 1 ≤ N) : featureRateScale N ≤ 1 := by
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hd : (1 : ℝ) / (N : ℝ) ≤ 1 := (div_le_iff₀ hNp).2 (by simpa)
  have hi : (N : ℝ)⁻¹ ≤ 1 := by simpa only [one_div] using hd
  exact (Real.sqrt_le_sqrt hi).trans_eq Real.sqrt_one

lemma featureRateScale_sq (N : ℕ) : featureRateScale N ^ 2 = (N : ℝ)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg N))

lemma featureRateScale_cube (N : ℕ) :
    featureRateScale N ^ 3 = 1 / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
  calc
    _ = featureRateScale N ^ 2 * featureRateScale N := by ring
    _ = (N : ℝ)⁻¹ * Real.sqrt (N : ℝ)⁻¹ := by rw [featureRateScale_sq]; rfl
    _ = _ := by rw [Real.sqrt_inv]; simp only [one_div, mul_inv_rev]; ring

lemma featureRateScale_fourth_cancel (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ 2 * featureRateScale N ^ 4 = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by norm_num : 0 < 1) hN))
  rw [show featureRateScale N ^ 4 = (featureRateScale N ^ 2) ^ 2 by ring, featureRateScale_sq]
  field_simp

lemma featureRateScale_mul_sqrt (β : ℝ) (N : ℕ) :
    featureRateScale N * Real.sqrt β = Real.sqrt (β / (N : ℝ)) := by
  unfold featureRateScale
  rw [div_eq_mul_inv, Real.sqrt_mul' β (inv_nonneg.mpr (Nat.cast_nonneg N))]
  ring

def featureRateRemainder (μ : Measure X) (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℂ :=
  ((N : ℝ) ^ 2 : ℝ) * featureIntegratedRemainder μ β k g (featureRateScale N) ω

lemma featureRateRemainder_div_sq (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (hN : 1 ≤ N) (ω : ℕ → ℝ) :
    featureRateRemainder μ β k g N ω / ((N : ℝ) ^ 2 : ℝ) =
      featureIntegratedRemainder μ β k g (featureRateScale N) ω := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by norm_num : 0 < 1) hN))
  unfold featureRateRemainder
  push_cast
  field_simp

lemma norm_featureRateRemainder (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    ‖featureRateRemainder μ β k g N ω‖ =
      (N : ℝ) ^ 2 * ‖featureIntegratedRemainder μ β k g (featureRateScale N) ω‖ := by
  unfold featureRateRemainder
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

lemma stronglyMeasurable_featureRateRemainder (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (N : ℕ) : StronglyMeasurable (featureRateRemainder μ β k g N) :=
  (stronglyMeasurable_featureIntegratedRemainder β k hk g hg (featureRateScale N)).const_mul _

lemma integrable_featureRateRemainder
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (N : ℕ) (hN : 1 ≤ N) :
    Integrable (featureRateRemainder μ β k g N) IsonormalProcess.iidStdGaussian :=
  (integrable_featureIntegratedRemainder b f hf β hβ k hk hM g hg hW (featureRateScale N)
    (featureRateScale_nonneg N) (featureRateScale_le_one N hN)).const_mul _

lemma integral_norm_featureRateRemainder_le
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (N : ℕ) (hN : 1 ≤ N) :
    (∫ ω, ‖featureRateRemainder μ β k g N ω‖ ∂IsonormalProcess.iidStdGaussian) ≤
      14 * β ^ 2 * ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  simp_rw [norm_featureRateRemainder]
  rw [integral_const_mul]
  calc
    _ ≤ (N : ℝ) ^ 2 * (14 * featureRateScale N ^ 4 * β ^ 2 *
        ∫ x, featureExponentialMomentWeight β k x ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_norm_featureIntegratedRemainder_le b f hf β hβ k hk hM g hg hW
        (featureRateScale N) (featureRateScale_nonneg N) (featureRateScale_le_one N hN)) (sq_nonneg _)
    _ = _ := by
      calc
        _ = 14 * β ^ 2 * (∫ x, featureExponentialMomentWeight β k x ∂μ) *
            ((N : ℝ) ^ 2 * featureRateScale N ^ 4) := by ring
        _ = _ := by rw [featureRateScale_fourth_cancel N hN, mul_one]

lemma featureOscillatoryIntegrand_eq_scaled_phase (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : X × (ℕ → ℝ)) :
    featureOscillatoryIntegrand β k g N p =
      Complex.exp (((featureRateScale N ^ 2 * β * ‖k p.1‖ ^ 2 / 2 : ℝ) : ℂ) +
        Complex.I * (featureRateScale N * Real.sqrt β * g p : ℝ)) := by
  unfold featureOscillatoryIntegrand
  rw [featureRateScale_sq, featureRateScale_mul_sqrt]
  congr 2
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma ae_featureOscillatoryFactor_expansion
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
      featureOscillatoryFactor μ β k g N ω =
      1 + (featureRateB μ β k g ω / (N : ℝ) : ℝ) +
        Complex.I * (featureRateR μ β k g ω / ((N : ℝ) * Real.sqrt (N : ℝ)) : ℝ) +
        featureRateRemainder μ β k g N ω / ((N : ℝ) ^ 2 : ℝ) := by
  filter_upwards [ae_feature_phase_expansion_of_exponential_moment b f hf β hβ k hk hM hmean g hg hW
    (featureRateScale N) (featureRateScale_nonneg N) (featureRateScale_le_one N hN)] with ω hω
  unfold featureOscillatoryFactor
  simp_rw [featureOscillatoryIntegrand_eq_scaled_phase]
  rw [hω, featureRateScale_sq, featureRateScale_cube, featureRateRemainder_div_sq β k g N hN ω]
  push_cast
  simp only [div_eq_mul_inv]
  ring

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureRateScale
#print axioms DGRHS.Gaussian.featureRateScale

#check DGRHS.Gaussian.featureRateScale_nonneg
#print axioms DGRHS.Gaussian.featureRateScale_nonneg

#check DGRHS.Gaussian.featureRateScale_le_one
#print axioms DGRHS.Gaussian.featureRateScale_le_one

#check DGRHS.Gaussian.featureRateScale_sq
#print axioms DGRHS.Gaussian.featureRateScale_sq

#check DGRHS.Gaussian.featureRateScale_cube
#print axioms DGRHS.Gaussian.featureRateScale_cube

#check DGRHS.Gaussian.featureRateScale_fourth_cancel
#print axioms DGRHS.Gaussian.featureRateScale_fourth_cancel

#check DGRHS.Gaussian.featureRateScale_mul_sqrt
#print axioms DGRHS.Gaussian.featureRateScale_mul_sqrt

#check DGRHS.Gaussian.featureRateRemainder
#print axioms DGRHS.Gaussian.featureRateRemainder

#check DGRHS.Gaussian.featureRateRemainder_div_sq
#print axioms DGRHS.Gaussian.featureRateRemainder_div_sq

#check DGRHS.Gaussian.norm_featureRateRemainder
#print axioms DGRHS.Gaussian.norm_featureRateRemainder

#check DGRHS.Gaussian.stronglyMeasurable_featureRateRemainder
#print axioms DGRHS.Gaussian.stronglyMeasurable_featureRateRemainder

#check DGRHS.Gaussian.integrable_featureRateRemainder
#print axioms DGRHS.Gaussian.integrable_featureRateRemainder

#check DGRHS.Gaussian.integral_norm_featureRateRemainder_le
#print axioms DGRHS.Gaussian.integral_norm_featureRateRemainder_le

#check DGRHS.Gaussian.featureOscillatoryIntegrand_eq_scaled_phase
#print axioms DGRHS.Gaussian.featureOscillatoryIntegrand_eq_scaled_phase

#check DGRHS.Gaussian.ae_featureOscillatoryFactor_expansion
#print axioms DGRHS.Gaussian.ae_featureOscillatoryFactor_expansion
