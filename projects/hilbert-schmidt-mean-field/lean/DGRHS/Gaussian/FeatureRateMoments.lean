/- UNCHECKED draft outside frozen proof. Actual supplied-field centering adapter
and probability-square estimates for subsequent source rate proof. -/
import DGRHS.Gaussian.FeatureModes
import DGRHS.Gaussian.Wick
import Mathlib.Tactic
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Gaussian

lemma ae_feature_spatial_mean_zero_of_same_process {ι H X : Type*} [Countable ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (hk : Measurable k) (hk2 : MemLp k 2 μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x,ω)) μ) ∧
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x,ω) ∂μ) = 0 := by
  have ha : MemLp (fun _ : X => (1 : ℝ)) 2 μ := memLp_const 1
  let a : Lp ℝ 2 μ := ha.toLp (fun _ : X => (1 : ℝ))
  have ha1 : (a : X → ℝ) =ᵐ[μ] fun _ => 1 := ha.coeFn_toLp
  have hA : featureSynthesis k hk2 a = 0 := by
    rw [featureSynthesis_eq_integral]
    calc
      (∫ x, a x • k x ∂μ) = ∫ x, k x ∂μ := by
        apply integral_congr_ae
        filter_upwards [ha1] with x hx
        rw [hx, one_smul]
      _ = 0 := hmean
  have hm := ae_weighted_featureGaussian_mode_of_fibers b f hf hk hk2 g hg hW a
  have hc (ω : ℕ → ℝ) : (fun x => a x * g (x,ω)) =ᵐ[μ] fun x => g (x,ω) := by
    filter_upwards [ha1] with x hx
    rw [hx, one_mul]
  have h0 : (indexedGaussianIsometry b f hf (featureSynthesis k hk2 a) : (ℕ → ℝ) → ℝ)
      =ᵐ[IsonormalProcess.iidStdGaussian] fun _ => 0 := by
    rw [hA, map_zero]
    exact Lp.coeFn_zero ℝ 2 IsonormalProcess.iidStdGaussian
  constructor
  · filter_upwards [hm.1] with ω hω
    exact hω.congr (hc ω)
  · filter_upwards [hm.2, h0] with ω hω hω0
    rw [← integral_congr_ae (hc ω)]
    exact hω.trans hω0

lemma integral_sq_mean_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (z : X → ℝ) (hz : Integrable z μ)
    (hz2 : Integrable (fun x => z x ^ 2) μ) :
    (∫ x, z x ∂μ) ^ 2 ≤ ∫ x, z x ^ 2 ∂μ := by
  let c := ∫ x, z x ∂μ
  have hpoly : (∫ x, (z x - c) ^ 2 ∂μ) = (∫ x, z x ^ 2 ∂μ) - c ^ 2 := by
    calc
      _ = ∫ x, (z x ^ 2 - 2 * c * z x) + c ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by
        have hsub : Integrable (fun x => z x ^ 2 - 2 * c * z x) μ :=
          hz2.sub (hz.const_mul (2 * c))
        rw [integral_add hsub (integrable_const (c ^ 2)),
          integral_sub hz2 (hz.const_mul (2 * c)), integral_const_mul]
        simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
        change (∫ x, z x ^ 2 ∂μ) - 2 * c * c + c ^ 2 = _
        ring
  have hn : 0 ≤ ∫ x, (z x - c) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  rw [hpoly] at hn
  exact sub_nonneg.mp hn

lemma ae_feature_fourth_moment {ι H X : Type*} [Countable ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace X]
    {μ : Measure X} (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ x ∂μ, Integrable (fun ω => g (x,ω) ^ 4) IsonormalProcess.iidStdGaussian ∧
      (∫ ω, g (x,ω) ^ 4 ∂IsonormalProcess.iidStdGaussian) = 3 * ‖k x‖ ^ 4 := by
  filter_upwards [hW] with x hx
  have hp : (fun ω => g (x,ω) ^ 4) =ᵐ[IsonormalProcess.iidStdGaussian]
      fun ω => indexedGaussianIsometry b f hf (k x) ω ^ 4 := by
    filter_upwards [hx] with ω hω
    rw [hω]
  constructor
  · exact (integrable_pow_four_gaussian_linear (indexedGaussianIsometry b f hf).toLinearMap
      (map_indexedGaussianIsometry_eq_gaussianReal b f hf) (k x)).congr hp.symm
  · rw [integral_congr_ae hp]
    exact integral_pow_four_gaussian_linear (indexedGaussianIsometry b f hf).toLinearMap
      (map_indexedGaussianIsometry_eq_gaussianReal b f hf) (k x)

lemma integrable_weighted_feature_fourth {ι H X : Type*} [Countable ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw4 : Integrable (fun x => w x * ‖k x‖ ^ 4) μ) :
    Integrable (fun p : X × (ℕ → ℝ) => w p.1 * g p ^ 4)
      (μ.prod IsonormalProcess.iidStdGaussian) := by
  have hm : StronglyMeasurable (fun p : X × (ℕ → ℝ) => w p.1 * g p ^ 4) :=
    (hw.comp measurable_fst).stronglyMeasurable.mul (hg.pow 4)
  have hs := ae_feature_fourth_moment b f hf k g hW
  have hn : (fun x => ∫ ω, ‖w x * g (x,ω) ^ 4‖ ∂IsonormalProcess.iidStdGaussian)
      =ᵐ[μ] fun x => 3 * (w x * ‖k x‖ ^ 4) := by
    filter_upwards [hs] with x hx
    calc
      _ = ∫ ω, w x * g (x,ω) ^ 4 ∂IsonormalProcess.iidStdGaussian := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (by positivity : 0 ≤ g (x,ω) ^ 4))]
      _ = _ := by rw [integral_const_mul, hx.2]; ring
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [hs] with x hx
    exact hx.1.const_mul (w x)
  · exact (hw4.const_mul 3).congr hn.symm

lemma integral_weighted_feature_fourth {ι H X : Type*} [Countable ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x))
    (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw4 : Integrable (fun x => w x * ‖k x‖ ^ 4) μ) :
    (∫ p, w p.1 * g p ^ 4 ∂μ.prod IsonormalProcess.iidStdGaussian) =
      3 * ∫ x, w x * ‖k x‖ ^ 4 ∂μ := by
  rw [integral_prod _ (integrable_weighted_feature_fourth b f hf k g hg hW w hw hw0 hw4),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_feature_fourth_moment b f hf k g hW] with x hx
  rw [integral_const_mul, hx.2]
  ring

end DGRHS.Gaussian
#check DGRHS.Gaussian.ae_feature_spatial_mean_zero_of_same_process
#print axioms DGRHS.Gaussian.ae_feature_spatial_mean_zero_of_same_process
#check DGRHS.Gaussian.integral_sq_mean_le
#print axioms DGRHS.Gaussian.integral_sq_mean_le

#check DGRHS.Gaussian.ae_feature_fourth_moment
#print axioms DGRHS.Gaussian.ae_feature_fourth_moment
#check DGRHS.Gaussian.integrable_weighted_feature_fourth
#print axioms DGRHS.Gaussian.integrable_weighted_feature_fourth
#check DGRHS.Gaussian.integral_weighted_feature_fourth
#print axioms DGRHS.Gaussian.integral_weighted_feature_fourth
