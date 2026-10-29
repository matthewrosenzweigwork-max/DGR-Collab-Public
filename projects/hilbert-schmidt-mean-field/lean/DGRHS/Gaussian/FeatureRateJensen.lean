import DGRHS.Gaussian.FeatureRateCubicBound
import Mathlib.Analysis.Convex.Mul
noncomputable section
open MeasureTheory
namespace DGRHS.Gaussian
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X} [IsProbabilityMeasure μ]

def featurePositiveFactor (μ : Measure X) (β : ℝ) (k : X → H) (N : ℕ) : ℝ :=
  ∫ x, Real.exp (β * ‖k x‖ ^ 2 / (2 * (N : ℝ))) ∂μ

def featureExponentialFactor (μ : Measure X) (β : ℝ) (k : X → H) : ℝ :=
  ∫ x, Real.exp (β * ‖k x‖ ^ 2 / 2) ∂μ

lemma feature_small_exponent_le (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (N : ℕ) (hN : 1 ≤ N) (x : X) :
    β * ‖k x‖ ^ 2 / (2 * (N : ℝ)) ≤ β * ‖k x‖ ^ 2 / 2 := by
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))).2
  have hm := mul_nonneg (mul_nonneg hβ (sq_nonneg ‖k x‖)) (sub_nonneg.mpr hN1)
  nlinarith

lemma feature_exponential_le_weight (β : ℝ) (k : X → H) (x : X) :
    Real.exp (β * ‖k x‖ ^ 2 / 2) ≤ featureExponentialMomentWeight β k x := by
  unfold featureExponentialMomentWeight
  have hp : 0 ≤ (‖k x‖ ^ 2) ^ 4 := by positivity
  have he := Real.exp_pos (β * ‖k x‖ ^ 2 / 2)
  nlinarith

lemma integrable_feature_full_exponential (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ) :
    Integrable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2)) μ := by
  apply hM.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact feature_exponential_le_weight β k x

lemma integrable_feature_small_exponential (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun x => Real.exp (β * ‖k x‖ ^ 2 / (2 * (N : ℝ)))) μ := by
  apply (integrable_feature_full_exponential β k hk hM).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (feature_small_exponent_le β hβ k N hN x)

lemma one_le_featurePositiveFactor (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (N : ℕ) (hN : 1 ≤ N) : 1 ≤ featurePositiveFactor μ β k N := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hN)
  have hi := integral_mono (integrable_const (1 : ℝ))
    (integrable_feature_small_exponential β hβ k hk hM N hN)
    (fun x => Real.one_le_exp (show 0 ≤ β * ‖k x‖ ^ 2 / (2 * (N : ℝ)) by positivity))
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, featurePositiveFactor] using hi

lemma featurePositiveFactor_pow_le (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (N : ℕ) (hN : 1 ≤ N) :
    featurePositiveFactor μ β k N ^ N ≤ featureExponentialFactor μ β k := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hN)
  have he (x : X) : Real.exp (β * ‖k x‖ ^ 2 / (2 * (N : ℝ))) ^ N =
      Real.exp (β * ‖k x‖ ^ 2 / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    <;> ring
  have hp : Integrable (fun x => Real.exp (β * ‖k x‖ ^ 2 / (2 * (N : ℝ))) ^ N) μ := by
    simpa only [he] using integrable_feature_full_exponential β k hk hM
  have hi := (convexOn_pow (𝕜 := ℝ) N).map_integral_le (by fun_prop)
    isClosed_Ici (Filter.Eventually.of_forall (fun x => le_of_lt (Real.exp_pos _)))
    (integrable_feature_small_exponential β hβ k hk hM N hN) hp
  simpa only [featurePositiveFactor, featureExponentialFactor, he] using hi

lemma featureExponentialFactor_le_moment (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ) :
    featureExponentialFactor μ β k ≤ ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  exact integral_mono (integrable_feature_full_exponential β k hk hM) hM
    (feature_exponential_le_weight β k)

lemma exp_feature_mean_le_positiveFactor (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (β * (∫ x, ‖k x‖ ^ 2 ∂μ) / (2 * (N : ℝ))) ≤ featurePositiveFactor μ β k N := by
  have hd : Integrable (fun x => ‖k x‖ ^ 2) μ := by
    simpa only [pow_one] using integrable_feature_moment_power β hβ k hk hM 1 (by norm_num)
  have hc : Integrable (fun x => β * ‖k x‖ ^ 2 / (2 * (N : ℝ))) μ :=
    (hd.const_mul β).div_const _
  have hi := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hc
    (integrable_feature_small_exponential β hβ k hk hM N hN)
  simpa only [div_eq_mul_inv, integral_mul_const, integral_const_mul,
    featurePositiveFactor] using hi

lemma exp_feature_mean_le_fullFactor (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ) :
    Real.exp (β * (∫ x, ‖k x‖ ^ 2 ∂μ) / 2) ≤ featureExponentialFactor μ β k := by
  simpa only [Nat.cast_one, mul_one, featurePositiveFactor, featureExponentialFactor] using
    exp_feature_mean_le_positiveFactor β hβ k hk hM 1 (by norm_num)

end DGRHS.Gaussian

#check DGRHS.Gaussian.featurePositiveFactor
#print axioms DGRHS.Gaussian.featurePositiveFactor

#check DGRHS.Gaussian.featureExponentialFactor
#print axioms DGRHS.Gaussian.featureExponentialFactor

#check DGRHS.Gaussian.feature_small_exponent_le
#print axioms DGRHS.Gaussian.feature_small_exponent_le

#check DGRHS.Gaussian.feature_exponential_le_weight
#print axioms DGRHS.Gaussian.feature_exponential_le_weight

#check DGRHS.Gaussian.integrable_feature_full_exponential
#print axioms DGRHS.Gaussian.integrable_feature_full_exponential

#check DGRHS.Gaussian.integrable_feature_small_exponential
#print axioms DGRHS.Gaussian.integrable_feature_small_exponential

#check DGRHS.Gaussian.one_le_featurePositiveFactor
#print axioms DGRHS.Gaussian.one_le_featurePositiveFactor

#check DGRHS.Gaussian.featurePositiveFactor_pow_le
#print axioms DGRHS.Gaussian.featurePositiveFactor_pow_le

#check DGRHS.Gaussian.featureExponentialFactor_le_moment
#print axioms DGRHS.Gaussian.featureExponentialFactor_le_moment

#check DGRHS.Gaussian.exp_feature_mean_le_positiveFactor
#print axioms DGRHS.Gaussian.exp_feature_mean_le_positiveFactor

#check DGRHS.Gaussian.exp_feature_mean_le_fullFactor
#print axioms DGRHS.Gaussian.exp_feature_mean_le_fullFactor
