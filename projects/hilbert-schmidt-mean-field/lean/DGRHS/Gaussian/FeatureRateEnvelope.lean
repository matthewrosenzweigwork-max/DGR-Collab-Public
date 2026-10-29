/- UNCHECKED outside proof: actual source moment hypothesis and elementary
domination. A finite totalized real integral is never used as integrability. -/
import DGRHS.Gaussian.FeatureQuadraticLaplace
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic
open MeasureTheory
noncomputable section
namespace DGRHS.Gaussian

def featureExponentialMomentWeight {X H : Type*} [NormedAddCommGroup H]
    (β : ℝ) (k : X → H) (x : X) : ℝ :=
  Real.exp (β * ‖k x‖ ^ 2 / 2) * (1 + (‖k x‖ ^ 2) ^ 4)

lemma nonnegative_power_le_one_add_fourth (d : ℝ) (hd : 0 ≤ d) (p : ℕ) (hp : p ≤ 4) :
    d ^ p ≤ 1 + d ^ 4 := by
  by_cases ht : d ≤ 1
  · have hp1 := pow_le_pow_left₀ hd ht p
    simp only [one_pow] at hp1
    exact hp1.trans (by linarith [pow_nonneg hd 4])
  · have h1 : 1 ≤ d := le_of_lt (lt_of_not_ge ht)
    exact (pow_le_pow_right₀ h1 hp).trans (by linarith)

lemma one_le_featureExponentialMomentWeight {X H : Type*} [NormedAddCommGroup H]
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (x : X) :
    1 ≤ featureExponentialMomentWeight β k x := by
  have he : 1 ≤ Real.exp (β * ‖k x‖ ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hp : 1 ≤ 1 + (‖k x‖ ^ 2) ^ 4 := by
    linarith [pow_nonneg (sq_nonneg ‖k x‖) 4]
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ 1 + (‖k x‖ ^ 2) ^ 4 by positivity)
  unfold featureExponentialMomentWeight
  exact hp.trans (by simpa only [one_mul] using hm)

lemma feature_moment_power_le_weight {X H : Type*} [NormedAddCommGroup H]
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (x : X) (p : ℕ) (hp : p ≤ 4) :
    (‖k x‖ ^ 2) ^ p ≤ featureExponentialMomentWeight β k x := by
  have hd : 0 ≤ ‖k x‖ ^ 2 := sq_nonneg _
  have he : 1 ≤ Real.exp (β * ‖k x‖ ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ 1 + (‖k x‖ ^ 2) ^ 4 by positivity)
  apply (nonnegative_power_le_one_add_fourth (‖k x‖ ^ 2) hd p hp).trans
  simpa only [one_mul, featureExponentialMomentWeight] using hm

lemma integrable_feature_moment_power {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X}
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ) (p : ℕ) (hp : p ≤ 4) :
    Integrable (fun x => (‖k x‖ ^ 2) ^ p) μ := by
  apply hM.mono' ((hk.norm.pow 2).pow p).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
  exact feature_moment_power_le_weight β hβ k x p hp

lemma memLp_feature_of_exponential_moment {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X}
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ) : MemLp k 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).2
  simpa only [pow_one] using integrable_feature_moment_power β hβ k hk hM 1 (by norm_num)

lemma integral_feature_moment_power_le {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X}
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ) (p : ℕ) (hp : p ≤ 4) :
    (∫ x, (‖k x‖ ^ 2) ^ p ∂μ) ≤ ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  apply integral_mono (integrable_feature_moment_power β hβ k hk hM p hp) hM
  intro x
  exact feature_moment_power_le_weight β hβ k x p hp

lemma one_le_integral_featureExponentialMomentWeight {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} [IsProbabilityMeasure μ]
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hM : Integrable (featureExponentialMomentWeight β k) μ) :
    1 ≤ ∫ x, featureExponentialMomentWeight β k x ∂μ := by
  have hi := integral_mono (integrable_const (1 : ℝ)) hM
    (one_le_featureExponentialMomentWeight β hβ k)
  simpa using hi

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureExponentialMomentWeight
#print axioms DGRHS.Gaussian.featureExponentialMomentWeight
#check DGRHS.Gaussian.nonnegative_power_le_one_add_fourth
#print axioms DGRHS.Gaussian.nonnegative_power_le_one_add_fourth
#check DGRHS.Gaussian.one_le_featureExponentialMomentWeight
#print axioms DGRHS.Gaussian.one_le_featureExponentialMomentWeight
#check DGRHS.Gaussian.feature_moment_power_le_weight
#print axioms DGRHS.Gaussian.feature_moment_power_le_weight
#check DGRHS.Gaussian.integrable_feature_moment_power
#print axioms DGRHS.Gaussian.integrable_feature_moment_power
#check DGRHS.Gaussian.memLp_feature_of_exponential_moment
#print axioms DGRHS.Gaussian.memLp_feature_of_exponential_moment
#check DGRHS.Gaussian.integral_feature_moment_power_le
#print axioms DGRHS.Gaussian.integral_feature_moment_power_le
#check DGRHS.Gaussian.one_le_integral_featureExponentialMomentWeight
#print axioms DGRHS.Gaussian.one_le_integral_featureExponentialMomentWeight
