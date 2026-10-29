import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

lemma power_le_one_add_high {y : ℝ} (hy : 0 ≤ y) {r m : ℕ} (hrm : r ≤ m) :
    y ^ r ≤ 1 + y ^ m := by
  by_cases hy1 : y ≤ 1
  · have hr : y ^ r ≤ 1 := by
      simpa only [pow_zero] using pow_le_pow_of_le_one hy hy1 (Nat.zero_le r)
    exact hr.trans (le_add_of_nonneg_right (pow_nonneg hy m))
  · have hr : y ^ r ≤ y ^ m := pow_le_pow_right₀ (le_of_not_ge hy1) hrm
    exact hr.trans (le_add_of_nonneg_left zero_le_one)

lemma lower_raw_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (m r : ℕ)
    (hf : AEStronglyMeasurable f μ)
    (hh : Integrable (fun x ↦ |f x| ^ m) μ) (hrm : r ≤ m) :
    Integrable (fun x ↦ f x ^ r) μ := by
  apply ((integrable_const (1 : ℝ)).add hh).mono' (hf.pow r)
  exact Filter.Eventually.of_forall fun x ↦ by
    change |f x ^ r| ≤ 1 + |f x| ^ m
    simpa only [abs_pow] using power_le_one_add_high (abs_nonneg (f x)) hrm

lemma lower_abs_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (m r : ℕ)
    (hf : AEStronglyMeasurable f μ)
    (hh : Integrable (fun x ↦ |f x| ^ m) μ) (hrm : r ≤ m) :
    Integrable (fun x ↦ |f x| ^ r) μ := by
  simpa only [Real.norm_eq_abs, abs_pow] using
    (lower_raw_power_integrable μ f m r hf hh hrm).norm

lemma independent_mixed_product_integrable {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : iIndepFun X μ)
    (mX : ∀ i, AEMeasurable (X i) μ) (g : ι → ℝ → ℝ)
    (hg : ∀ i, Integrable (g i) (μ.map (X i))) :
    Integrable (fun ω ↦ ∏ i, g i (X i ω)) μ := by
  classical
  have hp : Integrable (fun x : ι → ℝ ↦ ∏ i, g i (x i))
      (Measure.pi (fun i ↦ μ.map (X i))) := Integrable.fintype_prod hg
  rw [← hX.map_fun_eq_pi_map mX] at hp
  have hj : AEMeasurable (fun ω ↦ (fun i ↦ X i ω)) μ := by fun_prop
  simpa only [Function.comp_def] using hp.comp_aemeasurable hj

#print axioms DGRHS.Concentration.lower_abs_power_integrable
#print axioms DGRHS.Concentration.independent_mixed_product_integrable

end DGRHS.Concentration
