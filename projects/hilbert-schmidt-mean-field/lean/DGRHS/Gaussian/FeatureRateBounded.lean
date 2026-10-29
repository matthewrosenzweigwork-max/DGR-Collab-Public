import DGRHS.Gaussian.FeatureRateSourceSpectrum
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The actual source bounded-feature specialization. The moment premise is
DERIVED from MemLp k infinity, and the beta-dependent source exponential bound
uses the actual essential L-infinity norm. Beta zero is included separately. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
universe u v
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {H : Type v} [NormedAddCommGroup H]

def featureBoundedRateConstant (β : ℝ) : ℝ :=
  1 + 2 / β + 625 * (26 * β ^ 2 + 12 * β ^ 3)

lemma featureBoundedRateConstant_pos (β : ℝ) (hβ : 0 ≤ β) :
    0 < featureBoundedRateConstant β := by
  have hd : 0 ≤ 2 / β := div_nonneg (by norm_num) hβ
  unfold featureBoundedRateConstant
  positivity

lemma featureExponentialMomentWeight_le_bounded (β : ℝ) (hβ : 0 ≤ β)
    (k : X → H) (K : ℝ) (hK : 0 ≤ K) (x : X) (hx : ‖k x‖ ≤ K) :
    featureExponentialMomentWeight β k x ≤ 25 * Real.exp ((β / 2 + 1) * K ^ 2) := by
  have hd : ‖k x‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
  have h4 := Real.pow_div_factorial_le_exp (‖k x‖ ^ 2) (sq_nonneg ‖k x‖) 4
  norm_num at h4
  have hpoly : 1 + (‖k x‖ ^ 2) ^ 4 ≤ 25 * Real.exp (‖k x‖ ^ 2) := by
    nlinarith [Real.one_le_exp (sq_nonneg ‖k x‖)]
  calc
    _ ≤ Real.exp (β * ‖k x‖ ^ 2 / 2) * (25 * Real.exp (‖k x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)
    _ = 25 * Real.exp ((β / 2 + 1) * ‖k x‖ ^ 2) := by
      rw [show (β / 2 + 1) * ‖k x‖ ^ 2 = β * ‖k x‖ ^ 2 / 2 + ‖k x‖ ^ 2 by ring,
        Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd (by positivity))) (by norm_num)

lemma integrable_featureExponentialMomentWeight_of_memLp_top
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hkinf : MemLp k ∞ μ) : Integrable (featureExponentialMomentWeight β k) μ := by
  have hsm : StronglyMeasurable (featureExponentialMomentWeight β k) := by
    have hd := hk.norm.pow 2
    have hr := Real.continuous_exp.comp_stronglyMeasurable ((hd.const_mul β).mul_const (2 : ℝ)⁻¹)
    have hp := (stronglyMeasurable_const (b := (1 : ℝ))).add (hd.pow 4)
    change StronglyMeasurable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) * (1 + (‖k x‖ ^ 2) ^ 4))
    simp only [div_eq_mul_inv]
    exact hr.mul hp
  apply (integrable_const (25 * Real.exp ((β / 2 + 1) * (lpNorm k ∞ μ) ^ 2))).mono' hsm.aestronglyMeasurable
  filter_upwards [ae_le_lpNorm_exponent_top hkinf] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1)
    (one_le_featureExponentialMomentWeight β hβ k x))]
  exact featureExponentialMomentWeight_le_bounded β hβ k _ lpNorm_nonneg x hx

lemma integral_featureExponentialMomentWeight_le_bounded
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hkinf : MemLp k ∞ μ) :
    (∫ x, featureExponentialMomentWeight β k x ∂μ) ≤
      25 * Real.exp ((β / 2 + 1) * (lpNorm k ∞ μ) ^ 2) := by
  have hm := integral_mono_ae (integrable_featureExponentialMomentWeight_of_memLp_top β hβ k hk hkinf)
    (integrable_const (25 * Real.exp ((β / 2 + 1) * (lpNorm k ∞ μ) ^ 2)))
    (by filter_upwards [ae_le_lpNorm_exponent_top hkinf] with x hx using
      featureExponentialMomentWeight_le_bounded β hβ k _ lpNorm_nonneg x hx)
  simpa using hm

lemma feature_bounded_rate_numeric (β M K Z L : ℝ) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hMb : M ≤ 25 * Real.exp ((β / 2 + 1) * K ^ 2)) (N : ℕ) (hN : 1 ≤ N)
    (h : |Z - L| ≤ (26 * β ^ 2 + 12 * β ^ 3) * M ^ 2 / (N : ℝ)) :
    |Z - L| ≤ featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β * K ^ 2) / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hN)
  have hc : 0 ≤ featureBoundedRateConstant β := (featureBoundedRateConstant_pos β hβ).le
  by_cases hz : β = 0
  · subst β
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 3 ≠ 0), mul_zero, zero_mul, zero_add, zero_div] at h
    exact h.trans (by positivity)
  · have hcoef : 0 ≤ 26 * β ^ 2 + 12 * β ^ 3 := by positivity
    have hsq : M ^ 2 ≤ 625 * Real.exp ((β + 2) * K ^ 2) := by
      calc
        M ^ 2 ≤ (25 * Real.exp ((β / 2 + 1) * K ^ 2)) ^ 2 := pow_le_pow_left₀ hM hMb 2
        _ = _ := by
          rw [mul_pow, ← Real.exp_nat_mul _ 2]
          norm_num only [show (25 : ℝ) ^ 2 = 625 by norm_num]
          congr 1
          ring
    have hfactor : 625 * (26 * β ^ 2 + 12 * β ^ 3) ≤ featureBoundedRateConstant β := by
      unfold featureBoundedRateConstant
      have hd : 0 ≤ 2 / β := div_nonneg (by norm_num) hβ
      linarith
    have hexp : β + 2 ≤ featureBoundedRateConstant β * β := by
      have hd : (2 / β) * β = 2 := div_mul_cancel₀ 2 hz
      unfold featureBoundedRateConstant
      nlinarith [mul_nonneg hcoef hβ]
    apply h.trans
    apply div_le_div_of_nonneg_right _ hn.le
    calc
      _ ≤ (26 * β ^ 2 + 12 * β ^ 3) * (625 * Real.exp ((β + 2) * K ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq hcoef
      _ = (625 * (26 * β ^ 2 + 12 * β ^ 3)) * Real.exp ((β + 2) * K ^ 2) := by ring
      _ ≤ featureBoundedRateConstant β * Real.exp ((β + 2) * K ^ 2) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexp (sq_nonneg K))) hc

variable [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace.CountablyGenerated X]

/-- Bounded-feature source rate with actual source spectral data constructed.
The constant depends only on beta, and the norm is the actual essential norm. -/
theorem exists_sourceKernelParticleStatistic_bounded_feature_rate
    (β : ℝ) (hβ : 0 ≤ β) (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (k : X → H) (hk : StronglyMeasurable k) (hkinf : MemLp k ∞ μ)
    (hmean : (∫ x, k x ∂μ) = 0) (heq : h =ᵐ[μ.prod μ] featureKernel k) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic h N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic h N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β * (lpNorm k ∞ μ) ^ 2) / (N : ℝ) := by
  have hM := integrable_featureExponentialMomentWeight_of_memLp_top β hβ k hk hkinf
  obtain ⟨ι, eig, e, hi, he, ha, hs, ht, hRate⟩ :=
    exists_sourceKernelParticleStatistic_feature_rate β hβ h hh k hk hM hmean heq
  refine ⟨ι, eig, e, hi, he, ha, hs, ht, fun N hN => ⟨(hRate N hN).1, ?_⟩⟩
  exact feature_bounded_rate_numeric β _ _ _ _ hβ
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_integral_featureExponentialMomentWeight β hβ k hM))
    (integral_featureExponentialMomentWeight_le_bounded β hβ k hk hkinf) N hN (hRate N hN).2

/-- The original bounded-feature estimate for any ACTUAL complete source
operator eigenbasis, with genuine positive determinant product convergence. -/
theorem sourceKernel_eigenbasis_bounded_feature_rate {κ : Type*}
    (β : ℝ) (hβ : 0 ≤ β) (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (k : X → H) (hk : StronglyMeasurable k) (hkinf : MemLp k ∞ μ)
    (hmean : (∫ x, k x ∂μ) = 0) (heq : h =ᵐ[μ.prod μ] featureKernel k)
    (c : κ → ℝ) (e : HilbertBasis κ ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator h hh (e i) = c i • e i) :
    HasProd (fun i => (1 + β * c i) * Real.exp (-(β * c i)))
      (DGRHS.Kernel.regularizedDet (fun i => β * c i)) ∧
    0 < DGRHS.Kernel.regularizedDet (fun i => β * c i) ∧
    ∀ N : ℕ, 1 ≤ N →
      Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic h N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic h N x)
        ∂Measure.pi (fun _ : Fin N => μ)) -
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * c i)))⁻¹| ≤
        featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β * (lpNorm k ∞ μ) ^ 2) / (N : ℝ) := by
  have hM := integrable_featureExponentialMomentWeight_of_memLp_top β hβ k hk hkinf
  obtain ⟨hP, hD, hRate⟩ := sourceKernel_eigenbasis_feature_rate β hβ h hh k hk hM hmean heq c e he
  refine ⟨hP, hD, fun N hN => ⟨(hRate N hN).1, ?_⟩⟩
  exact feature_bounded_rate_numeric β _ _ _ _ hβ
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_integral_featureExponentialMomentWeight β hβ k hM))
    (integral_featureExponentialMomentWeight_le_bounded β hβ k hk hkinf) N hN (hRate N hN).2

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureBoundedRateConstant
#print axioms DGRHS.Gaussian.featureBoundedRateConstant

#check DGRHS.Gaussian.featureBoundedRateConstant_pos
#print axioms DGRHS.Gaussian.featureBoundedRateConstant_pos

#check DGRHS.Gaussian.featureExponentialMomentWeight_le_bounded
#print axioms DGRHS.Gaussian.featureExponentialMomentWeight_le_bounded

#check DGRHS.Gaussian.integrable_featureExponentialMomentWeight_of_memLp_top
#print axioms DGRHS.Gaussian.integrable_featureExponentialMomentWeight_of_memLp_top

#check DGRHS.Gaussian.integral_featureExponentialMomentWeight_le_bounded
#print axioms DGRHS.Gaussian.integral_featureExponentialMomentWeight_le_bounded

#check DGRHS.Gaussian.feature_bounded_rate_numeric
#print axioms DGRHS.Gaussian.feature_bounded_rate_numeric

#check DGRHS.Gaussian.exists_sourceKernelParticleStatistic_bounded_feature_rate
#print axioms DGRHS.Gaussian.exists_sourceKernelParticleStatistic_bounded_feature_rate

#check DGRHS.Gaussian.sourceKernel_eigenbasis_bounded_feature_rate
#print axioms DGRHS.Gaussian.sourceKernel_eigenbasis_bounded_feature_rate
