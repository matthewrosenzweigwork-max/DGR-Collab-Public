import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import DGPS.Foundations.Entropy

/-!
# Defect removal: scalar tail entropy and small mass inequalities (LIP080)

* `DGPS.Analysis.scalar_tail_entropy_inequality`: for every `η > 0` there is `C` with
  `s² log s² - M² log M² ≤ (1+η)(s-M)² log⁺((s-M)²) + C s² log M²` for `M ≥ e`, `s > M`.
* `DGPS.Analysis.small_mass_posLog_le_entropy`: if `c = ∫ t² ≤ e⁻¹` (`t²` integrable, `P`
  probability), then `∫ t² log⁺ t² ≤ Ent_P(t²)` (including `c = 0`); stated with the lower
  integral, which also covers the non-integrable case.
* `DGPS.Analysis.scalar_tail_entropy_and_small_mass_inequalities`: the packet interface,
  the conjunction of both.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Analysis

open Real

/-- Part one of LIP080, the scalar tail inequality. -/
theorem scalar_tail_entropy_inequality (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ M : ℝ, Real.exp 1 ≤ M → ∀ s : ℝ, M < s →
      s ^ 2 * Real.log (s ^ 2) - M ^ 2 * Real.log (M ^ 2)
        ≤ (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2)
          + C * s ^ 2 * Real.log (M ^ 2) := by
  set β : ℝ := η / (2 * (1 + η)) with hβdef
  have h1η : 0 < 1 + η := by linarith
  have hβ0 : 0 < β := by positivity
  have hβ2 : β * (2 * (1 + η)) = η := by rw [hβdef]; field_simp
  have hβ1 : β < 1 / 2 := by nlinarith
  have hkey : 1 ≤ (1 + η) * (1 - β) ^ 2 := by nlinarith [sq_nonneg β]
  set LA : ℝ := -Real.log β with hLA
  have hLA0 : 0 ≤ LA := by
    have := Real.log_nonpos hβ0.le (by linarith); rw [hLA]; linarith
  set Lc : ℝ := -Real.log (1 - β) with hLc
  have hLc0 : 0 ≤ Lc := by
    have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - β) (by linarith); rw [hLc]; linarith
  refine ⟨1 + LA + Lc, fun M hM s hs => ?_⟩
  have hMe : (1:ℝ) ≤ M := by
    have := Real.add_one_le_exp 1; linarith
  have hM0 : 0 < M := by linarith
  have hs0 : 0 < s := by linarith
  have hlogM : 1 ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le hM0]; exact hM
  have hL : Real.log (M ^ 2) = 2 * Real.log M := by
    rw [Real.log_pow]; push_cast; ring
  have hL2 : 2 ≤ Real.log (M ^ 2) := by rw [hL]; linarith
  have hLs : Real.log (s ^ 2) = 2 * Real.log s := by
    rw [Real.log_pow]; push_cast; ring
  set L := Real.log (M ^ 2) with hLdef
  have hpos : 0 ≤ (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) :=
    mul_nonneg (mul_nonneg h1η.le (sq_nonneg _)) Real.posLog_nonneg
  have hML : 0 ≤ M ^ 2 * L := mul_nonneg (sq_nonneg _) (by linarith)
  have hsL : 0 ≤ s ^ 2 * L := mul_nonneg (sq_nonneg _) (by linarith)
  have hcom : 2 * LA * s ^ 2 ≤ LA * s ^ 2 * L := by
    have := mul_nonneg (mul_nonneg hLA0 (sq_nonneg s)) (sub_nonneg.2 hL2); nlinarith
  have hcom2 : 2 * Lc * s ^ 2 ≤ Lc * s ^ 2 * L := by
    have := mul_nonneg (mul_nonneg hLc0 (sq_nonneg s)) (sub_nonneg.2 hL2); nlinarith
  by_cases hcase : s ≤ M / β
  · -- moderate range
    have hlogs : Real.log s ≤ Real.log M + LA := by
      have h := Real.log_le_log hs0 hcase
      rw [Real.log_div hM0.ne' hβ0.ne'] at h; rw [hLA]; linarith
    have h2 : s ^ 2 * Real.log (s ^ 2) ≤ s ^ 2 * (L + 2 * LA) := by
      rw [hLs, hL]
      exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg s)
    have h3 : 0 ≤ Lc * (s ^ 2 * L) := mul_nonneg hLc0 hsL
    have h8 : (1 + LA + Lc) * s ^ 2 * L = s ^ 2 * L + LA * s ^ 2 * L + Lc * (s ^ 2 * L) := by ring
    have h9 : s ^ 2 * (L + 2 * LA) = s ^ 2 * L + 2 * LA * s ^ 2 := by ring
    linarith
  · push Not at hcase
    have hMs : M < β * s := by rwa [div_lt_iff₀ hβ0, mul_comm] at hcase
    have hs2 : 2 ≤ s := by
      have : M / β > 2 * M := by
        rw [gt_iff_lt, lt_div_iff₀ hβ0]; nlinarith
      linarith
    have hu : (1 - β) * s ≤ s - M := by nlinarith
    have hu1 : 1 ≤ (1 - β) * s := by nlinarith
    have hu2 : ((1 - β) * s) ^ 2 ≤ (s - M) ^ 2 := by
      exact pow_le_pow_left₀ (by linarith) hu 2
    set X : ℝ := Real.log (((1 - β) * s) ^ 2) with hX
    have hX0 : 0 ≤ X := Real.log_nonneg (by nlinarith)
    have hXle : X ≤ Real.posLog ((s - M) ^ 2) := by
      refine le_trans ?_ (le_max_right _ _)
      rw [hX]
      exact Real.log_le_log (by positivity) hu2
    have hXeq : X = Real.log (s ^ 2) - 2 * Lc := by
      rw [hX, Real.log_pow, Real.log_mul (by linarith) hs0.ne', hLc, hLs]; push_cast; ring
    have h4 : ((1 - β) * s) ^ 2 * X ≤ (s - M) ^ 2 * Real.posLog ((s - M) ^ 2) :=
      mul_le_mul hu2 hXle hX0 (sq_nonneg _)
    have h5 : s ^ 2 * X ≤ (1 + η) * ((1 - β) * s) ^ 2 * X := by
      have : s ^ 2 ≤ (1 + η) * ((1 - β) * s) ^ 2 := by nlinarith [sq_nonneg s]
      exact mul_le_mul_of_nonneg_right this hX0
    have h6 : (1 + η) * (((1 - β) * s) ^ 2 * X)
        ≤ (1 + η) * ((s - M) ^ 2 * Real.posLog ((s - M) ^ 2)) :=
      mul_le_mul_of_nonneg_left h4 h1η.le
    have h7 : 0 ≤ (1 + LA) * (s ^ 2 * L) := mul_nonneg (by linarith) hsL
    have h9 : s ^ 2 * X = s ^ 2 * Real.log (s ^ 2) - 2 * Lc * s ^ 2 := by rw [hXeq]; ring
    have h8 : (1 + LA + Lc) * s ^ 2 * L = s ^ 2 * L + LA * s ^ 2 * L + Lc * s ^ 2 * L := by ring
    have h10 : (1 + η) * (((1 - β) * s) ^ 2 * X) = (1 + η) * ((1 - β) * s) ^ 2 * X := by ring
    have h11 : (1 + LA) * (s ^ 2 * L) = s ^ 2 * L + LA * s ^ 2 * L := by ring
    have h12 : (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2)
        = (1 + η) * ((s - M) ^ 2 * Real.posLog ((s - M) ^ 2)) := by ring
    linarith

/-- The pointwise inequality `x log⁺ x ≤ x log (x / c) - x + c` for `0 < c ≤ e⁻¹`, `x ≥ 0`. -/
theorem mul_posLog_le_entropyIntegrand {c x : ℝ} (hc : 0 < c) (hc1 : c ≤ Real.exp (-1))
    (hx : 0 ≤ x) : x * Real.posLog x ≤ DGPS.entropyIntegrand c x := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0; simp [DGPS.entropyIntegrand, hc.le]
  by_cases h1 : x ≤ 1
  · have : Real.posLog x = 0 := (Real.posLog_eq_zero_iff x).2 (by rw [abs_of_nonneg hx]; exact h1)
    rw [this, mul_zero]; exact DGPS.entropyIntegrand_nonneg hc hx
  · push Not at h1
    rw [Real.posLog_eq_log (by rw [abs_of_nonneg hx]; exact h1.le)]
    have hlc : Real.log c ≤ -1 := (Real.log_le_iff_le_exp hc).2 hc1
    unfold DGPS.entropyIntegrand
    rw [Real.log_div hpos.ne' hc.ne']
    nlinarith [mul_nonneg hpos.le (by linarith : 0 ≤ -Real.log c - 1)]

/-- Part two of LIP080, the small-mass inequality. -/
theorem small_mass_posLog_le_entropy {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (t : α → ℝ) (_ht : ∀ x, 0 ≤ t x)
    (hint : Integrable (fun x => t x ^ 2) P)
    (hc : ∫ x, t x ^ 2 ∂P ≤ Real.exp (-1)) :
    ∫⁻ x, ENNReal.ofReal (t x ^ 2 * Real.posLog (t x ^ 2)) ∂P
      ≤ DGPS.homogeneousEntropy P (fun x => t x ^ 2) := by
  have hnn : 0 ≤ ∫ x, t x ^ 2 ∂P := integral_nonneg (fun x => sq_nonneg _)
  rcases hnn.eq_or_lt with h0 | hpos
  · rw [DGPS.homogeneousEntropy_of_integral_eq_zero h0.symm]
    have hae : (fun x => t x ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).1 h0.symm
    have : ∫⁻ x, ENNReal.ofReal (t x ^ 2 * Real.posLog (t x ^ 2)) ∂P = 0 := by
      rw [← lintegral_zero (μ := P)]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      have : t x ^ 2 = 0 := hx
      simp [this]
    rw [this]
  · rw [DGPS.homogeneousEntropy_of_integral_ne_zero hpos.ne']
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    exact mul_posLog_le_entropyIntegrand hpos hc (sq_nonneg _)

/-- LIP080: scalar tail entropy and small mass inequalities. -/
theorem scalar_tail_entropy_and_small_mass_inequalities {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P] :
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ M : ℝ, Real.exp 1 ≤ M → ∀ s : ℝ, M < s →
      s ^ 2 * Real.log (s ^ 2) - M ^ 2 * Real.log (M ^ 2)
        ≤ (1 + η) * (s - M) ^ 2 * Real.posLog ((s - M) ^ 2)
          + C * s ^ 2 * Real.log (M ^ 2)) ∧
    (∀ t : α → ℝ, (∀ x, 0 ≤ t x) → Integrable (fun x => t x ^ 2) P →
      ∫ x, t x ^ 2 ∂P ≤ Real.exp (-1) →
      ∫⁻ x, ENNReal.ofReal (t x ^ 2 * Real.posLog (t x ^ 2)) ∂P
        ≤ DGPS.homogeneousEntropy P (fun x => t x ^ 2)) :=
  ⟨scalar_tail_entropy_inequality, fun t ht hint hc => small_mass_posLog_le_entropy P t ht hint hc⟩

end DGPS.Analysis
