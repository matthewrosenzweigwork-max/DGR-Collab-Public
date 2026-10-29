import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import DGPS.Foundations.Entropy
import DGPS.Basic.DefectRemoval
import DGPS.Basic.VanishingEntropyDeviations

/-!
# Vanishing entropy: Taylor inequality and tightening (LIP083)

With `Φ(s) = s² log s² - s² + 1`, `g = min s A0` and `t = (s - A0)⁺` one has pointwise
`Φ(s) ≤ 2(1+log A0)(g-1)² + t² log⁺ t² + 2(1+log(A0+1)) t² + Φ'(A0) t`
(`entropyIntegrand_le_split`), integrated in `entropy_le_split_integrals` using the Poincaré
inequality for `g`, the small-mass bound and defective inequality for `t` (LIP080).

* `DGPS.Analysis.vanishing_entropy_taylor_inequality_and_tightening`: under `TighteningHyp`
  (LIP079) and energy splitting for the truncation `f = f ∧ c + (f - c)⁺`, a normalized violating
  sequence of LIP079 (with `n k → ∞`) cannot have `h k → 0` (uses LIP082).
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Analysis

/-- A one-sided second-order Taylor upper bound from a second derivative bound. -/
theorem taylor_upper_of_second_deriv_le (φ φ' φ'' : ℝ → ℝ) {a b K : ℝ} (hab : a ≤ b)
    (h1 : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x)
    (h2 : ∀ x ∈ Icc a b, HasDerivAt φ' (φ'' x) x)
    (hK : ∀ x ∈ Icc a b, φ'' x ≤ 2 * K) :
    φ b ≤ φ a + φ' a * (b - a) + K * (b - a) ^ 2 := by
  have hξ : MonotoneOn (fun x => φ' a + 2 * K * (x - a) - φ' x) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      exact ((continuousAt_const.add (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))).sub
        (h2 x hx).continuousAt).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have h3 : HasDerivAt (fun x => φ' a + 2 * K * (x - a) - φ' x) (2 * K * 1 - φ'' x) x := by
        have e1 : HasDerivAt (fun x => x - a) 1 x := (hasDerivAt_id x).sub_const a
        exact ((e1.const_mul (2 * K)).const_add (φ' a)).sub (h2 x (Ioo_subset_Icc_self hx))
      exact h3.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have h3 : HasDerivAt (fun x => φ' a + 2 * K * (x - a) - φ' x) (2 * K * 1 - φ'' x) x := by
        have e1 : HasDerivAt (fun x => x - a) 1 x := (hasDerivAt_id x).sub_const a
        exact ((e1.const_mul (2 * K)).const_add (φ' a)).sub (h2 x (Ioo_subset_Icc_self hx))
      rw [h3.deriv]
      have := hK x (Ioo_subset_Icc_self hx)
      linarith
  have hθ : MonotoneOn (fun x => φ a + φ' a * (x - a) + K * (x - a) ^ 2 - φ x) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      have := (h1 x hx).continuousAt
      exact ((continuousAt_const.add (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
        |>.add (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).pow 2))).sub
        this).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have h3 : HasDerivAt (fun x => φ a + φ' a * (x - a) + K * (x - a) ^ 2 - φ x)
          (φ' a * 1 + K * (2 * (x - a) * 1) - φ' x) x := by
        have e1 : HasDerivAt (fun x => x - a) 1 x := (hasDerivAt_id x).sub_const a
        exact (((e1.const_mul (φ' a)).const_add (φ a)).add ((e1.pow 2).const_mul K)).sub
          (h1 x (Ioo_subset_Icc_self hx)) |>.congr_deriv (by simp)
      exact h3.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have h3 : HasDerivAt (fun x => φ a + φ' a * (x - a) + K * (x - a) ^ 2 - φ x)
          (φ' a * 1 + K * (2 * (x - a) * 1) - φ' x) x := by
        have e1 : HasDerivAt (fun x => x - a) 1 x := (hasDerivAt_id x).sub_const a
        exact (((e1.const_mul (φ' a)).const_add (φ a)).add ((e1.pow 2).const_mul K)).sub
          (h1 x (Ioo_subset_Icc_self hx)) |>.congr_deriv (by simp)
      rw [h3.deriv]
      have hx' := hξ (left_mem_Icc.2 hab) (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hx).1
      simp only [sub_self, mul_zero, add_zero] at hx'
      linarith
  have := hθ (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at this
  linarith


/-- The entropy profile `Φ(s) = 2 s² log s - s² + 1`. -/
noncomputable def entropyProfile (x : ℝ) : ℝ := 2 * x ^ 2 * Real.log x - x ^ 2 + 1

theorem entropyProfile_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt entropyProfile (4 * x * Real.log x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x ^ 2 * Real.log x)
      (2 * (2 * x) * Real.log x + 2 * x ^ 2 * x⁻¹) x := by
    have := ((hasDerivAt_pow 2 x).const_mul 2).mul (Real.hasDerivAt_log hx.ne')
    refine this.congr_deriv ?_
    simp
  have h2 := (h1.sub (hasDerivAt_pow 2 x)).add_const 1
  refine h2.congr_deriv ?_
  field_simp
  push_cast
  ring

theorem entropyProfile_deriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => 4 * x * Real.log x) (4 * Real.log x + 4) x := by
  have := ((hasDerivAt_id x).const_mul 4).mul (Real.hasDerivAt_log hx.ne')
  refine this.congr_deriv ?_
  field_simp
  simp
  ring

theorem entropyProfile_eq {s : ℝ} :
    DGPS.entropyIntegrand 1 (s ^ 2) = entropyProfile s := by
  have hl : Real.log (s ^ 2) = 2 * Real.log s := by
    rw [Real.log_pow]; push_cast; ring
  simp only [DGPS.entropyIntegrand, div_one, hl, entropyProfile]
  ring

theorem entropyProfile_one : entropyProfile 1 = 0 := by simp [entropyProfile]

theorem entropyProfile_le_quad {A0 : ℝ} (hA : 1 < A0) {s : ℝ} (hs : 0 ≤ s) (hsA : s ≤ A0) :
    entropyProfile s ≤ 2 * (1 + Real.log A0) * (s - 1) ^ 2 := by
  have hL : 0 ≤ Real.log A0 := Real.log_nonneg hA.le
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    simp only [entropyProfile]
    norm_num
    linarith
  rcases le_or_gt 1 s with h1 | h1
  · have := taylor_upper_of_second_deriv_le entropyProfile (fun x => 4 * x * Real.log x)
      (fun x => 4 * Real.log x + 4) (a := 1) (b := s) (K := 2 * (1 + Real.log A0)) h1
      (fun x hx => entropyProfile_hasDerivAt (by linarith [hx.1]))
      (fun x hx => entropyProfile_deriv_hasDerivAt (by linarith [hx.1]))
      (fun x hx => by
        have hx0 : 0 < x := by linarith [hx.1]
        have : Real.log x ≤ Real.log A0 := Real.log_le_log hx0 (by linarith [hx.2])
        linarith)
    simp only [entropyProfile_one, Real.log_one, mul_zero, zero_mul, zero_add] at this
    linarith
  · -- reflect
    have hψ1 : ∀ x ∈ Icc (0:ℝ) (1 - s), HasDerivAt (fun x => entropyProfile (1 - x))
        (-(4 * (1 - x) * Real.log (1 - x))) x := by
      intro x hx
      have hx0 : 0 < 1 - x := by linarith [hx.2]
      have := (entropyProfile_hasDerivAt hx0).comp x ((hasDerivAt_id x).const_sub 1)
      refine this.congr_deriv ?_
      simp
    have hψ2 : ∀ x ∈ Icc (0:ℝ) (1 - s), HasDerivAt (fun x => -(4 * (1 - x) * Real.log (1 - x)))
        (4 * Real.log (1 - x) + 4) x := by
      intro x hx
      have hx0 : 0 < 1 - x := by linarith [hx.2]
      have := (entropyProfile_deriv_hasDerivAt hx0).comp x ((hasDerivAt_id x).const_sub 1)
      have := this.neg
      refine this.congr_deriv ?_
      simp
    have := taylor_upper_of_second_deriv_le (fun x => entropyProfile (1 - x))
      (fun x => -(4 * (1 - x) * Real.log (1 - x))) (fun x => 4 * Real.log (1 - x) + 4)
      (a := 0) (b := 1 - s) (K := 2 * (1 + Real.log A0)) (by linarith) hψ1 hψ2
      (fun x hx => by
        have hx0 : 0 < 1 - x := by linarith [hx.2]
        have : Real.log (1 - x) ≤ 0 := Real.log_nonpos hx0.le (by linarith [hx.1])
        linarith)
    simp only [sub_zero, sub_sub_cancel, entropyProfile_one, Real.log_one, mul_zero, zero_mul,
      neg_zero, zero_add] at this
    nlinarith [this]


theorem entropyProfile_le_tail {A0 : ℝ} (hA : 1 < A0) {t : ℝ} (ht : 0 ≤ t) :
    entropyProfile (A0 + t) ≤ entropyProfile A0 + 4 * A0 * Real.log A0 * t
      + 2 * (1 + Real.log (A0 + 1) + Real.posLog t) * t ^ 2 := by
  have hA0 : 0 < A0 := by linarith
  have := taylor_upper_of_second_deriv_le entropyProfile (fun x => 4 * x * Real.log x)
      (fun x => 4 * Real.log x + 4) (a := A0) (b := A0 + t)
      (K := 2 * (1 + Real.log (A0 + 1) + Real.posLog t)) (by linarith)
      (fun x hx => entropyProfile_hasDerivAt (by linarith [hx.1]))
      (fun x hx => entropyProfile_deriv_hasDerivAt (by linarith [hx.1]))
      (fun x hx => by
        have hx0 : 0 < x := by linarith [hx.1]
        have h1 : x ≤ (A0 + 1) * max 1 t := by
          have h2 : 1 ≤ max 1 t := le_max_left _ _
          have h3 : t ≤ max 1 t := le_max_right _ _
          nlinarith [hx.2]
        have h4 : Real.log x ≤ Real.log (A0 + 1) + Real.posLog t := by
          calc Real.log x ≤ Real.log ((A0 + 1) * max 1 t) := Real.log_le_log hx0 h1
            _ = Real.log (A0 + 1) + Real.log (max 1 t) := by
              rw [Real.log_mul (by linarith) (by positivity)]
            _ = _ := by rw [Real.posLog_eq_log_max_one ht]
        linarith)
  have e : A0 + t - A0 = t := by ring
  rw [e] at this
  linarith

/-- The pointwise Taylor inequality of LIP083. -/
theorem entropyIntegrand_le_split {A0 : ℝ} (hA : 1 < A0) {s : ℝ} (hs : 0 ≤ s) :
    DGPS.entropyIntegrand 1 (s ^ 2)
      ≤ 2 * (1 + Real.log A0) * (min s A0 - 1) ^ 2
        + (max (s - A0) 0) ^ 2 * Real.posLog ((max (s - A0) 0) ^ 2)
        + 2 * (1 + Real.log (A0 + 1)) * (max (s - A0) 0) ^ 2
        + 4 * A0 * Real.log A0 * max (s - A0) 0 := by
  have hL : 0 ≤ Real.log A0 := Real.log_nonneg hA.le
  have hL1 : 0 ≤ Real.log (A0 + 1) := Real.log_nonneg (by linarith)
  rw [entropyProfile_eq]
  rcases le_total s A0 with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), Real.posLog_pow]
    have := entropyProfile_le_quad hA hs h
    simp only [Real.posLog_zero]
    nlinarith
  · rw [min_eq_right h, max_eq_left (by linarith)]
    have ht : 0 ≤ s - A0 := by linarith
    have h1 := entropyProfile_le_tail hA ht
    have h2 := entropyProfile_le_quad hA (by linarith : 0 ≤ A0) le_rfl
    have e : A0 + (s - A0) = s := by ring
    rw [e] at h1
    have h3 : Real.posLog ((s - A0) ^ 2) = 2 * Real.posLog (s - A0) := by
      rw [Real.posLog_pow]; push_cast; ring
    rw [h3]
    nlinarith


/-- Integrated form of the pointwise Taylor inequality for a single test. -/
theorem entropy_le_split_integrals {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {h A0 r0 C Eg Et : ℝ} (hm : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) (hsi : Integrable (fun x => f x ^ 2) P) (hmass : ∫ x, f x ^ 2 ∂P = 1)
    (hent : homogeneousEntropy P (fun x => f x ^ 2) = ENNReal.ofReal h) (hA : 1 < A0)
    (hr0 : 0 < r0) (hEt : 0 ≤ Et)
    (hPoin : r0 * (∫ x, (min (f x) A0) ^ 2 ∂P - (∫ x, min (f x) A0 ∂P) ^ 2) ≤ Eg)
    (hdef : homogeneousEntropy P (fun x => (max (f x - A0) 0) ^ 2)
      ≤ ENNReal.ofReal (2 * Et / r0 + C * ∫ x, (max (f x - A0) 0) ^ 2 ∂P))
    (hsmall : ∫ x, (max (f x - A0) 0) ^ 2 ∂P ≤ Real.exp (-1)) :
    h ≤ 2 * (1 + Real.log A0) * (Eg / r0 + (∫ x, min (f x) A0 ∂P - 1) ^ 2)
      + (2 * Et / r0 + |C| * ∫ x, (max (f x - A0) 0) ^ 2 ∂P)
      + 2 * (1 + Real.log (A0 + 1)) * ∫ x, (max (f x - A0) 0) ^ 2 ∂P
      + 4 * A0 * Real.log A0 * ∫ x, max (f x - A0) 0 ∂P := by
  have hL : 0 ≤ Real.log A0 := Real.log_nonneg hA.le
  have hL1 : 0 ≤ Real.log (A0 + 1) := Real.log_nonneg (by linarith)
  have hA0 : 0 < A0 := by linarith
  -- measurability and integrability
  have htm : Measurable fun x => max (f x - A0) 0 := (hm.sub_const A0).max measurable_const
  have hgm : Measurable fun x => min (f x) A0 := hm.min measurable_const
  have ht0 : ∀ x, 0 ≤ max (f x - A0) 0 := fun x => le_max_right _ _
  have htle : ∀ x, max (f x - A0) 0 ≤ f x := fun x => max_le (by linarith) (hnn x)
  have hg0 : ∀ x, 0 ≤ min (f x) A0 := fun x => le_min (hnn x) hA0.le
  have hgA : ∀ x, min (f x) A0 ≤ A0 := fun x => min_le_right _ _
  have hti : Integrable (fun x => max (f x - A0) 0) P := by
    refine Integrable.mono' (hsi.add (integrable_const (1 : ℝ))) htm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ht0 x)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f x - 1), htle x]
  have hti2 : Integrable (fun x => (max (f x - A0) 0) ^ 2) P := by
    refine Integrable.mono' hsi (htm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (ht0 x) (htle x) 2
  have hgi : Integrable (fun x => min (f x) A0) P :=
    Integrable.of_bound hgm.aestronglyMeasurable A0 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgA x)
  have hgi2 : Integrable (fun x => (min (f x) A0) ^ 2) P :=
    Integrable.of_bound (hgm.pow_const 2).aestronglyMeasurable (A0 ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hg0 x) (hgA x) 2)
  have hgi3 : Integrable (fun x => (min (f x) A0 - 1) ^ 2) P := by
    have e : (fun x => (min (f x) A0 - 1) ^ 2)
        = fun x => (min (f x) A0) ^ 2 - 2 * min (f x) A0 + 1 := by funext x; ring
    rw [e]
    exact (hgi2.sub (hgi.const_mul 2)).add (integrable_const _)
  -- the small mass bound for the tail
  have hsm := small_mass_posLog_le_entropy P (fun x => max (f x - A0) 0) ht0 hti2 hsmall
  set u : Ω → ℝ := fun x => (max (f x - A0) 0) ^ 2 * Real.posLog ((max (f x - A0) 0) ^ 2) with hu
  have hum : Measurable u := by
    refine (htm.pow_const 2).mul ?_
    exact Real.continuous_posLog.measurable.comp (htm.pow_const 2)
  have hu0 : ∀ x, 0 ≤ u x := fun x => mul_nonneg (sq_nonneg _) Real.posLog_nonneg
  have hX : 0 ≤ 2 * Et / r0 + |C| * ∫ x, (max (f x - A0) 0) ^ 2 ∂P := by
    have : 0 ≤ ∫ x, (max (f x - A0) 0) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
    positivity
  have hle : ∫⁻ x, ENNReal.ofReal (u x) ∂P
      ≤ ENNReal.ofReal (2 * Et / r0 + |C| * ∫ x, (max (f x - A0) 0) ^ 2 ∂P) := by
    refine hsm.trans (hdef.trans (ENNReal.ofReal_le_ofReal ?_))
    have : C * ∫ x, (max (f x - A0) 0) ^ 2 ∂P ≤ |C| * ∫ x, (max (f x - A0) 0) ^ 2 ∂P :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (integral_nonneg fun x => sq_nonneg _)
    linarith
  have hui : Integrable u P := by
    refine ⟨hum.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hu0)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  have hu_int : ∫ x, u x ∂P ≤ 2 * Et / r0 + |C| * ∫ x, (max (f x - A0) 0) ^ 2 ∂P := by
    rw [← ENNReal.ofReal_le_ofReal_iff hX, ofReal_integral_eq_lintegral_ofReal hui
      (Filter.Eventually.of_forall hu0)]
    exact hle
  -- the integrated pointwise bound
  set K1 := 2 * (1 + Real.log A0) with hK1
  set K2 := 2 * (1 + Real.log (A0 + 1)) with hK2
  set K3 := 4 * A0 * Real.log A0 with hK3
  have hΨi : Integrable (fun x => K1 * (min (f x) A0 - 1) ^ 2 + u x
      + K2 * (max (f x - A0) 0) ^ 2 + K3 * max (f x - A0) 0) P :=
    (((hgi3.const_mul K1).add hui).add (hti2.const_mul K2)).add (hti.const_mul K3)
  have hΨ0 : ∀ x, 0 ≤ K1 * (min (f x) A0 - 1) ^ 2 + u x
      + K2 * (max (f x - A0) 0) ^ 2 + K3 * max (f x - A0) 0 := by
    intro x
    have : 0 ≤ K1 := by rw [hK1]; positivity
    have : 0 ≤ K2 := by rw [hK2]; positivity
    have : 0 ≤ K3 := by rw [hK3]; positivity
    have := hu0 x
    have := ht0 x
    positivity
  have hhle : ENNReal.ofReal h ≤ ENNReal.ofReal (∫ x, K1 * (min (f x) A0 - 1) ^ 2 + u x
      + K2 * (max (f x - A0) 0) ^ 2 + K3 * max (f x - A0) 0 ∂P) := by
    rw [← hent, homogeneousEntropy_of_integral_ne_zero (by rw [hmass]; exact one_ne_zero), hmass,
      ofReal_integral_eq_lintegral_ofReal hΨi (Filter.Eventually.of_forall hΨ0)]
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    have := entropyIntegrand_le_split hA (hnn x)
    exact this
  have hint0 : 0 ≤ ∫ x, K1 * (min (f x) A0 - 1) ^ 2 + u x
      + K2 * (max (f x - A0) 0) ^ 2 + K3 * max (f x - A0) 0 ∂P :=
    integral_nonneg hΨ0
  have hh1 := (ENNReal.ofReal_le_ofReal_iff hint0).mp hhle
  have hs1 : Integrable (fun x => K1 * (min (f x) A0 - 1) ^ 2 + u x) P :=
    (hgi3.const_mul K1).add hui
  have hs2 : Integrable (fun x => K1 * (min (f x) A0 - 1) ^ 2 + u x
      + K2 * (max (f x - A0) 0) ^ 2) P := hs1.add (hti2.const_mul K2)
  rw [integral_add (f := fun x => K1 * (min (f x) A0 - 1) ^ 2 + u x
      + K2 * (max (f x - A0) 0) ^ 2) (g := fun x => K3 * max (f x - A0) 0) hs2
      (hti.const_mul K3),
    integral_add (f := fun x => K1 * (min (f x) A0 - 1) ^ 2 + u x)
      (g := fun x => K2 * (max (f x - A0) 0) ^ 2) hs1 (hti2.const_mul K2),
    integral_add (f := fun x => K1 * (min (f x) A0 - 1) ^ 2) (g := u) (hgi3.const_mul K1) hui,
    integral_const_mul, integral_const_mul, integral_const_mul] at hh1
  -- variance and Poincare for g
  have hvar : ∫ x, (min (f x) A0 - 1) ^ 2 ∂P
      = (∫ x, (min (f x) A0) ^ 2 ∂P - (∫ x, min (f x) A0 ∂P) ^ 2)
        + (∫ x, min (f x) A0 ∂P - 1) ^ 2 := by
    have e : (fun x => (min (f x) A0 - 1) ^ 2)
        = fun x => ((min (f x) A0) ^ 2 - 2 * min (f x) A0) + 1 := by funext x; ring
    rw [e, integral_add (f := fun x => (min (f x) A0) ^ 2 - 2 * min (f x) A0)
      (g := fun _ => (1 : ℝ)) (hgi2.sub (hgi.const_mul 2)) (integrable_const _),
      integral_sub (f := fun x => (min (f x) A0) ^ 2) (g := fun x => 2 * min (f x) A0) hgi2
      (hgi.const_mul 2), integral_const_mul]
    simp
    ring
  have hvarle : ∫ x, (min (f x) A0 - 1) ^ 2 ∂P
      ≤ Eg / r0 + (∫ x, min (f x) A0 ∂P - 1) ^ 2 := by
    rw [hvar]
    have : (∫ x, (min (f x) A0) ^ 2 ∂P - (∫ x, min (f x) A0 ∂P) ^ 2) ≤ Eg / r0 := by
      rw [le_div_iff₀ hr0]; linarith
    linarith
  have hK1nn : 0 ≤ K1 := by rw [hK1]; positivity
  have := mul_le_mul_of_nonneg_left hvarle hK1nn
  linarith


/-- LIP083.  Under the abstract tightening hypotheses and energy splitting for truncations
(`E (f ∧ c) + E ((f - c)⁺) ≤ E f`), a sequence of nonnegative mass-one tests `f k ∈ S (n k)`,
`n k → ∞`, with `Ent (f k ^ 2) = h k > 0`, `2 E (f k) < r h k` cannot have `h k → 0`. -/
theorem vanishing_entropy_taylor_inequality_and_tightening
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R)
    (hsplit : ∀ n, ∀ f ∈ S n, (∀ x, 0 ≤ f x) → ∀ c : ℝ, 0 ≤ c →
      E n (fun x => min (f x) c) + E n (fun x => max (f x - c) 0) ≤ E n f)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (f : ∀ k, Ω (n k) → ℝ) (h : ℕ → ℝ)
    (hf : ∀ k, f k ∈ S (n k) ∧ (∀ x, 0 ≤ f k x) ∧ ∫ x, f k x ^ 2 ∂P (n k) = 1 ∧
      homogeneousEntropy (P (n k)) (fun x => f k x ^ 2) = ENNReal.ofReal (h k) ∧ 0 < h k ∧
      2 * E (n k) (f k) < r * h k)
    (hh : Tendsto h atTop (𝓝 0)) : False := by
  obtain ⟨-, -, -, -, htail⟩ :=
    vanishing_entropy_normalized_deviations_and_tail_estimates hyp hr hrR n f h hf hh
  set ρ1 : ℝ := r + (R - r) / 3 with hρ1def
  set r0 : ℝ := r + 2 * (R - r) / 3 with hr0def
  have hρ1r : r < ρ1 := by rw [hρ1def]; linarith
  have hρ1r0 : ρ1 < r0 := by rw [hρ1def, hr0def]; linarith
  have hr0R : r0 < R := by rw [hr0def]; linarith
  have hρ1pos : 0 < ρ1 := by linarith
  have hr0pos : 0 < r0 := by linarith
  set A0 : ℝ := Real.exp (r0 / ρ1 - 1) with hA0def
  have hA : 1 < A0 := Real.one_lt_exp_iff.2 (sub_pos.2 ((one_lt_div hρ1pos).2 hρ1r0))
  have hA0pos : 0 < A0 := by linarith
  have hL : Real.log A0 = r0 / ρ1 - 1 := Real.log_exp _
  obtain ⟨C, hC⟩ := hyp.defective r0 hr0pos hr0R
  obtain ⟨N0, hN0⟩ := hyp.poincare r0 hr0R
  obtain ⟨hT2, hT1, hTg⟩ := htail A0 hA
  set K1 : ℝ := 2 * (1 + Real.log A0) with hK1
  set K2 : ℝ := 2 * (1 + Real.log (A0 + 1)) with hK2
  set K3 : ℝ := 4 * A0 * Real.log A0 with hK3
  set a : ℕ → ℝ := fun k => (∫ x, (max (f k x - A0) 0) ^ 2 ∂P (n k)) / h k with ha
  set b : ℕ → ℝ := fun k => (∫ x, max (f k x - A0) 0 ∂P (n k)) / h k with hb
  set d : ℕ → ℝ := fun k => (∫ x, min (f k x) A0 ∂P (n k) - 1) ^ 2 / h k with hd
  set ε : ℕ → ℝ := fun k => K1 * d k + (|C| + K2) * a k + K3 * b k with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := (((hTg.const_mul K1).add (hT2.const_mul (|C| + K2))).add (hT1.const_mul K3))
    simpa using this
  have hη : 0 < 1 - r / ρ1 := by
    rw [sub_pos, div_lt_one hρ1pos]; exact hρ1r
  have hev1 : ∀ᶠ k in atTop, ε k < 1 - r / ρ1 := hε.eventually (gt_mem_nhds hη)
  have hsm : ∀ᶠ k in atTop, ∫ x, (max (f k x - A0) 0) ^ 2 ∂P (n k) ≤ Real.exp (-1) := by
    have h1 : Tendsto (fun k => a k * h k) atTop (𝓝 0) := by simpa using hT2.mul hh
    have h2 : ∀ k, a k * h k = ∫ x, (max (f k x - A0) 0) ^ 2 ∂P (n k) := fun k => by
      simp only [ha]; exact div_mul_cancel₀ _ (hf k).2.2.2.2.1.ne'
    simp only [h2] at h1
    exact h1.eventually (ge_mem_nhds (Real.exp_pos _))
  have hnev : ∀ᶠ k in atTop, N0 ≤ n k := hn.eventually_ge_atTop N0
  refine (hev1.and (hsm.and hnev)).exists.elim fun k ⟨hk1, hk2, hk3⟩ => ?_
  obtain ⟨hfS, hnn, hmass, hent, hpos, hlt⟩ := hf k
  have hm := hyp.measurable _ _ hfS
  have hsi := hyp.sq_integrable _ _ hfS
  have hgS : (fun x => min (f k x) A0) ∈ S (n k) := hyp.min_mem _ _ hfS A0
  have htS : (fun x => max (f k x - A0) 0) ∈ S (n k) := by
    have h1 := hyp.affine_mem (n k) _ hfS 1 (-A0)
    have h2 := hyp.max_mem (n k) _ h1 0
    convert h2 using 2
    congr 1; ring
  have hPoin := hN0 (n k) hk3 _ hgS
  have hdef := hC (n k) _ htS
  have hEt := hyp.energy_nonneg (n k) _ htS
  have hEs := hsplit (n k) _ hfS hnn A0 hA0pos.le
  have key := entropy_le_split_integrals hm hnn hsi hmass hent hA hr0pos hEt hPoin hdef hk2
  -- algebra
  set T2 := ∫ x, (max (f k x - A0) 0) ^ 2 ∂P (n k) with hT2def
  set T1 := ∫ x, max (f k x - A0) 0 ∂P (n k) with hT1def
  set D := (∫ x, min (f k x) A0 ∂P (n k) - 1) ^ 2 with hDdef
  set Eg := E (n k) (fun x => min (f k x) A0)
  set Et := E (n k) (fun x => max (f k x - A0) 0)
  have hhk := hpos
  have eD : D = d k * h k := by simp only [hd]; exact (div_mul_cancel₀ _ hhk.ne').symm
  have eT2 : T2 = a k * h k := by simp only [ha]; exact (div_mul_cancel₀ _ hhk.ne').symm
  have eT1 : T1 = b k * h k := by simp only [hb]; exact (div_mul_cancel₀ _ hhk.ne').symm
  have hK1r : K1 / r0 = 2 / ρ1 := by
    rw [hK1, hL]; field_simp; ring
  have hEg0 : 0 ≤ Eg := hyp.energy_nonneg (n k) _ hgS
  have h1 : K1 * (Eg / r0 + D) = (2 / ρ1) * Eg + K1 * D := by
    rw [mul_add, ← hK1r]; ring
  have h2 : 2 * Et / r0 ≤ (2 / ρ1) * Et := by
    rw [div_le_iff₀ hr0pos]
    have : 2 / ρ1 * Et * r0 = 2 * Et * (r0 / ρ1) := by field_simp
    rw [this]
    have : 1 ≤ r0 / ρ1 := (one_le_div hρ1pos).2 hρ1r0.le
    nlinarith
  have h3 : h k ≤ (2 / ρ1) * E (n k) (f k) + h k * ε k := by
    have hsp : (2 / ρ1) * (Eg + Et) ≤ (2 / ρ1) * E (n k) (f k) :=
      mul_le_mul_of_nonneg_left hEs (by positivity)
    have : h k * ε k = K1 * D + (|C| + K2) * T2 + K3 * T1 := by
      simp only [hεdef, eD, eT2, eT1]; ring
    linarith
  have h4 : (2 / ρ1) * E (n k) (f k) < (r / ρ1) * h k := by
    have : (2 / ρ1) * E (n k) (f k) = (1 / ρ1) * (2 * E (n k) (f k)) := by ring
    rw [this, show r / ρ1 * h k = (1 / ρ1) * (r * h k) by ring]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have h5 : h k * ε k < h k * (1 - r / ρ1) := mul_lt_mul_of_pos_left hk1 hhk
  linarith

end DGPS.Analysis
