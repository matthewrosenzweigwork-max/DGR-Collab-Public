import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.L2Space
import DGPS.Frontier.EX049.T32
import DGPS.Frontier.STR029.T04
import DGPS.Frontier.STR029.T33

/-!
# STR029.06: Information bound for low quotients

Task id and title: STR029.06, "Information bound for low quotients" (node STR029). Let `|h| ≤ 1/1000`,
let `g ≥ 0` be periodic `H¹` with `∫ g² q_h = 1` and `H = ∫ g² log g² q_h > 0`, and suppose
`4E/(2H) ≤ 2` where `E = ∫ g'² q_h`. With `K = 8π² e^{1/500}` and `A = log (K + 2)` one has
`E ≤ 4(A + 1)` and `‖g‖_∞ ≤ 1 + 2π e^{1/1000} √E`.

## Provides

* `DGPS.Frontier.STR029.str029_06_information_bound_low_quotients`: the main statement. Under the
  hypotheses above, `E ≤ 4 (A + 1)`, and the continuous periodic locally absolutely continuous
  representative `F` of `g` (from EX049.32) satisfies `|F t| ≤ 1 + 2π e^{1/1000} √E` for all `t`; the
  essential supremum of `g` over one period obeys the same bound.
* `DGPS.Frontier.STR029.str029_06_information_bound_low_quotients_unique`: the sup-norm bound holds for
  every continuous `2π`-periodic function that is almost everywhere equal to `g` on the period.
* `DGPS.Frontier.STR029.str029_06_information_bound_low_quotients_sup_bound`: the self-contained
  statement that a continuous periodic `F` with `F = c + ∫₀ˣ w` on `[0, 2π]` and `∫ F² q_h = 2π` obeys
  `|F t| ≤ 1 + 2π e^{|h|} √(∫ w² q_h dm)` for all `t`.
* `DGPS.Frontier.STR029.str029_06_information_bound_low_quotients_log_le_sqrt`: for `E ≥ 0`,
  `log (1 + E) ≤ √E`.

## R5 notes

* Carriers. The weighted integrals use the common carriers of STR029.04: `normInt_STR02904` for the
  normalized circle integral `∫ · dm = (2π)⁻¹ ∫₀^{2π}` and `qT_STR02904 h` for the reference density
  `q_h`. "Periodic `H¹` with derivative `g'`" uses the STR029.33 predicate
  `IsPeriodicWeakDerivative_STR02933 g g'` (both `2π`-periodic and `L²` on `(0, 2π]`, weak identity
  against smooth periodic tests). The continuous periodic representative is the one supplied by
  EX049.32 (`ex049_32_periodic_weak_pairs_have_periodic_ac`) with `L = 2π`; no second periodic Sobolev
  development is made.
* Reading of the unknown names. `E`, `H`, `K`, `A` are universally quantified reals tied to the
  specification's integrals by defining equations `hE`, `hH`, `hK`, `hA`. The derivative `g'` is a
  second function variable, constrained only by being a periodic weak derivative of `g`; `E` does not
  depend on the choice of `g'` because weak derivatives agree almost everywhere.
* Hypothesis `g ≥ 0` is stated for every `t`. It is not used by the proof: the argument bounds `|F|`
  and every integrand is estimated through `g²`. It is carried only because the specification lists
  it, as the underscore-named hypothesis `_hg0`.
* The conclusion `‖g‖_∞ ≤ B` is made explicit in two forms. (1) For the continuous periodic locally
  absolutely continuous representative `F` of EX049.32: `|F t| ≤ B` for every real `t`. (2) For the
  given function: `eLpNorm g ⊤ (volume.restrict (Ioc 0 (2π))) ≤ ENNReal.ofReal B`, the
  essential supremum over the period. The companion `_unique` extends (1) to every continuous periodic
  function a.e. equal to `g`. All a.e. statements are with respect to `volume.restrict (Ioc 0 (2π))`
  (the form used by STR029.33); EX049.32 uses `Ioo 0 (2π)`, which differs by a null set.
* The specification's constant `e^{|h|}` is relaxed to `e^{1/1000}` using `|h| ≤ 1/1000`; the
  intermediate bound `1 + 2π e^{|h|} √E` is the helper `..._sup_bound`.
* Convention for `z log z` at `0`: Lean has `Real.log 0 = 0`, so `g² log g²` is `0` where `g = 0`, as in the
  specification (`0 log 0 = 0`). The hypothesis `0 < H` is used only to cancel `H` in the quotient
  hypothesis (`E ≤ H`) and implicitly guarantees the entropy integral is not the junk value `0`.
* Minimum point. The specification takes a point where `g ≤ 1`. The proof takes the minimizer `t₀` of
  `F²` on `[0, 2π]` (exists by compactness), whose weighted average bound gives `F(t₀)² ≤ 1` because
  `∫ q_h dm = 1`. This is the same point-selection argument, in a form that needs no strict inequality.
* Oscillation. `|F t - F t₀| ≤ ∫₀^{2π} |g'|` comes from `F = c + ∫₀ˣ g'` on `[0, 2π]` (EX049.32);
  Cauchy–Schwarz is proved elementarily (`0 ≤ ∫ (|w| - λ)²` with `λ = ∫|w| / (2π)`), and the lower
  density bound `q_h ≥ e^{-2|h|}` of STR029.04 gives `∫ w² ≤ e^{2|h|} · 2π · E`. Hence the oscillation
  is at most `2π e^{|h|} √E`.
* Final elementary step. `log (1 + E) ≤ √E` is proved from the partial exponential sum
  `1 + s + s²/2 + s³/6 ≤ e^s` (not by the derivative argument of the sketch), and the concluding
  contradiction is the quadratic inequality `3s²/4 - s + 1 > 0` for `s = √E`.
* Every statement is proved; no hypothesis is added beyond the specification's.
-/

open MeasureTheory Set
open scoped Real ContDiff

namespace DGPS.Frontier.STR029

/-- The normalized weight integrates to one: `∫ q_h dm = 1`. -/
lemma normInt_qT_STR02906 (h : ℝ) : normInt_STR02904 (qT_STR02904 h) = 1 := by
  have hq : qT_STR02904 h = fun t => (normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))))⁻¹ *
      Real.exp (h * Real.cos (3 * t)) := funext (qT_eq_STR02904 h)
  rw [hq, normInt_const_mul_STR02904]
  exact inv_mul_cancel₀ (partition_pos_STR02904 h).ne'

/-- Unnormalized form: `∫₀^{2π} q_h = 2π`. -/
lemma int_qT_STR02906 (h : ℝ) : ∫ t in (0 : ℝ)..(2 * π), qT_STR02904 h t = 2 * π := by
  have h1 := normInt_qT_STR02906 h
  have hpi : (2 * π) ≠ 0 := by positivity
  unfold normInt_STR02904 at h1
  field_simp at h1
  exact h1

/-- Unnormalized form of a normalized integral. -/
lemma int_of_normInt_STR02906 {u : ℝ → ℝ} {a : ℝ} (hu : normInt_STR02904 u = a) :
    ∫ t in (0 : ℝ)..(2 * π), u t = 2 * π * a := by
  have hpi : (2 * π) ≠ 0 := by positivity
  rw [← hu]
  unfold normInt_STR02904
  field_simp

/-- Normalized integrals ignore almost-everywhere modifications on the period. -/
lemma normInt_congr_ae_STR02906 {u v : ℝ → ℝ}
    (huv : u =ᵐ[volume.restrict (Ioo 0 (2 * π))] v) : normInt_STR02904 u = normInt_STR02904 v := by
  have hT : (0 : ℝ) ≤ 2 * π := by positivity
  unfold normInt_STR02904
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact congrArg _ (integral_congr_ae huv)

/-- Cauchy–Schwarz on an interval: `(∫₀ᵀ |w|)² ≤ T ∫₀ᵀ w²`. -/
lemma sq_int_abs_le_STR02906 {w : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hw : IntervalIntegrable w volume 0 T) (hw2 : IntervalIntegrable (fun t => w t ^ 2) volume 0 T) :
    (∫ t in (0 : ℝ)..T, |w t|) ^ 2 ≤ T * ∫ t in (0 : ℝ)..T, w t ^ 2 := by
  have hwa : IntervalIntegrable (fun t => |w t|) volume 0 T := hw.abs
  have key : ∀ l : ℝ, 0 ≤ (∫ t in (0 : ℝ)..T, w t ^ 2) - 2 * l * (∫ t in (0 : ℝ)..T, |w t|) +
      l ^ 2 * T := by
    intro l
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..T, (|w t| - l) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hT.le (fun t => sq_nonneg _)
    have e : (fun t => (|w t| - l) ^ 2) = fun t => (w t ^ 2 - (2 * l) * |w t|) + l ^ 2 := by
      funext t
      rw [sub_sq, sq_abs]
      ring
    rw [e, intervalIntegral.integral_add (hw2.sub (hwa.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hw2 (hwa.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at h0
    simp only [sub_zero, smul_eq_mul] at h0
    linarith
  have hk := key ((∫ t in (0 : ℝ)..T, |w t|) / T)
  have hT0 : T ≠ 0 := hT.ne'
  have e2 : (∫ t in (0 : ℝ)..T, w t ^ 2) - 2 * ((∫ t in (0 : ℝ)..T, |w t|) / T) *
      (∫ t in (0 : ℝ)..T, |w t|) + ((∫ t in (0 : ℝ)..T, |w t|) / T) ^ 2 * T =
      (∫ t in (0 : ℝ)..T, w t ^ 2) - (∫ t in (0 : ℝ)..T, |w t|) ^ 2 / T := by
    field_simp
    ring
  rw [e2, sub_nonneg, div_le_iff₀ hT] at hk
  linarith

/-- For `E ≥ 0`, `log (1 + E) ≤ √E`. -/
theorem str029_06_information_bound_low_quotients_log_le_sqrt {E : ℝ} (hE : 0 ≤ E) :
    Real.log (1 + E) ≤ Real.sqrt E := by
  have hs0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hs2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  rw [Real.log_le_iff_le_exp (by linarith)]
  have h4 := Real.sum_le_exp_of_nonneg hs0 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one, pow_zero,
    pow_one] at h4
  norm_num at h4
  nlinarith [mul_nonneg hs0 (sq_nonneg (Real.sqrt E - 3 / 2))]

/-- The closing quadratic step: `E ≤ A + √E` forces `E ≤ 4 (A + 1)`. -/
lemma bound_of_le_STR02906 {E A : ℝ} (hE : 0 ≤ E) (h : E ≤ A + Real.sqrt E) :
    E ≤ 4 * (A + 1) := by
  by_contra hcon
  have hcon' := not_le.1 hcon
  have hs2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  nlinarith [sq_nonneg (Real.sqrt E - 2 / 3)]

/-- Oscillation bound on the period and sup-norm bound everywhere. -/
theorem str029_06_information_bound_low_quotients_sup_bound {h c : ℝ} {F w : ℝ → ℝ}
    (hFc : Continuous F) (hFp : Function.Periodic F (2 * π))
    (hFw : ∀ x ∈ Icc (0 : ℝ) (2 * π), F x = c + ∫ t in (0 : ℝ)..x, w t)
    (hw : IntervalIntegrable w volume 0 (2 * π))
    (hw2 : IntervalIntegrable (fun t => w t ^ 2) volume 0 (2 * π))
    (hFq : ∫ t in (0 : ℝ)..(2 * π), F t ^ 2 * qT_STR02904 h t = 2 * π) :
    ∀ t, |F t| ≤
      1 + 2 * π * Real.exp |h| *
        Real.sqrt (normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t)) := by
  have hT : 0 < 2 * π := by positivity
  have hqc : Continuous (qT_STR02904 h) := continuous_qT_STR02904 h
  have hq0 : ∀ t, 0 ≤ qT_STR02904 h t := fun t => (qT_pos_STR02904 h t).le
  -- the energy and its lower bound
  have hwq : IntervalIntegrable (fun t => w t ^ 2 * qT_STR02904 h t) volume 0 (2 * π) :=
    hw2.mul_continuousOn hqc.continuousOn
  have hE0 : 0 ≤ normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t) :=
    mul_nonneg (inv_nonneg.2 hT.le) (intervalIntegral.integral_nonneg_of_forall hT.le
      (fun t => mul_nonneg (sq_nonneg _) (hq0 t)))
  have hEint := int_of_normInt_STR02906 (u := fun t => w t ^ 2 * qT_STR02904 h t) rfl
  have hS : ∫ t in (0 : ℝ)..(2 * π), w t ^ 2 ≤
      Real.exp (2 * |h|) * (2 * π * normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t)) := by
    rw [← hEint, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT.le hw2 (hwq.const_mul _) (fun t _ => ?_)
    have hlow := (qT_bounds_STR02904 h t).1
    have h1 : 1 ≤ Real.exp (2 * |h|) * qT_STR02904 h t := by
      calc (1 : ℝ) = Real.exp (2 * |h|) * Real.exp (-(2 * |h|)) := by
            rw [← Real.exp_add]; simp
        _ ≤ Real.exp (2 * |h|) * qT_STR02904 h t :=
            mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    calc w t ^ 2 = w t ^ 2 * 1 := (mul_one _).symm
      _ ≤ w t ^ 2 * (Real.exp (2 * |h|) * qT_STR02904 h t) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = Real.exp (2 * |h|) * (w t ^ 2 * qT_STR02904 h t) := by ring
  have hCS := sq_int_abs_le_STR02906 hT hw hw2
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..(2 * π), |w t| :=
    intervalIntegral.integral_nonneg_of_forall hT.le (fun _ => abs_nonneg _)
  have he2 : Real.exp (2 * |h|) = Real.exp |h| ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsq := Real.sq_sqrt hE0
  have hB0 : 0 ≤ 2 * π * Real.exp |h| *
      Real.sqrt (normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t)) := by positivity
  have hIB : ∫ t in (0 : ℝ)..(2 * π), |w t| ≤ 2 * π * Real.exp |h| *
      Real.sqrt (normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t)) := by
    refine (sq_le_sq₀ hI0 hB0).1 ?_
    have : (2 * π * Real.exp |h| *
        Real.sqrt (normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t))) ^ 2 =
        (2 * π) * (Real.exp |h| ^ 2 *
          ((2 * π) * normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t))) := by
      rw [mul_pow, hsq]; ring
    rw [this, ← he2]
    exact hCS.trans (mul_le_mul_of_nonneg_left hS hT.le)
  -- a point with F² ≤ 1
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT.le)
    (hFc.pow 2).continuousOn
  have hm : F t0 ^ 2 ≤ 1 := by
    have h1 : ∫ s in (0 : ℝ)..(2 * π), F t0 ^ 2 * qT_STR02904 h s ≤
        ∫ s in (0 : ℝ)..(2 * π), F s ^ 2 * qT_STR02904 h s :=
      intervalIntegral.integral_mono_on hT.le ((continuous_const.mul hqc).intervalIntegrable _ _)
        (((hFc.pow 2).mul hqc).intervalIntegrable _ _)
        (fun s hs => mul_le_mul_of_nonneg_right (isMinOn_iff.1 hmin s hs) (hq0 s))
    rw [intervalIntegral.integral_const_mul, int_qT_STR02906, hFq] at h1
    nlinarith
  have hF0 : |F t0| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 hm
  -- oscillation
  have hosc : ∀ s ∈ Icc (0 : ℝ) (2 * π), |F s| ≤ 1 + ∫ x in (0 : ℝ)..(2 * π), |w x| := by
    intro s hs
    have hsub : ∀ x ∈ Icc (0 : ℝ) (2 * π),
        Set.uIcc (0 : ℝ) x ⊆ Set.uIcc (0 : ℝ) (2 * π) := fun x hx =>
      Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.uIcc_of_le hT.le]; exact hx)
    have hdiff : F s - F t0 = ∫ x in t0..s, w x := by
      rw [hFw s hs, hFw t0 ht0, add_sub_add_left_eq_sub]
      exact intervalIntegral.integral_interval_sub_left (hw.mono_set (hsub s hs))
        (hw.mono_set (hsub t0 ht0))
    have hsubI : Set.uIoc t0 s ⊆ Set.uIoc 0 (2 * π) := by
      rw [Set.uIoc_of_le hT.le]
      intro x hx
      rw [Set.mem_uIoc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
        linarith [ht0.1, ht0.2, hs.1, hs.2]
    have hstep : |∫ x in t0..s, w x| ≤ ∫ x in (0 : ℝ)..(2 * π), |w x| := by
      calc |∫ x in t0..s, w x| ≤ abs (∫ x in t0..s, |w x|) := by
            simpa only [Real.norm_eq_abs] using
              intervalIntegral.norm_integral_le_abs_integral_norm (f := w) (a := t0) (b := s)
        _ ≤ abs (∫ x in (0 : ℝ)..(2 * π), |w x|) :=
            intervalIntegral.abs_integral_mono_interval hsubI (ae_of_all _ fun x => abs_nonneg _) hw.abs
        _ = ∫ x in (0 : ℝ)..(2 * π), |w x| := abs_of_nonneg hI0
    have := abs_sub_abs_le_abs_sub (F s) (F t0)
    rw [hdiff] at this
    linarith
  intro t
  obtain ⟨s, hs, hts⟩ := Function.Periodic.exists_mem_Ico₀ hFp hT t
  rw [hts]
  exact (hosc s ⟨hs.1, hs.2.le⟩).trans (by linarith)

/-- Entropy against the weight is at most `log M²` when `|F| ≤ M` and `∫ F² q_h dm = 1`. -/
lemma entropy_le_STR02906 {h M : ℝ} {F : ℝ → ℝ} (hFc : Continuous F) (hM : ∀ t, |F t| ≤ M)
    (hFq : ∫ t in (0 : ℝ)..(2 * π), F t ^ 2 * qT_STR02904 h t = 2 * π) :
    normInt_STR02904 (fun t => F t ^ 2 * Real.log (F t ^ 2) * qT_STR02904 h t) ≤
      Real.log (M ^ 2) := by
  have hT : 0 < 2 * π := by positivity
  have hqc : Continuous (qT_STR02904 h) := continuous_qT_STR02904 h
  have hcont : Continuous (fun t => F t ^ 2 * Real.log (F t ^ 2) * qT_STR02904 h t) :=
    ((Real.continuous_mul_log.comp (hFc.pow 2))).mul hqc
  have hle : ∫ t in (0 : ℝ)..(2 * π), F t ^ 2 * Real.log (F t ^ 2) * qT_STR02904 h t ≤
      ∫ t in (0 : ℝ)..(2 * π), Real.log (M ^ 2) * (F t ^ 2 * qT_STR02904 h t) := by
    refine intervalIntegral.integral_mono_on hT.le (hcont.intervalIntegrable _ _)
      ((((hFc.pow 2).mul hqc).intervalIntegrable _ _).const_mul _) (fun t _ => ?_)
    have hq0 : 0 ≤ qT_STR02904 h t := (qT_pos_STR02904 h t).le
    have hF2 : F t ^ 2 * Real.log (F t ^ 2) ≤ Real.log (M ^ 2) * F t ^ 2 := by
      by_cases h0 : F t = 0
      · simp [h0]
      · have hpos : 0 < F t ^ 2 := by positivity
        have hab := hM t
        have hMF : F t ^ 2 ≤ M ^ 2 := by
          nlinarith [abs_le.1 hab, sq_abs (F t), abs_nonneg (F t)]
        have := Real.log_le_log hpos hMF
        nlinarith [sq_nonneg (F t)]
    calc F t ^ 2 * Real.log (F t ^ 2) * qT_STR02904 h t
        ≤ (Real.log (M ^ 2) * F t ^ 2) * qT_STR02904 h t :=
          mul_le_mul_of_nonneg_right hF2 hq0
      _ = Real.log (M ^ 2) * (F t ^ 2 * qT_STR02904 h t) := by ring
  rw [intervalIntegral.integral_const_mul, hFq] at hle
  unfold normInt_STR02904
  have : (2 * π)⁻¹ * (Real.log (M ^ 2) * (2 * π)) = Real.log (M ^ 2) := by
    field_simp
  rw [← this]
  exact mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hT.le)

/-- Information bound for low quotients. -/
theorem str029_06_information_bound_low_quotients
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' : ℝ → ℝ} (_hg0 : ∀ t, 0 ≤ g t)
    (hH1 : IsPeriodicWeakDerivative_STR02933 g g')
    (hnorm : normInt_STR02904 (fun t => g t ^ 2 * qT_STR02904 h t) = 1)
    {E H K A : ℝ}
    (hE : E = normInt_STR02904 (fun t => g' t ^ 2 * qT_STR02904 h t))
    (hH : H = normInt_STR02904 (fun t => g t ^ 2 * Real.log (g t ^ 2) * qT_STR02904 h t))
    (hHpos : 0 < H) (hquot : 4 * E / (2 * H) ≤ 2)
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2)) :
    E ≤ 4 * (A + 1) ∧
      ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F (2 * π) ∧
        (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
        F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g ∧
        (∀ t, |F t| ≤ 1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt E) ∧
        eLpNorm g ⊤ (volume.restrict (Ioc 0 (2 * π))) ≤
          ENNReal.ofReal (1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt E) := by
  obtain ⟨⟨hgp, hgL2⟩, ⟨hg'p, hg'L2⟩, hweak⟩ := hH1
  have hT : 0 < 2 * π := by positivity
  have hmono : volume.restrict (Ioo 0 (2 * π)) ≤ volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_mono Ioo_subset_Ioc_self le_rfl
  have hweak' : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ (2 * π) →
      ∫ x in Ioo 0 (2 * π), g x * deriv φ x = -∫ x in Ioo 0 (2 * π), g' x * φ x := by
    intro φ hφ hper
    have h1 := hweak φ ⟨hφ, hper⟩
    unfold normInt_STR02933 at h1
    rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h1
    have hp : (2 * π)⁻¹ ≠ 0 := by positivity
    refine mul_left_cancel₀ hp ?_
    rw [mul_neg]
    linarith
  obtain ⟨c, -, -, F, ⟨hFc, hFp, hFac, hFeq, hFf⟩, huniq⟩ :=
    DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac (2 * π) hT g g'
      (hgL2.mono_measure hmono) (hg'L2.mono_measure hmono) hweak'
  have hFg : F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hFf
  -- integrability of the derivative
  have hw : IntervalIntegrable g' volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2 (hg'L2.integrable (by norm_num))
  have hw2 : IntervalIntegrable (fun t => g' t ^ 2) volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2 hg'L2.integrable_sq
  -- normalization transferred to F
  have hnormF : ∫ t in (0 : ℝ)..(2 * π), F t ^ 2 * qT_STR02904 h t = 2 * π := by
    have h1 : normInt_STR02904 (fun t => F t ^ 2 * qT_STR02904 h t) = 1 := by
      rw [← hnorm]
      refine normInt_congr_ae_STR02906 ?_
      filter_upwards [hFf] with t ht
      rw [ht]
    have := int_of_normInt_STR02906 h1
    linarith
  have hsup : ∀ t, |F t| ≤ 1 + 2 * π * Real.exp |h| * Real.sqrt E := by
    rw [hE]
    exact str029_06_information_bound_low_quotients_sup_bound hFc hFp hFeq hw hw2 hnormF
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact mul_nonneg (inv_nonneg.2 hT.le) (intervalIntegral.integral_nonneg_of_forall hT.le
      (fun t => mul_nonneg (sq_nonneg _) (qT_pos_STR02904 h t).le))
  -- relaxed constant
  have hexp : Real.exp |h| ≤ Real.exp (1 / 1000) := Real.exp_le_exp.2 hh
  have hsup' : ∀ t, |F t| ≤ 1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt E := by
    intro t
    have : 2 * π * Real.exp |h| * Real.sqrt E ≤ 2 * π * Real.exp (1 / 1000) * Real.sqrt E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hT.le) (Real.sqrt_nonneg _)
    linarith [hsup t]
  -- entropy bound
  set M : ℝ := 1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt E with hMdef
  have hHle : H ≤ Real.log (M ^ 2) := by
    have h1 : H = normInt_STR02904 (fun t => F t ^ 2 * Real.log (F t ^ 2) * qT_STR02904 h t) := by
      rw [hH]
      refine normInt_congr_ae_STR02906 ?_
      filter_upwards [hFf] with t ht
      rw [ht]
    rw [h1]
    exact entropy_le_STR02906 hFc hsup' hnormF
  -- algebra
  have hsq := Real.sq_sqrt hE0
  have hexp2 : Real.exp (1 / 1000) ^ 2 = Real.exp (1 / 500) := by
    rw [sq, ← Real.exp_add]; norm_num
  have hKpos : 0 ≤ K := by rw [hK]; positivity
  have hM2 : M ^ 2 ≤ (K + 2) * (1 + E) := by
    have hc2 : (2 * π * Real.exp (1 / 1000)) ^ 2 = K / 2 := by
      rw [hK, mul_pow, mul_pow, hexp2]; ring
    have hcs : 2 * (2 * π * Real.exp (1 / 1000) * Real.sqrt E) ≤
        1 + (2 * π * Real.exp (1 / 1000) * Real.sqrt E) ^ 2 := by
      nlinarith [sq_nonneg (1 - 2 * π * Real.exp (1 / 1000) * Real.sqrt E)]
    have hcs2 : (2 * π * Real.exp (1 / 1000) * Real.sqrt E) ^ 2 = K / 2 * E := by
      rw [mul_pow, hc2, hsq]
    rw [hMdef]
    nlinarith
  have hMpos : 0 < M ^ 2 := by
    have : 0 < M := by
      rw [hMdef]; positivity
    positivity
  have hlog : Real.log (M ^ 2) ≤ A + Real.sqrt E := by
    calc Real.log (M ^ 2) ≤ Real.log ((K + 2) * (1 + E)) := Real.log_le_log hMpos hM2
      _ = A + Real.log (1 + E) := by
          rw [Real.log_mul (by linarith) (by linarith), hA]
      _ ≤ A + Real.sqrt E := by
          have := str029_06_information_bound_low_quotients_log_le_sqrt hE0
          linarith
  -- quotient hypothesis
  have hEH : E ≤ H := by
    rw [div_le_iff₀ (by positivity)] at hquot
    linarith
  refine ⟨bound_of_le_STR02906 hE0 (hEH.trans (hHle.trans hlog)), F, hFc, hFp, hFac, hFg,
    hsup', ?_⟩
  rw [eLpNorm_exponent_top hgL2.aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_bound ?_
  filter_upwards [hFg] with t ht
  rw [← ht, Real.norm_eq_abs]
  exact hsup' t

/-- The sup-norm bound holds for every continuous periodic function a.e. equal to `g`. -/
theorem str029_06_information_bound_low_quotients_unique
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hH1 : IsPeriodicWeakDerivative_STR02933 g g')
    (hnorm : normInt_STR02904 (fun t => g t ^ 2 * qT_STR02904 h t) = 1)
    {E H K A : ℝ}
    (hE : E = normInt_STR02904 (fun t => g' t ^ 2 * qT_STR02904 h t))
    (hH : H = normInt_STR02904 (fun t => g t ^ 2 * Real.log (g t ^ 2) * qT_STR02904 h t))
    (hHpos : 0 < H) (hquot : 4 * E / (2 * H) ≤ 2)
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2))
    {F' : ℝ → ℝ} (hc : Continuous F') (hp : Function.Periodic F' (2 * π))
    (hae : F' =ᵐ[volume.restrict (Ioc 0 (2 * π))] g) :
    ∀ t, |F' t| ≤ 1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt E := by
  obtain ⟨-, F, hFc, hFp, -, hFg, hb, -⟩ :=
    str029_06_information_bound_low_quotients hh hg0 hH1 hnorm hE hH hHpos hquot hK hA
  have hT : 0 < 2 * π := by positivity
  have hmono : volume.restrict (Ioo 0 (2 * π)) ≤ volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_mono Ioo_subset_Ioc_self le_rfl
  have heq : F' = F :=
    DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac_unique hT hc hFc hp hFp
      (hae.filter_mono (ae_mono hmono)) (hFg.filter_mono (ae_mono hmono))
  rw [heq]
  exact hb

end DGPS.Frontier.STR029
