import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.L2Space
import DGPS.Frontier.EX049.T32
import DGPS.Frontier.STR029.T04
import DGPS.Frontier.STR029.T06
import DGPS.Frontier.STR029.T33

/-!
# STR029.37: Uniform equicontinuity of low-quotient square roots

Task id and title: STR029.37, "Uniform equicontinuity of low-quotient square roots" (node STR029).
For fixed `h`, the continuous periodic representatives of the square roots `g` from STR029.06 are
uniformly bounded and satisfy `|g t - g s| ≤ √(2π) e^{|h|} √E d(t,s)^{1/2}`, where `d` is the circular
distance modulo `2π`. Consequently they are uniformly equicontinuous: the modulus depends only on
`h`, `A` and `ε`, not on the particular `g`.

## Provides

* `DGPS.Frontier.STR029.str029_37_uniform_equicontinuity_low_quotient_square_roots`: the main
  statement. Under the hypotheses of STR029.06, `E ≤ 4 (A + 1)`, and there is a continuous,
  `2π`-periodic, locally absolutely continuous `F` with `F = g` a.e. on the period, such that
  `|F t| ≤ 1 + 2π e^{1/1000} √E` for all `t` and the Hölder bound holds for all `t, s`.
* `DGPS.Frontier.STR029.str029_37_uniform_equicontinuity_low_quotient_square_roots_equicontinuous`:
  the uniform equicontinuity. For every `ε > 0` there is `δ > 0`, depending only on `h`, `A` and `ε`,
  such that for every admissible `g` and every continuous periodic `F` a.e. equal to `g` on the
  period, circular distance below `δ` forces `|F t - F s| < ε`.
* `DGPS.Frontier.STR029.str029_37_uniform_equicontinuity_low_quotient_square_roots_circdist_min`:
  the circular distance `circDist_STR02937 t s` is at most `|t - s - 2π k|` for every integer `k`,
  so it is the minimum of `|t - s - 2π k|` over `k ∈ ℤ`.

## R5 notes

* Carriers. The weighted integrals use the STR029.04 carriers: `normInt_STR02904` for the normalized
  circle integral `∫ · dm = (2π)⁻¹ ∫₀^{2π}` and `qT_STR02904 h` for the reference density `q_h`. The
  periodic weak derivative is the STR029.33 predicate `IsPeriodicWeakDerivative_STR02933 g g'`. The
  representative `F` is the one supplied by EX049.32 with interval length `L = 2π`.
* Hypotheses. The hypotheses of the main statement are exactly those of
  `str029_06_information_bound_low_quotients` (STR029.06), which the proof calls for `E ≤ 4 (A + 1)`.
  The constants `E`, `H`, `K`, `A` are universally quantified reals tied to their integrals by the
  defining equations `hE`, `hH`, `hK`, `hA`. The condition `hquot` and `hHpos` are used only through
  that call. `hg0` (`g ≥ 0`) is likewise only passed on.
* Domain. `g` is a periodic `H¹` function: `IsPeriodicWeakDerivative_STR02933 g g'` gives periodicity,
  `L²` on `(0, 2π]`, and the weak identity against smooth periodic tests. Almost-everywhere statements
  are with respect to `volume.restrict (Ioc 0 (2π))`, as in STR029.06. EX049.32 uses `Ioo 0 (2π)`,
  which differs by a null set.
* Circular distance (design choice). `d(t,s)` is defined as
  `|t - s - 2π · round((t - s)/(2π))|`, the distance from `t - s` to the nearest multiple of `2π`.
  The minimality lemma `..._circdist_min` shows this equals the minimum over all lattice points
  `2πk`, `k ∈ ℤ`. The lemma `circDist_le_pi_STR02937` gives `d ≤ π`.
* Exponent. The specification's `d^{1/2}` is stated as the real power `(·) ^ (1 / 2 : ℝ)`. The proof
  converts it to `Real.sqrt` via `Real.sqrt_eq_rpow`, which is an identity for all reals.
* Non-literal reading of "integrate along the shorter arc". Periodicity of `F` lets the proof replace
  `t` by `s + δ` with `δ = t - s - 2π r` and `|δ| = d(t,s) ≤ π`. The integral is then taken over
  `[s, s + δ]` (or `[s + δ, s]` when `δ < 0`), an arc of length `d(t,s)`. The global identity
  `F x = c + ∫₀ˣ g'` for all real `x` is derived from the window identity on `[0, 2π]` by using that
  `g'` has zero mean (test function `φ = 1`), so that `∫₀^{x} g'` is `2π`-periodic.
* Energy bound. Cauchy–Schwarz on `[a, b]` (length at most `2π`) and periodicity give
  `(∫_a^b g')² ≤ d · ∫₀^{2π} g'²`. The density bound `q_h ≥ e^{-2|h|}` from STR029.04 gives
  `∫₀^{2π} g'² ≤ e^{2|h|} · 2π · E`. Together these yield the stated Hölder bound.
* Uniformity. The constant `√(2π) e^{|h|} √E` is bounded by `√(2π) e^{|h|} √(4 (A + 1))` through
  `E ≤ 4 (A + 1)` from STR029.06, which does not depend on `g`. The equicontinuity family quantifies
  over every admissible `g`, `g'`, `E`, `H`, and every continuous periodic `F` a.e. equal to `g`. It
  uses the EX049.32 uniqueness of such `F` to identify it with the representative of the main
  statement.
* Supremum bound. The bound `|F t| ≤ 1 + 2π e^{1/1000} √E` is the relaxed form of STR029.06's
  `str029_06_information_bound_low_quotients_sup_bound` with `e^{|h|} ≤ e^{1/1000}` from `|h| ≤ 1/1000`.
* Helpers. Every helper carries the suffix `_STR02937`. The public declarations carry the prefix
  `str029_37_uniform_equicontinuity_low_quotient_square_roots`. The proof uses only the
  STR029.04, STR029.06, STR029.33 and EX049.32 declarations listed above.
-/

open MeasureTheory Set
open scoped Real ContDiff

namespace DGPS.Frontier.STR029

/-- Circular distance modulo `2π`: the distance from `t - s` to the nearest multiple of `2π`. -/
noncomputable def circDist_STR02937 (t s : ℝ) : ℝ :=
  |t - s - 2 * π * ((round ((t - s) / (2 * π)) : ℤ) : ℝ)|

/-- The circular distance is nonnegative. -/
lemma circDist_nonneg_STR02937 (t s : ℝ) : 0 ≤ circDist_STR02937 t s :=
  abs_nonneg _

/-- The circular distance is the absolute value of a representative `δ` of `t - s` modulo `2π`. -/
lemma circDist_repr_STR02937 (t s : ℝ) :
    ∃ δ : ℝ, ∃ r : ℤ, circDist_STR02937 t s = |δ| ∧ t = s + δ + (r : ℝ) * (2 * π) :=
  ⟨t - s - 2 * π * ((round ((t - s) / (2 * π)) : ℤ) : ℝ), round ((t - s) / (2 * π)), rfl, by ring⟩

/-- The circular distance is at most `π`. -/
lemma circDist_le_pi_STR02937 (t s : ℝ) : circDist_STR02937 t s ≤ π := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have h1 := abs_sub_round ((t - s) / (2 * π))
  have e : t - s - 2 * π * ((round ((t - s) / (2 * π)) : ℤ) : ℝ) =
      (2 * π) * ((t - s) / (2 * π) - ((round ((t - s) / (2 * π)) : ℤ) : ℝ)) := by
    field_simp
  unfold circDist_STR02937
  rw [e, abs_mul, abs_of_pos hpi]
  linarith [mul_le_mul_of_nonneg_left h1 hpi.le]

/-- Minimality over the lattice: the circular distance is at most `|t - s - 2πk|` for every `k`. -/
lemma str029_37_uniform_equicontinuity_low_quotient_square_roots_circdist_min (t s : ℝ) (k : ℤ) :
    circDist_STR02937 t s ≤ |t - s - 2 * π * (k : ℝ)| := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have h1 := round_le ((t - s) / (2 * π)) k
  have e : ∀ r : ℝ, t - s - 2 * π * r = (2 * π) * ((t - s) / (2 * π) - r) := fun r => by
    field_simp
  have ea : ∀ x : ℝ, |2 * π * x| = 2 * π * |x| := fun x => by
    rw [abs_mul, abs_of_pos hpi]
  unfold circDist_STR02937
  rw [e, e, ea, ea]
  exact mul_le_mul_of_nonneg_left h1 hpi.le

/-- Cauchy–Schwarz on an interval: `(∫_a^b w)² ≤ (b - a) ∫_a^b w²`. -/
lemma sq_int_le_STR02937 {w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hw : IntervalIntegrable w volume a b) (hw2 : IntervalIntegrable (fun t => w t ^ 2) volume a b) :
    (∫ t in a..b, w t) ^ 2 ≤ (b - a) * ∫ t in a..b, w t ^ 2 := by
  rcases eq_or_lt_of_le hab with hEq | hlt
  · subst hEq
    simp
  · have hL : (0 : ℝ) < b - a := sub_pos.2 hlt
    have key : ∀ l : ℝ, 0 ≤ (∫ t in a..b, w t ^ 2) - 2 * l * (∫ t in a..b, w t) + (b - a) * l ^ 2 := by
      intro l
      have h0 : 0 ≤ ∫ t in a..b, (w t - l) ^ 2 :=
        intervalIntegral.integral_nonneg_of_forall hab (fun t => sq_nonneg _)
      have e : (fun t => (w t - l) ^ 2) = fun t => (w t ^ 2 - (2 * l) * w t) + l ^ 2 := by
        funext t
        ring
      rw [e, intervalIntegral.integral_add (hw2.sub (hw.const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub hw2 (hw.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const] at h0
      simp only [smul_eq_mul] at h0
      linarith
    have hk := key ((∫ t in a..b, w t) / (b - a))
    have e2 : (∫ t in a..b, w t ^ 2) - 2 * ((∫ t in a..b, w t) / (b - a)) * (∫ t in a..b, w t) +
        (b - a) * ((∫ t in a..b, w t) / (b - a)) ^ 2 =
        (∫ t in a..b, w t ^ 2) - (∫ t in a..b, w t) ^ 2 / (b - a) := by
      field_simp
      ring
    rw [e2, sub_nonneg, div_le_iff₀ hL] at hk
    linarith [mul_comm (∫ t in a..b, w t ^ 2) (b - a)]

/-- A window of length at most `2π` carries no more energy than one period, for a `2π`-periodic
integrable `w` with square integrable on a period. -/
lemma sq_window_STR02937 {w : ℝ → ℝ} (hwp2 : Function.Periodic (fun t => w t ^ 2) (2 * π))
    (hw2 : IntervalIntegrable (fun t => w t ^ 2) volume 0 (2 * π)) {a b : ℝ} (hab : a ≤ b)
    (hba : b ≤ a + 2 * π) : ∫ t in a..b, w t ^ 2 ≤ ∫ t in (0 : ℝ)..(2 * π), w t ^ 2 := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hI : IntervalIntegrable (fun t => w t ^ 2) volume a (a + 2 * π) :=
    hwp2.intervalIntegrable₀ hT.ne' hw2 a (a + 2 * π)
  have hper : ∫ t in a..(a + 2 * π), w t ^ 2 = ∫ t in (0 : ℝ)..(2 * π), w t ^ 2 := by
    have := hwp2.intervalIntegral_add_eq a 0
    simpa only [zero_add] using this
  have hmono : ∫ t in a..b, w t ^ 2 ≤ ∫ t in a..(a + 2 * π), w t ^ 2 :=
    intervalIntegral.integral_mono_interval (le_refl a) hab hba
      (ae_of_all _ fun t => sq_nonneg (w t)) hI
  rw [hper] at hmono
  exact hmono

/-- Energy on a period: `∫₀^{2π} w² ≤ e^{2|h|} · 2π · ∫ w² q_h dm`. -/
lemma energy_window_STR02937 {h : ℝ} {w : ℝ → ℝ}
    (hw2 : IntervalIntegrable (fun t => w t ^ 2) volume 0 (2 * π)) :
    ∫ t in (0 : ℝ)..(2 * π), w t ^ 2 ≤
      Real.exp (2 * |h|) * (2 * π * normInt_STR02904 (fun t => w t ^ 2 * qT_STR02904 h t)) := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hqc : Continuous (qT_STR02904 h) := continuous_qT_STR02904 h
  have hwq : IntervalIntegrable (fun t => w t ^ 2 * qT_STR02904 h t) volume 0 (2 * π) :=
    hw2.mul_continuousOn hqc.continuousOn
  have hEint := int_of_normInt_STR02906 (u := fun t => w t ^ 2 * qT_STR02904 h t) rfl
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

/-- Weak identity on one period for a smooth periodic test function. -/
lemma weak_identity_STR02937 {g g' : ℝ → ℝ} (hH1 : IsPeriodicWeakDerivative_STR02933 g g')
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hper : Function.Periodic φ (2 * π)) :
    ∫ x in Ioo 0 (2 * π), g x * deriv φ x = -∫ x in Ioo 0 (2 * π), g' x * φ x := by
  obtain ⟨-, -, hweak⟩ := hH1
  have h1 := hweak φ ⟨hφ, hper⟩
  unfold normInt_STR02933 at h1
  rw [integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h1
  have hp : (2 * π)⁻¹ ≠ 0 := by positivity
  refine mul_left_cancel₀ hp ?_
  rw [mul_neg]
  linarith

/-- A periodic weak derivative has zero mean over one period. -/
lemma mean_zero_STR02937 {g g' : ℝ → ℝ} (hH1 : IsPeriodicWeakDerivative_STR02933 g g') :
    ∫ t in (0 : ℝ)..(2 * π), g' t = 0 := by
  have h1 := weak_identity_STR02937 hH1 (fun _ => (1 : ℝ)) contDiff_const (fun _ => rfl)
  simp only [deriv_const, mul_zero, integral_zero, mul_one] at h1
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * π by positivity),
    integral_Ioc_eq_integral_Ioo]
  linarith

/-- Global form of the integral identity: a continuous periodic `F` with `F = c + ∫₀ˣ w` on
`[0, 2π]` satisfies `F x = c + ∫₀ˣ w` for every real `x`, when `w` is periodic with zero mean. -/
lemma periodic_ftc_STR02937 {F w : ℝ → ℝ} {c : ℝ} (hFp : Function.Periodic F (2 * π))
    (hwp : Function.Periodic w (2 * π)) (hw : IntervalIntegrable w volume 0 (2 * π))
    (hmean : ∫ t in (0 : ℝ)..(2 * π), w t = 0)
    (hFeq : ∀ x ∈ Icc (0 : ℝ) (2 * π), F x = c + ∫ t in (0 : ℝ)..x, w t) :
    ∀ x : ℝ, F x = c + ∫ t in (0 : ℝ)..x, w t := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable w volume a b := fun a b =>
    hwp.intervalIntegrable₀ hT.ne' hw a b
  have hWp : ∀ y : ℝ, ∫ t in (0 : ℝ)..(y + 2 * π), w t = ∫ t in (0 : ℝ)..y, w t := by
    intro y
    have hy : ∫ t in y..(y + 2 * π), w t = 0 := by
      rw [hwp.intervalIntegral_add_eq y 0, zero_add, hmean]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 y) (hint y (y + 2 * π)), hy,
      add_zero]
  have hDp : Function.Periodic (fun y => F y - c - ∫ t in (0 : ℝ)..y, w t) (2 * π) := by
    intro y
    show F (y + 2 * π) - c - ∫ t in (0 : ℝ)..(y + 2 * π), w t =
      F y - c - ∫ t in (0 : ℝ)..y, w t
    rw [hFp y, hWp y]
  intro x
  obtain ⟨z, hz, hxz⟩ := Function.Periodic.exists_mem_Ico₀ hDp hT x
  have hxz' : F x - c - ∫ t in (0 : ℝ)..x, w t = F z - c - ∫ t in (0 : ℝ)..z, w t := hxz
  have hz0 := hFeq z ⟨hz.1, hz.2.le⟩
  linarith

/-- Hölder bound on the square along the shorter arc:
`(F t - F s)² ≤ d(t,s) · ∫₀^{2π} w²`. -/
lemma holder_sq_STR02937 {F w : ℝ → ℝ} {c : ℝ} (hFp : Function.Periodic F (2 * π))
    (hwp : Function.Periodic w (2 * π)) (hw : IntervalIntegrable w volume 0 (2 * π))
    (hw2 : IntervalIntegrable (fun t => w t ^ 2) volume 0 (2 * π))
    (hF : ∀ x, F x = c + ∫ t in (0 : ℝ)..x, w t) (t s : ℝ) :
    (F t - F s) ^ 2 ≤ circDist_STR02937 t s * ∫ x in (0 : ℝ)..(2 * π), w x ^ 2 := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hwp2 : Function.Periodic (fun x => w x ^ 2) (2 * π) := fun x => by
    show w (x + 2 * π) ^ 2 = w x ^ 2
    rw [hwp x]
  have hint : ∀ a b : ℝ, IntervalIntegrable w volume a b := fun a b =>
    hwp.intervalIntegrable₀ hT.ne' hw a b
  have hint2 : ∀ a b : ℝ, IntervalIntegrable (fun x => w x ^ 2) volume a b := fun a b =>
    hwp2.intervalIntegrable₀ hT.ne' hw2 a b
  obtain ⟨δ, r, hd, ht⟩ := circDist_repr_STR02937 t s
  have hδb : |δ| ≤ π := by
    rw [← hd]
    exact circDist_le_pi_STR02937 t s
  obtain ⟨hδ1, hδ2⟩ := abs_le.1 hδb
  have hpi := Real.pi_pos
  have hFt : F t = F (s + δ) := by
    rw [ht]
    exact hFp.int_mul r (s + δ)
  have hdiff : F (s + δ) - F s = ∫ x in s..(s + δ), w x := by
    have h1 := intervalIntegral.integral_interval_sub_left (hint 0 (s + δ)) (hint 0 s)
    rw [hF (s + δ), hF s]
    linarith
  rw [hFt, hdiff, hd]
  rcases le_total 0 δ with hδ | hδ
  · have hcs := sq_int_le_STR02937 (show s ≤ s + δ by linarith) (hint s (s + δ))
      (hint2 s (s + δ))
    have hwin := sq_window_STR02937 hwp2 hw2 (show s ≤ s + δ by linarith)
      (show s + δ ≤ s + 2 * π by linarith)
    rw [abs_of_nonneg hδ]
    have e1 : s + δ - s = δ := by ring
    rw [e1] at hcs
    linarith [mul_le_mul_of_nonneg_left hwin hδ]
  · have hsym := intervalIntegral.integral_symm (μ := volume) (f := w) (s + δ) s
    have hcs := sq_int_le_STR02937 (show s + δ ≤ s by linarith) (hint (s + δ) s)
      (hint2 (s + δ) s)
    have hwin := sq_window_STR02937 hwp2 hw2 (show s + δ ≤ s by linarith)
      (show s ≤ s + δ + 2 * π by linarith)
    rw [hsym, neg_sq, abs_of_nonpos hδ]
    have e1 : s - (s + δ) = -δ := by ring
    rw [e1] at hcs
    linarith [mul_le_mul_of_nonneg_left hwin (show 0 ≤ -δ by linarith)]

/-- A small nonnegative parameter gives a small product: `C u < ε` when `u < ε / (C + 1)`. -/
lemma modulus_small_STR02937 {C ε u : ℝ} (hC : 0 ≤ C) (hu0 : 0 ≤ u)
    (hu : u < ε / (C + 1)) : C * u < ε := by
  have hC1 : 0 < C + 1 := by linarith
  have h1 : u * (C + 1) < ε := (lt_div_iff₀ hC1).1 hu
  linarith

/-- Main statement of STR029.37. Under the hypotheses of STR029.06, `E ≤ 4 (A + 1)`, and there is
a continuous, `2π`-periodic, locally absolutely continuous `F` with `F = g` almost everywhere on the
period, such that `|F t| ≤ 1 + 2π e^{1/1000} √E` for all `t` and
`|F t - F s| ≤ √(2π) e^{|h|} √E d(t,s)^{1/2}` for all `t, s`. -/
theorem str029_37_uniform_equicontinuity_low_quotient_square_roots
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t)
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
        (∀ t s : ℝ, |F t - F s| ≤
          Real.sqrt (2 * π) * Real.exp |h| * Real.sqrt E * circDist_STR02937 t s ^ (1 / 2 : ℝ)) := by
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hEA : E ≤ 4 * (A + 1) :=
    (str029_06_information_bound_low_quotients hh hg0 hH1 hnorm hE hH hHpos hquot hK hA).1
  have hmono : volume.restrict (Ioo 0 (2 * π)) ≤ volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_mono Ioo_subset_Ioc_self le_rfl
  obtain ⟨⟨-, hgL2⟩, ⟨hg'p, hg'L2⟩, -⟩ := id hH1
  have hweak' : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ (2 * π) →
      ∫ x in Ioo 0 (2 * π), g x * deriv φ x = -∫ x in Ioo 0 (2 * π), g' x * φ x :=
    fun φ hφ hper => weak_identity_STR02937 hH1 φ hφ hper
  obtain ⟨c, -, -, F, ⟨hFc, hFp, hFac, hFeq, hFf⟩, -⟩ :=
    DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac (2 * π) hT g g'
      (hgL2.mono_measure hmono) (hg'L2.mono_measure hmono) hweak'
  have hFg : F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hFf
  have hw : IntervalIntegrable g' volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2 (hg'L2.integrable (by norm_num))
  have hw2 : IntervalIntegrable (fun t => g' t ^ 2) volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).2 hg'L2.integrable_sq
  have hglob := periodic_ftc_STR02937 hFp hg'p hw (mean_zero_STR02937 hH1) hFeq
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
  have hexp : Real.exp |h| ≤ Real.exp (1 / 1000) := Real.exp_le_exp.2 hh
  have hsup' : ∀ t, |F t| ≤ 1 + 2 * π * Real.exp (1 / 1000) * Real.sqrt E := by
    intro t
    have : 2 * π * Real.exp |h| * Real.sqrt E ≤ 2 * π * Real.exp (1 / 1000) * Real.sqrt E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hT.le) (Real.sqrt_nonneg _)
    linarith [hsup t]
  -- energy of the derivative on one period
  have hS : ∫ t in (0 : ℝ)..(2 * π), g' t ^ 2 ≤ Real.exp (2 * |h|) * (2 * π * E) := by
    have h1 := energy_window_STR02937 (h := h) hw2
    rw [← hE] at h1
    exact h1
  have he2 : Real.exp (2 * |h|) = Real.exp |h| ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsq2 : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hsqE : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0
  have hholder : ∀ t s : ℝ, |F t - F s| ≤
      Real.sqrt (2 * π) * Real.exp |h| * Real.sqrt E * circDist_STR02937 t s ^ (1 / 2 : ℝ) := by
    intro t s
    rw [← Real.sqrt_eq_rpow]
    have hd0 := circDist_nonneg_STR02937 t s
    have hY0 : 0 ≤ Real.sqrt (2 * π) * Real.exp |h| * Real.sqrt E *
        Real.sqrt (circDist_STR02937 t s) := by positivity
    have hfin : (F t - F s) ^ 2 ≤ circDist_STR02937 t s * (Real.exp (2 * |h|) * (2 * π * E)) :=
      (holder_sq_STR02937 hFp hg'p hw hw2 hglob t s).trans
        (mul_le_mul_of_nonneg_left hS hd0)
    apply (sq_le_sq₀ (abs_nonneg (F t - F s)) hY0).1
    have key : (Real.sqrt (2 * π) * Real.exp |h| * Real.sqrt E *
        Real.sqrt (circDist_STR02937 t s)) ^ 2 =
        circDist_STR02937 t s * (Real.exp (2 * |h|) * (2 * π * E)) := by
      rw [he2]
      calc _ = Real.sqrt (2 * π) ^ 2 * Real.exp |h| ^ 2 * Real.sqrt E ^ 2 *
            Real.sqrt (circDist_STR02937 t s) ^ 2 := by ring
        _ = circDist_STR02937 t s * (Real.exp |h| ^ 2 * (2 * π * E)) := by
            rw [hsq2, hsqE, Real.sq_sqrt hd0]; ring
    rw [sq_abs, key]
    exact hfin
  exact ⟨hEA, F, hFc, hFp, hFac, hFg, hsup', hholder⟩

/-- Uniform equicontinuity of the low-quotient square roots. For every `ε > 0` there is `δ > 0`,
depending only on `h`, `A` and `ε`, such that for every admissible `g`, `g'`, `E`, `H` (those of
STR029.06) and every continuous periodic `F` a.e. equal to `g` on the period, circular distance
below `δ` forces `|F t - F s| < ε`. -/
theorem str029_37_uniform_equicontinuity_low_quotient_square_roots_equicontinuous
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {K A : ℝ}
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ {g g' : ℝ → ℝ} {E H : ℝ}, (∀ t, 0 ≤ g t) → IsPeriodicWeakDerivative_STR02933 g g' →
        normInt_STR02904 (fun t => g t ^ 2 * qT_STR02904 h t) = 1 →
        E = normInt_STR02904 (fun t => g' t ^ 2 * qT_STR02904 h t) →
        H = normInt_STR02904 (fun t => g t ^ 2 * Real.log (g t ^ 2) * qT_STR02904 h t) →
        0 < H → 4 * E / (2 * H) ≤ 2 →
        ∀ {F : ℝ → ℝ}, Continuous F → Function.Periodic F (2 * π) →
          F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g →
          ∀ t s : ℝ, circDist_STR02937 t s < δ → |F t - F s| < ε := by
  intro ε hε
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hmono : volume.restrict (Ioo 0 (2 * π)) ≤ volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_mono Ioo_subset_Ioc_self le_rfl
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Real.sqrt (2 * π) * Real.exp |h| * Real.sqrt (4 * (A + 1)) :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨(ε / (C + 1)) ^ 2, pow_pos (div_pos hε (by linarith)) 2, ?_⟩
  intro g g' E H hg0 hH1 hnorm hE hH hHpos hquot F hFc hFp hFg t s hts
  obtain ⟨hEA, F0, hF0c, hF0p, -, hF0g, -, hF0H⟩ :=
    str029_37_uniform_equicontinuity_low_quotient_square_roots hh hg0 hH1 hnorm hE hH hHpos hquot
      hK hA
  have heq : F = F0 :=
    DGPS.Frontier.EX049.ex049_32_periodic_weak_pairs_have_periodic_ac_unique hT hFc hF0c hFp hF0p
      (hFg.filter_mono (ae_mono hmono)) (hF0g.filter_mono (ae_mono hmono))
  rw [heq]
  have hH' := hF0H t s
  rw [← Real.sqrt_eq_rpow] at hH'
  have hsE : Real.sqrt E ≤ Real.sqrt (4 * (A + 1)) := Real.sqrt_le_sqrt hEA
  have hmain : Real.sqrt (2 * π) * Real.exp |h| * Real.sqrt E *
      Real.sqrt (circDist_STR02937 t s) ≤ C * Real.sqrt (circDist_STR02937 t s) := by
    rw [hCdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsE (by positivity))
      (Real.sqrt_nonneg _)
  have hlt : Real.sqrt (circDist_STR02937 t s) < ε / (C + 1) := by
    have h1 := Real.sqrt_lt_sqrt (circDist_nonneg_STR02937 t s) hts
    rwa [Real.sqrt_sq (div_nonneg hε.le (by linarith))] at h1
  exact lt_of_le_of_lt (hH'.trans hmain) (modulus_small_STR02937 hC0 (Real.sqrt_nonneg _) hlt)

end DGPS.Frontier.STR029
