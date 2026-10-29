import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support

/-!
# EX049.26: Smooth step and normalized test bump

Task id and title: EX049.26, "Smooth step and normalized test bump" (node EX049, shared
infrastructure; library input: smooth bump supported in a prescribed open interval).

## Provides
* `DGPS.Frontier.EX049.ex049_26_smooth_step_normalized_test_bump` : the main statement, the
  conjunction of the step part and the bump part below.
* `DGPS.Frontier.EX049.ex049_26_smooth_step_normalized_test_bump_step` : there is a smooth
  `S : ℝ → ℝ` with `S x ∈ [0,1]` for all `x`, `S = 0` on `(-∞, 0]` and `S = 1` on `[1, ∞)`.
* `DGPS.Frontier.EX049.ex049_26_smooth_step_normalized_test_bump_bump` : for all reals
  `0 < a < b < L` there is a smooth nonnegative `β` with `Function.support β ⊆ Set.Icc a b`
  and `∫ x, β x = 1`.
* `DGPS.Frontier.EX049.zetaBase_EX04926` : the unnormalized bump
  `ζ(y) = S₀(4y - 1) S₀(3 - 4y)`, `S₀ = Real.smoothTransition`.
* `DGPS.Frontier.EX049.zetaBase_contDiff_EX04926` : `ζ` is smooth.
* `DGPS.Frontier.EX049.zetaBase_nonneg_EX04926` : `0 ≤ ζ`.
* `DGPS.Frontier.EX049.zetaBase_pos_EX04926` : `ζ > 0` on the open interval `(1/4, 3/4)`.
* `DGPS.Frontier.EX049.zetaBase_ne_zero_EX04926` : `ζ y ≠ 0` implies `1/4 < y < 3/4`.
* `DGPS.Frontier.EX049.zetaBase_eq_zero_EX04926` : `ζ y = 0` outside `[1/4, 3/4]`.
* `DGPS.Frontier.EX049.zetaBase_hasCompactSupport_EX04926` : `ζ` has compact support.
* `DGPS.Frontier.EX049.zetaBase_integrable_EX04926` : `ζ` is integrable.
* `DGPS.Frontier.EX049.zetaInt_EX04926` : the normalizing constant `c = ∫ ζ`.
* `DGPS.Frontier.EX049.zetaInt_pos_EX04926` : `0 < c`.
* `DGPS.Frontier.EX049.bump_EX04926` : the rescaled bump
  `β_{a,b}(x) = ((b - a) c)⁻¹ ζ((x - a)/(b - a))`.
* `DGPS.Frontier.EX049.bump_contDiff_EX04926` : `β_{a,b}` is smooth.
* `DGPS.Frontier.EX049.bump_nonneg_EX04926` : `0 ≤ β_{a,b}` for `a < b`.
* `DGPS.Frontier.EX049.bump_support_EX04926` : `support β_{a,b} ⊆ [a, b]` for `a < b`.
* `DGPS.Frontier.EX049.bump_integral_EX04926` : `∫ β_{a,b} = 1` for `a < b`.

## R5 notes
* Smoothness is read as `C^∞`, written `ContDiff ℝ ∞` (the `∞` notation of `ℕ∞`, not the
  analytic `ω`). The step and bump are not required to be analytic.
* `S : ℝ → [0,1]` is read as `∀ x, S x ∈ Set.Icc 0 1`. "Equal to zero on `(-∞, 0]`" is read as
  `∀ x, x ≤ 0 → S x = 0`, and "one on `[1, ∞)`" as `∀ x, 1 ≤ x → S x = 1`.
* Non-literal witness choice (design choice, not a change of statement): the specification's
  proof sketch defines `S` as the normalized integral `c⁻¹ ∫_{-∞}^x ζ`. Here the witness is
  Mathlib's `Real.smoothTransition`, which is smooth, takes values in `[0,1]` and has the two
  plateaus. The statement is existential, so the witness does not alter it. The integral
  construction was not formalized.
* "Supported in `[a, b]`" is read as the literal support `Function.support β ⊆ Set.Icc a b`.
  Closed support is not stated. The proof shows the support lies in the open interval `(a, b)`,
  which is stronger but is not claimed in the statement.
* `ζ` follows the specification's bump: it is supported in `[1/4, 3/4] ⊂ (0, 1)`, and it is
  positive at a point. The proof uses the stronger fact that `ζ > 0` on all of `(1/4, 3/4)`,
  needed to show `c > 0` through `integral_pos_iff_support_of_nonneg`.
* `L` is a free real variable constrained only by `0 < a < b < L`. The hypothesis `b < L` and
  `0 < a` are kept as listed in the statement; the proof does not use `L` or `0 < a`.
* Integrals are Bochner integrals with respect to Lebesgue measure `volume` on `ℝ`. No
  integrability hypothesis is added: `β` is continuous with compact support, so integrability
  is proved (`zetaBase_integrable_EX04926`).
* No hypothesis beyond the statement's own is assumed. Every Mathlib declaration used was checked
  at the pinned commit (`Mathlib.Analysis.SpecialFunctions.SmoothTransition`, the Bochner and
  interval integral API, and `MeasureTheory.Measure.integral_comp_div`).
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX049

noncomputable def zetaBase_EX04926 (y : ℝ) : ℝ :=
  Real.smoothTransition (4 * y - 1) * Real.smoothTransition (3 - 4 * y)

lemma zetaBase_contDiff_EX04926 : ContDiff ℝ ∞ zetaBase_EX04926 := by
  unfold zetaBase_EX04926
  fun_prop

lemma zetaBase_nonneg_EX04926 (y : ℝ) : 0 ≤ zetaBase_EX04926 y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma zetaBase_pos_EX04926 {y : ℝ} (h1 : 1 / 4 < y) (h2 : y < 3 / 4) :
    0 < zetaBase_EX04926 y :=
  mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
    (Real.smoothTransition.pos_of_pos (by linarith))

lemma zetaBase_ne_zero_EX04926 {y : ℝ} (hy : zetaBase_EX04926 y ≠ 0) :
    1 / 4 < y ∧ y < 3 / 4 := by
  unfold zetaBase_EX04926 at hy
  have h1 : Real.smoothTransition (4 * y - 1) ≠ 0 := left_ne_zero_of_mul hy
  have h2 : Real.smoothTransition (3 - 4 * y) ≠ 0 := right_ne_zero_of_mul hy
  rw [Ne, Real.smoothTransition.zero_iff_nonpos, not_le] at h1 h2
  constructor <;> linarith

lemma zetaBase_eq_zero_EX04926 {y : ℝ} (hy : y ∉ Set.Icc (1 / 4 : ℝ) (3 / 4)) :
    zetaBase_EX04926 y = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := zetaBase_ne_zero_EX04926 hne
  exact hy ⟨h1.le, h2.le⟩

lemma zetaBase_hasCompactSupport_EX04926 : HasCompactSupport zetaBase_EX04926 :=
  HasCompactSupport.intro isCompact_Icc (fun _ hy => zetaBase_eq_zero_EX04926 hy)

lemma zetaBase_integrable_EX04926 : Integrable zetaBase_EX04926 :=
  zetaBase_contDiff_EX04926.continuous.integrable_of_hasCompactSupport
    zetaBase_hasCompactSupport_EX04926

noncomputable def zetaInt_EX04926 : ℝ := ∫ y, zetaBase_EX04926 y

lemma zetaInt_pos_EX04926 : 0 < zetaInt_EX04926 := by
  unfold zetaInt_EX04926
  rw [integral_pos_iff_support_of_nonneg zetaBase_nonneg_EX04926 zetaBase_integrable_EX04926]
  have hsub : Set.Ioo (1 / 4 : ℝ) (3 / 4) ⊆ Function.support zetaBase_EX04926 :=
    fun y hy => (zetaBase_pos_EX04926 hy.1 hy.2).ne'
  have hvol : 0 < volume (Set.Ioo (1 / 4 : ℝ) (3 / 4)) := by
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    norm_num
  exact lt_of_lt_of_le hvol (measure_mono hsub)


/-- The rescaled normalized bump `x ↦ ((b - a) c)⁻¹ ζ((x - a)/(b - a))`, `c = ∫ ζ`. -/
noncomputable def bump_EX04926 (a b x : ℝ) : ℝ :=
  ((b - a) * zetaInt_EX04926)⁻¹ * zetaBase_EX04926 ((x - a) / (b - a))

lemma bump_contDiff_EX04926 (a b : ℝ) : ContDiff ℝ ∞ (bump_EX04926 a b) := by
  unfold bump_EX04926
  have h : ContDiff ℝ ∞ (fun x : ℝ => (x - a) / (b - a)) := by fun_prop
  exact contDiff_const.mul (zetaBase_contDiff_EX04926.comp h)

lemma bump_nonneg_EX04926 {a b : ℝ} (hab : a < b) (x : ℝ) : 0 ≤ bump_EX04926 a b x := by
  unfold bump_EX04926
  refine mul_nonneg ?_ (zetaBase_nonneg_EX04926 _)
  exact inv_nonneg.mpr (mul_nonneg (by linarith) zetaInt_pos_EX04926.le)

lemma bump_support_EX04926 {a b : ℝ} (hab : a < b) :
    Function.support (bump_EX04926 a b) ⊆ Set.Icc a b := by
  intro x hx
  have hx' : bump_EX04926 a b x ≠ 0 := hx
  unfold bump_EX04926 at hx'
  obtain ⟨h1, h2⟩ := zetaBase_ne_zero_EX04926 (right_ne_zero_of_mul hx')
  have hpos : 0 < b - a := by linarith
  rw [lt_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  constructor <;> linarith

lemma bump_integral_EX04926 {a b : ℝ} (hab : a < b) :
    ∫ x, bump_EX04926 a b x = 1 := by
  have hpos : 0 < b - a := by linarith
  have hc : zetaInt_EX04926 ≠ 0 := zetaInt_pos_EX04926.ne'
  unfold bump_EX04926
  rw [integral_const_mul]
  have h1 : ∫ x, zetaBase_EX04926 ((x - a) / (b - a))
      = ∫ x, zetaBase_EX04926 (x / (b - a)) :=
    integral_sub_right_eq_self (fun y => zetaBase_EX04926 (y / (b - a))) a
  rw [h1, MeasureTheory.Measure.integral_comp_div zetaBase_EX04926 (b - a), abs_of_pos hpos,
    smul_eq_mul]
  exact inv_mul_cancel₀ (mul_ne_zero hpos.ne' hc)

/-- Smooth step: Mathlib's `Real.smoothTransition`. -/
theorem ex049_26_smooth_step_normalized_test_bump_step :
    ∃ S : ℝ → ℝ, ContDiff ℝ ∞ S ∧ (∀ x, S x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, x ≤ 0 → S x = 0) ∧ (∀ x, 1 ≤ x → S x = 1) :=
  ⟨Real.smoothTransition, Real.smoothTransition.contDiff,
    fun x => ⟨Real.smoothTransition.nonneg x, Real.smoothTransition.le_one x⟩,
    fun _ hx => Real.smoothTransition.zero_of_nonpos hx,
    fun _ hx => Real.smoothTransition.one_of_one_le hx⟩

theorem ex049_26_smooth_step_normalized_test_bump_bump :
    ∀ a b L : ℝ, 0 < a → a < b → b < L →
      ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ x, 0 ≤ β x) ∧
        Function.support β ⊆ Set.Icc a b ∧ ∫ x, β x = 1 := by
  intro a b _ _ hab _
  exact ⟨bump_EX04926 a b, bump_contDiff_EX04926 a b, bump_nonneg_EX04926 hab,
    bump_support_EX04926 hab, bump_integral_EX04926 hab⟩

theorem ex049_26_smooth_step_normalized_test_bump :
    (∃ S : ℝ → ℝ, ContDiff ℝ ∞ S ∧ (∀ x, S x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, x ≤ 0 → S x = 0) ∧ (∀ x, 1 ≤ x → S x = 1)) ∧
    (∀ a b L : ℝ, 0 < a → a < b → b < L →
      ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ x, 0 ≤ β x) ∧
        Function.support β ⊆ Set.Icc a b ∧ ∫ x, β x = 1) :=
  ⟨ex049_26_smooth_step_normalized_test_bump_step,
    ex049_26_smooth_step_normalized_test_bump_bump⟩

end DGPS.Frontier.EX049
