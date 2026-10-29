import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# STR029.04: Reference symmetries and quantitative density bounds

Task id: STR029.04 (node STR029, size L, leaf formalization).
Title: Reference symmetries and quantitative density bounds.

Statement (specification): for every real `h`, `q_h` is positive and smooth, is invariant under
`t ↦ t + 2π/3` and reflection, and `q_{-h}(t) = q_h(t + π)`. For `|h| ≤ 1/1000`,
`e^{-2|h|} ≤ q_h ≤ e^{2|h|}` and `‖q_h - 1‖∞ ≤ 3|h|`. Every first harmonic `p` satisfies
`∫ p q_h = 0` and `∫ p² q_h = ∫ p'² q_h = ‖p‖₂²`.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_04_reference_symmetries_quantitative_density_bounds`: the main theorem,
  the conjunction of the three parts below.
* `DGPS.Frontier.STR029.str029_04_reference_symmetries_quantitative_density_bounds_symmetries`: for every
  real `h`, `q_h > 0`, `q_h` is `C^∞`, `q_h(t + 2π/3) = q_h(t)`, `q_h(-t) = q_h(t)` and
  `q_{-h}(t) = q_h(t + π)`.
* `DGPS.Frontier.STR029.str029_04_reference_symmetries_quantitative_density_bounds_normalizer`: for every
  real `h`, the normalizer `∫ e^{h cos 3t} dm` lies between `e^{-|h|}` and `e^{|h|}`.
* `DGPS.Frontier.STR029.str029_04_reference_symmetries_quantitative_density_bounds_bounds`: for
  `|h| ≤ 1/1000`, `e^{-2|h|} ≤ q_h(t) ≤ e^{2|h|}` and `|q_h(t) - 1| ≤ 3|h|` for every `t`; also the
  supremum form `⨆ t, |q_h(t) - 1| ≤ 3|h|`.
* `DGPS.Frontier.STR029.str029_04_reference_symmetries_quantitative_density_bounds_harmonic`: for every real
  `h` and every first harmonic `p`, `∫ p q_h dm = 0` and `∫ p² q_h dm = ∫ p'² q_h dm = ∫ p² dm`.
* `DGPS.Frontier.STR029.str029_04_reference_symmetries_quantitative_density_bounds_harmonic_value`: the
  common value `‖p‖₂² = (a² + b²)/2` for `p = a cos t + b sin t`.
* `DGPS.Frontier.STR029.normInt_STR02904`, `DGPS.Frontier.STR029.qT_STR02904`,
  `DGPS.Frontier.STR029.IsFirstHarmonic_STR02904`: the normalized integral, the reference density and the
  first-harmonic predicate used in the statements.

R5 notes:
* Carriers are concrete: `q_h` is a function `ℝ → ℝ` of the angle `t = 2πx`, and `∫ f dm` is
  `normInt_STR02904 f = (2π)⁻¹ ∫_0^{2π} f dt` (interval integral, Mathlib convention for non-integrable
  integrands). `qT_STR02904 h t = e^{h cos 3t} / ∫ e^{h cos 3s} dm` has the same body as the
  `.01` declaration `qT_STR02901`, with `normInt_STR02904` for `meanT_STR02901`, so the two agree by
  `rfl` once both modules are available. This unit does not depend on `.01`; the identification with
  `DGPS.Examples.ThreeSpeciesCircle.referenceDensity` and `AbsoluteDensity 1` is the business of `.01`.
* "Invariant under reflection" is read as `q_h(-t) = q_h(t)`, the reflection fixing `t = 0`; reflections
  about other centers follow from it together with the invariance under `2π/3` and periodicity.
* "`q_h` is smooth" is `ContDiff ℝ ∞ (qT_STR02904 h)`. Periodicity of `q_h` is also proved
  (`periodic_STR02904`) because the harmonic identities use it.
* The supremum norm `‖q_h - 1‖∞` is stated as the pointwise bound `|q_h(t) - 1| ≤ 3|h|` for all `t`,
  and in addition as `⨆ t, |q_h(t) - 1| ≤ 3|h|` (the family is bounded, so the supremum is genuine).
* The bound `e^{-2|h|} ≤ q_h ≤ e^{2|h|}` holds for every real `h`, not only `|h| ≤ 1/1000`; it is stated
  under the specification's hypothesis in the main theorem, and unconditionally in the helper
  `qT_bounds_STR02904`. Only the estimate `e^{2|h|} - 1 ≤ 3|h|` needs the smallness `|h| ≤ 1/1000`.
* A "first harmonic" is a function `p` with `p t = a cos t + b sin t` for all `t` and some reals `a, b`
  (`IsFirstHarmonic_STR02904`). The derivative `p'` is `deriv p` (derivative in the variable `t`), and
  `‖p‖₂² = ∫ p² dm = normInt_STR02904 (p ^ 2)`. The harmonic identities are proved for every real `h`
  (the specification places them next to the smallness hypothesis, but the proof only uses the
  invariance under `2π/3`).
* Proof route. The exponential-series bound `e^x ≤ (1 - x)⁻¹` (`Real.exp_bound_div_one_sub_of_interval`)
  with `x = 2|h| ≤ 1/500` gives `e^{2|h|} - 1 ≤ 2|h| / (1 - 1/500) ≤ 3|h|`; this replaces the derivative
  bound of the specification by the same series estimate applied directly. The vanishing of the first
  and second Fourier coefficients of `q_h` follows from `q_h(t + 2π/3) = q_h(t)`: the real and imaginary
  parts of the translation identity form a rotation by the angle `2πn/3` acting on the coefficient pair,
  and a rotation by an angle with cosine `≠ 1` fixes only the origin. The identities for `p²` and `p'²`
  expand `p²` into the mean and the second harmonic.
-/

open scoped Real ContDiff

namespace DGPS.Frontier.STR029

/-- The normalized integral over one period: `∫ f dm = (2π)⁻¹ ∫_0^{2π} f dt`. -/
noncomputable def normInt_STR02904 (f : ℝ → ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), f t

/-- The reference density `q_h(t) = e^{h cos 3t} / ∫ e^{h cos 3s} dm`. -/
noncomputable def qT_STR02904 (h t : ℝ) : ℝ :=
  Real.exp (h * Real.cos (3 * t)) /
    normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s)))

/-- A first harmonic: `p t = a cos t + b sin t` for all `t`. -/
def IsFirstHarmonic_STR02904 (p : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ t, p t = a * Real.cos t + b * Real.sin t

theorem normInt_const_STR02904 (c : ℝ) : normInt_STR02904 (fun _ => c) = c := by
  have hpi : (2 * π) ≠ 0 := by positivity
  simp only [normInt_STR02904, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem normInt_const_mul_STR02904 (c : ℝ) (f : ℝ → ℝ) :
    normInt_STR02904 (fun t => c * f t) = c * normInt_STR02904 f := by
  simp only [normInt_STR02904, intervalIntegral.integral_const_mul]
  ring

theorem normInt_add_STR02904 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    normInt_STR02904 (fun t => f t + g t) = normInt_STR02904 f + normInt_STR02904 g := by
  simp only [normInt_STR02904]
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem normInt_bounds_STR02904 {f : ℝ → ℝ} {c d : ℝ} (hf : Continuous f) (hc : ∀ t, c ≤ f t)
    (hd : ∀ t, f t ≤ d) : c ≤ normInt_STR02904 f ∧ normInt_STR02904 f ≤ d := by
  have hpi : 0 < 2 * π := by positivity
  have hinv : 0 < (2 * π)⁻¹ := inv_pos.2 hpi
  have hlo : ∫ _ in (0 : ℝ)..(2 * π), c ≤ ∫ t in (0 : ℝ)..(2 * π), f t :=
    intervalIntegral.integral_mono_on hpi.le intervalIntegrable_const (hf.intervalIntegrable _ _)
      (fun t _ => hc t)
  have hhi : ∫ t in (0 : ℝ)..(2 * π), f t ≤ ∫ _ in (0 : ℝ)..(2 * π), d :=
    intervalIntegral.integral_mono_on hpi.le (hf.intervalIntegrable _ _) intervalIntegrable_const
      (fun t _ => hd t)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlo hhi
  have e1 : (2 * π)⁻¹ * (2 * π * c) = c := by field_simp
  have e2 : (2 * π)⁻¹ * (2 * π * d) = d := by field_simp
  refine ⟨?_, ?_⟩
  · calc c = (2 * π)⁻¹ * (2 * π * c) := e1.symm
      _ ≤ normInt_STR02904 f := mul_le_mul_of_nonneg_left hlo hinv.le
  · calc normInt_STR02904 f ≤ (2 * π)⁻¹ * (2 * π * d) := mul_le_mul_of_nonneg_left hhi hinv.le
      _ = d := e2

theorem normInt_shift_STR02904 {F : ℝ → ℝ} (hper : Function.Periodic F (2 * π)) (τ : ℝ) :
    normInt_STR02904 (fun t => F (t + τ)) = normInt_STR02904 F := by
  simp only [normInt_STR02904]
  congr 1
  rw [intervalIntegral.integral_comp_add_right F τ, zero_add, add_comm (2 * π) τ]
  have := hper.intervalIntegral_add_eq τ 0
  rw [zero_add] at this
  exact this

/-- The exponential of `h cos 3s` is a continuous periodic function. -/
theorem expCos_continuous_STR02904 (h : ℝ) :
    Continuous (fun s : ℝ => Real.exp (h * Real.cos (3 * s))) := by fun_prop

theorem cos3_periodic_STR02904 : Function.Periodic (fun s : ℝ => Real.cos (3 * s)) (2 * π) := by
  intro t
  have : 3 * (t + 2 * π) = 3 * t + ((3 : ℕ) : ℝ) * (2 * π) := by push_cast; ring
  simp only [this, Real.cos_add_nat_mul_two_pi]

theorem expCos_periodic_STR02904 (h : ℝ) :
    Function.Periodic (fun s : ℝ => Real.exp (h * Real.cos (3 * s))) (2 * π) := by
  intro t
  simp only [cos3_periodic_STR02904 t]

theorem abs_hcos_le_STR02904 (h t : ℝ) : |h * Real.cos (3 * t)| ≤ |h| := by
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The normalizer `∫ e^{h cos 3t} dm` lies between `e^{-|h|}` and `e^{|h|}`. -/
theorem str029_04_reference_symmetries_quantitative_density_bounds_normalizer (h : ℝ) :
    Real.exp (-|h|) ≤ normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))) ∧
      normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))) ≤ Real.exp |h| := by
  refine normInt_bounds_STR02904 (expCos_continuous_STR02904 h) (fun t => ?_) (fun t => ?_)
  · exact Real.exp_le_exp.2 (abs_le.1 (abs_hcos_le_STR02904 h t)).1
  · exact Real.exp_le_exp.2 (abs_le.1 (abs_hcos_le_STR02904 h t)).2

theorem partition_pos_STR02904 (h : ℝ) :
    0 < normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))) :=
  lt_of_lt_of_le (Real.exp_pos _)
    (str029_04_reference_symmetries_quantitative_density_bounds_normalizer h).1

theorem qT_pos_STR02904 (h t : ℝ) : 0 < qT_STR02904 h t :=
  div_pos (Real.exp_pos _) (partition_pos_STR02904 h)

theorem qT_eq_STR02904 (h t : ℝ) :
    qT_STR02904 h t =
      (normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))))⁻¹ *
        Real.exp (h * Real.cos (3 * t)) := by
  rw [qT_STR02904, div_eq_inv_mul]

theorem contDiff_qT_STR02904 (h : ℝ) : ContDiff ℝ ∞ (qT_STR02904 h) := by
  have : qT_STR02904 h = fun t =>
      Real.exp (h * Real.cos (3 * t)) /
        normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))) := rfl
  rw [this]
  exact (Real.contDiff_exp.comp
    (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)))).div_const _

theorem continuous_qT_STR02904 (h : ℝ) : Continuous (qT_STR02904 h) :=
  (contDiff_qT_STR02904 h).continuous

theorem periodic_STR02904 (h : ℝ) : Function.Periodic (qT_STR02904 h) (2 * π) := by
  intro t
  simp only [qT_STR02904, cos3_periodic_STR02904 t]

theorem shift_STR02904 (h t : ℝ) : qT_STR02904 h (t + 2 * π / 3) = qT_STR02904 h t := by
  have : 3 * (t + 2 * π / 3) = 3 * t + 2 * π := by ring
  simp only [qT_STR02904, this, Real.cos_add_two_pi]

theorem reflect_STR02904 (h t : ℝ) : qT_STR02904 h (-t) = qT_STR02904 h t := by
  simp only [qT_STR02904, mul_neg, Real.cos_neg]

theorem partition_neg_STR02904 (h : ℝ) :
    normInt_STR02904 (fun s => Real.exp (-h * Real.cos (3 * s))) =
      normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))) := by
  have key : ∀ s : ℝ, Real.exp (-h * Real.cos (3 * s)) =
      (fun u : ℝ => Real.exp (h * Real.cos (3 * u))) (s + π) := by
    intro s
    have e : 3 * (s + π) = (3 * s + π) + 2 * π := by ring
    simp only [e, Real.cos_add_two_pi, Real.cos_add_pi]
    congr 1
    ring
  simp only [key]
  exact normInt_shift_STR02904 (expCos_periodic_STR02904 h) π

theorem neg_STR02904 (h t : ℝ) : qT_STR02904 (-h) t = qT_STR02904 h (t + π) := by
  have e : 3 * (t + π) = (3 * t + π) + 2 * π := by ring
  simp only [qT_STR02904, partition_neg_STR02904 h, e, Real.cos_add_two_pi, Real.cos_add_pi]
  congr 2
  ring

/-- Symmetries of the reference density, for every real `h`. -/
theorem str029_04_reference_symmetries_quantitative_density_bounds_symmetries (h : ℝ) :
    (∀ t, 0 < qT_STR02904 h t) ∧ ContDiff ℝ ∞ (qT_STR02904 h) ∧
      (∀ t, qT_STR02904 h (t + 2 * π / 3) = qT_STR02904 h t) ∧
      (∀ t, qT_STR02904 h (-t) = qT_STR02904 h t) ∧
      (∀ t, qT_STR02904 (-h) t = qT_STR02904 h (t + π)) :=
  ⟨qT_pos_STR02904 h, contDiff_qT_STR02904 h, shift_STR02904 h, reflect_STR02904 h,
    neg_STR02904 h⟩

theorem qT_bounds_STR02904 (h t : ℝ) :
    Real.exp (-(2 * |h|)) ≤ qT_STR02904 h t ∧ qT_STR02904 h t ≤ Real.exp (2 * |h|) := by
  obtain ⟨hZlo, hZhi⟩ := str029_04_reference_symmetries_quantitative_density_bounds_normalizer h
  have hZ := partition_pos_STR02904 h
  have hnum := abs_le.1 (abs_hcos_le_STR02904 h t)
  have e1 : Real.exp (-(2 * |h|)) * Real.exp |h| = Real.exp (-|h|) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (2 * |h|) * Real.exp (-|h|) = Real.exp |h| := by
    rw [← Real.exp_add]; congr 1; ring
  unfold qT_STR02904
  constructor
  · rw [le_div_iff₀ hZ]
    calc Real.exp (-(2 * |h|)) * normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s)))
        ≤ Real.exp (-(2 * |h|)) * Real.exp |h| :=
          mul_le_mul_of_nonneg_left hZhi (Real.exp_pos _).le
      _ = Real.exp (-|h|) := e1
      _ ≤ Real.exp (h * Real.cos (3 * t)) := Real.exp_le_exp.2 hnum.1
  · rw [div_le_iff₀ hZ]
    calc Real.exp (h * Real.cos (3 * t)) ≤ Real.exp |h| := Real.exp_le_exp.2 hnum.2
      _ = Real.exp (2 * |h|) * Real.exp (-|h|) := e2.symm
      _ ≤ Real.exp (2 * |h|) * normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))) :=
          mul_le_mul_of_nonneg_left hZlo (Real.exp_pos _).le

theorem exp_two_sub_one_le_STR02904 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 1000) :
    Real.exp (2 * s) - 1 ≤ 3 * s := by
  have hx : 2 * s < 1 := by linarith
  have h1 := Real.exp_bound_div_one_sub_of_interval (x := 2 * s) (by linarith) hx
  have hpos : 0 < 1 - 2 * s := by linarith
  have h2 : 1 / (1 - 2 * s) ≤ 1 + 3 * s := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

/-- Quantitative bounds on the reference density for `|h| ≤ 1/1000`. -/
theorem str029_04_reference_symmetries_quantitative_density_bounds_bounds (h : ℝ)
    (hh : |h| ≤ 1 / 1000) :
    (∀ t, Real.exp (-(2 * |h|)) ≤ qT_STR02904 h t ∧ qT_STR02904 h t ≤ Real.exp (2 * |h|)) ∧
      (∀ t, |qT_STR02904 h t - 1| ≤ 3 * |h|) ∧ (⨆ t, |qT_STR02904 h t - 1|) ≤ 3 * |h| := by
  have hpt : ∀ t, |qT_STR02904 h t - 1| ≤ 3 * |h| := by
    intro t
    obtain ⟨hlo, hhi⟩ := qT_bounds_STR02904 h t
    have hup := exp_two_sub_one_le_STR02904 (abs_nonneg h) hh
    have hdown := Real.add_one_le_exp (-(2 * |h|))
    have habs := abs_nonneg h
    rw [abs_le]
    constructor <;> linarith
  exact ⟨qT_bounds_STR02904 h, hpt, ciSup_le hpt⟩

theorem cos_two_pi_div_three_STR02904 : Real.cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem cos_four_pi_div_three_STR02904 : Real.cos (2 * (2 * π / 3)) = -(1 / 2) := by
  rw [show 2 * (2 * π / 3) = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]

/-- A weight invariant under the shift `2π/3` has vanishing `n`-th Fourier coefficients when
`cos (2π n / 3) ≠ 1`. -/
theorem fourier_vanish_STR02904 {w : ℝ → ℝ} (hw : Continuous w)
    (hper : Function.Periodic w (2 * π)) (hshift : ∀ t, w (t + 2 * π / 3) = w t) (n : ℕ)
    (hn : Real.cos (n * (2 * π / 3)) ≠ 1) :
    normInt_STR02904 (fun t => Real.cos (n * t) * w t) = 0 ∧
      normInt_STR02904 (fun t => Real.sin (n * t) * w t) = 0 := by
  set θ : ℝ := n * (2 * π / 3) with hθ
  set C := normInt_STR02904 (fun t => Real.cos (n * t) * w t) with hC
  set S := normInt_STR02904 (fun t => Real.sin (n * t) * w t) with hS
  have hcp : Function.Periodic (fun t : ℝ => Real.cos (n * t) * w t) (2 * π) := by
    intro t
    have : (n : ℝ) * (t + 2 * π) = n * t + n * (2 * π) := by ring
    simp only [this, Real.cos_add_nat_mul_two_pi, hper t]
  have hsp : Function.Periodic (fun t : ℝ => Real.sin (n * t) * w t) (2 * π) := by
    intro t
    have : (n : ℝ) * (t + 2 * π) = n * t + n * (2 * π) := by ring
    simp only [this, Real.sin_add_nat_mul_two_pi, hper t]
  have e1 : C = Real.cos θ * C + (-Real.sin θ) * S := by
    have h1 := normInt_shift_STR02904 hcp (2 * π / 3)
    have h2 : (fun t : ℝ => Real.cos (n * (t + 2 * π / 3)) * w (t + 2 * π / 3)) =
        fun t => Real.cos θ * (Real.cos (n * t) * w t) +
          (-Real.sin θ) * (Real.sin (n * t) * w t) := by
      funext t
      have : (n : ℝ) * (t + 2 * π / 3) = n * t + θ := by rw [hθ]; ring
      rw [this, hshift t, Real.cos_add]
      ring
    rw [h2, normInt_add_STR02904 (by fun_prop) (by fun_prop), normInt_const_mul_STR02904,
      normInt_const_mul_STR02904] at h1
    exact h1.symm
  have e2 : S = Real.sin θ * C + Real.cos θ * S := by
    have h1 := normInt_shift_STR02904 hsp (2 * π / 3)
    have h2 : (fun t : ℝ => Real.sin (n * (t + 2 * π / 3)) * w (t + 2 * π / 3)) =
        fun t => Real.sin θ * (Real.cos (n * t) * w t) +
          Real.cos θ * (Real.sin (n * t) * w t) := by
      funext t
      have : (n : ℝ) * (t + 2 * π / 3) = n * t + θ := by rw [hθ]; ring
      rw [this, hshift t, Real.sin_add]
      ring
    rw [h2, normInt_add_STR02904 (by fun_prop) (by fun_prop), normInt_const_mul_STR02904,
      normInt_const_mul_STR02904] at h1
    exact h1.symm
  have pyth := Real.sin_sq_add_cos_sq θ
  have hne : (2 - 2 * Real.cos θ) ≠ 0 := by
    intro h0
    exact hn (by linarith)
  constructor
  · have : (2 - 2 * Real.cos θ) * C = 0 := by
      linear_combination (1 - Real.cos θ) * e1 - Real.sin θ * e2 - C * pyth
    exact (mul_eq_zero.1 this).resolve_left hne
  · have : (2 - 2 * Real.cos θ) * S = 0 := by
      linear_combination (1 - Real.cos θ) * e2 + Real.sin θ * e1 - S * pyth
    exact (mul_eq_zero.1 this).resolve_left hne

/-- First and second moments of a first harmonic against a shift-invariant unit-mass weight. -/
theorem harmonic_weight_STR02904 {w : ℝ → ℝ} (hw : Continuous w)
    (hper : Function.Periodic w (2 * π)) (hshift : ∀ t, w (t + 2 * π / 3) = w t)
    (hnorm : normInt_STR02904 w = 1) (a b : ℝ) :
    normInt_STR02904 (fun t => (a * Real.cos t + b * Real.sin t) * w t) = 0 ∧
      normInt_STR02904 (fun t => (a * Real.cos t + b * Real.sin t) ^ 2 * w t) =
        (a ^ 2 + b ^ 2) / 2 := by
  have h1 := fourier_vanish_STR02904 hw hper hshift 1
    (by rw [Nat.cast_one, one_mul, cos_two_pi_div_three_STR02904]; norm_num)
  have h2 := fourier_vanish_STR02904 hw hper hshift 2
    (by rw [Nat.cast_ofNat, cos_four_pi_div_three_STR02904]; norm_num)
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at h1 h2
  constructor
  · have : (fun t => (a * Real.cos t + b * Real.sin t) * w t) =
        fun t => a * (Real.cos t * w t) + b * (Real.sin t * w t) := by
      funext t; ring
    rw [this, normInt_add_STR02904 (by fun_prop) (by fun_prop), normInt_const_mul_STR02904,
      normInt_const_mul_STR02904, h1.1, h1.2]
    ring
  · have : (fun t => (a * Real.cos t + b * Real.sin t) ^ 2 * w t) =
        fun t => ((a ^ 2 + b ^ 2) / 2) * w t +
          (((a ^ 2 - b ^ 2) / 2) * (Real.cos (2 * t) * w t) +
            (a * b) * (Real.sin (2 * t) * w t)) := by
      funext t
      have hs := Real.sin_sq_add_cos_sq t
      rw [Real.cos_two_mul, Real.sin_two_mul]
      linear_combination (b ^ 2 * w t) * hs
    rw [this, normInt_add_STR02904 (by fun_prop) (by fun_prop), normInt_const_mul_STR02904,
      normInt_add_STR02904 (by fun_prop) (by fun_prop), normInt_const_mul_STR02904,
      normInt_const_mul_STR02904, h2.1, h2.2, hnorm]
    ring

theorem deriv_harmonic_STR02904 (a b : ℝ) :
    deriv (fun t => a * Real.cos t + b * Real.sin t) =
      fun t => b * Real.cos t + (-a) * Real.sin t := by
  funext t
  have : HasDerivAt (fun t => a * Real.cos t + b * Real.sin t)
      (a * -Real.sin t + b * Real.cos t) t :=
    ((Real.hasDerivAt_cos t).const_mul a).add ((Real.hasDerivAt_sin t).const_mul b)
  rw [this.deriv]
  ring

/-- The common value of `‖p‖₂²`, `∫ p² q_h` and `∫ p'² q_h` for `p = a cos t + b sin t`. -/
theorem str029_04_reference_symmetries_quantitative_density_bounds_harmonic_value (a b : ℝ) :
    normInt_STR02904 (fun t => (a * Real.cos t + b * Real.sin t) ^ 2) = (a ^ 2 + b ^ 2) / 2 := by
  have := (harmonic_weight_STR02904 (w := fun _ => (1 : ℝ)) continuous_const
    (fun _ => rfl) (fun _ => rfl) (normInt_const_STR02904 1) a b).2
  simpa only [mul_one] using this

/-- First harmonics are orthogonal to `q_h`, and `∫ p² q_h = ∫ p'² q_h = ‖p‖₂²`. -/
theorem str029_04_reference_symmetries_quantitative_density_bounds_harmonic (h : ℝ) (p : ℝ → ℝ)
    (hp : IsFirstHarmonic_STR02904 p) :
    normInt_STR02904 (fun t => p t * qT_STR02904 h t) = 0 ∧
      normInt_STR02904 (fun t => p t ^ 2 * qT_STR02904 h t) = normInt_STR02904 (fun t => p t ^ 2) ∧
      normInt_STR02904 (fun t => deriv p t ^ 2 * qT_STR02904 h t) =
        normInt_STR02904 (fun t => p t ^ 2) := by
  obtain ⟨a, b, hab⟩ := hp
  have hpe : p = fun t => a * Real.cos t + b * Real.sin t := funext hab
  subst hpe
  have hq := continuous_qT_STR02904 h
  have hnorm : normInt_STR02904 (qT_STR02904 h) = 1 := by
    have : qT_STR02904 h = fun t =>
        (normInt_STR02904 (fun s => Real.exp (h * Real.cos (3 * s))))⁻¹ *
          Real.exp (h * Real.cos (3 * t)) := funext (qT_eq_STR02904 h)
    rw [this, normInt_const_mul_STR02904]
    exact inv_mul_cancel₀ (partition_pos_STR02904 h).ne'
  obtain ⟨m1, m2⟩ := harmonic_weight_STR02904 hq (periodic_STR02904 h) (shift_STR02904 h) hnorm a b
  obtain ⟨-, d2⟩ := harmonic_weight_STR02904 hq (periodic_STR02904 h) (shift_STR02904 h) hnorm b (-a)
  rw [deriv_harmonic_STR02904,
    str029_04_reference_symmetries_quantitative_density_bounds_harmonic_value]
  refine ⟨m1, m2, ?_⟩
  rw [d2]
  ring

/-- Main theorem: reference symmetries and quantitative density bounds. -/
theorem str029_04_reference_symmetries_quantitative_density_bounds :
    (∀ h : ℝ, (∀ t, 0 < qT_STR02904 h t) ∧ ContDiff ℝ ∞ (qT_STR02904 h) ∧
      (∀ t, qT_STR02904 h (t + 2 * π / 3) = qT_STR02904 h t) ∧
      (∀ t, qT_STR02904 h (-t) = qT_STR02904 h t) ∧
      (∀ t, qT_STR02904 (-h) t = qT_STR02904 h (t + π))) ∧
    (∀ h : ℝ, |h| ≤ 1 / 1000 →
      (∀ t, Real.exp (-(2 * |h|)) ≤ qT_STR02904 h t ∧ qT_STR02904 h t ≤ Real.exp (2 * |h|)) ∧
        (∀ t, |qT_STR02904 h t - 1| ≤ 3 * |h|) ∧ (⨆ t, |qT_STR02904 h t - 1|) ≤ 3 * |h|) ∧
    (∀ (h : ℝ) (p : ℝ → ℝ), IsFirstHarmonic_STR02904 p →
      normInt_STR02904 (fun t => p t * qT_STR02904 h t) = 0 ∧
        normInt_STR02904 (fun t => p t ^ 2 * qT_STR02904 h t) =
          normInt_STR02904 (fun t => p t ^ 2) ∧
        normInt_STR02904 (fun t => deriv p t ^ 2 * qT_STR02904 h t) =
          normInt_STR02904 (fun t => p t ^ 2)) :=
  ⟨str029_04_reference_symmetries_quantitative_density_bounds_symmetries,
    str029_04_reference_symmetries_quantitative_density_bounds_bounds,
    str029_04_reference_symmetries_quantitative_density_bounds_harmonic⟩

end DGPS.Frontier.STR029
