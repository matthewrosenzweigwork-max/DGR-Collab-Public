import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# STR029.33: Fourier coefficients of the weak derivative

Task id: STR029.33. Title: Fourier coefficients of the weak derivative (node STR029, size M).

Provides:
* `DGPS.Frontier.STR029.normInt_STR02933`: the normalized integral `∫ f dm = (2π)⁻¹ ∫_{(0,2π]} f dt`.
* `DGPS.Frontier.STR029.cosCoeff_STR02933`: `c_n(w) = 2 ∫ w cos(nt) dm`.
* `DGPS.Frontier.STR029.sinCoeff_STR02933`: `s_n(w) = 2 ∫ w sin(nt) dm`.
* `DGPS.Frontier.STR029.IsSmoothPeriodicTest_STR02933`: `φ` is `C^∞` and `2π`-periodic on `ℝ`.
* `DGPS.Frontier.STR029.IsPeriodicWeakDerivative_STR02933`: `w` and `g` are periodic `L²` functions and `g` is
  the weak derivative of `w` against all smooth periodic tests (periodic `H¹` with weak derivative `g`).
* `DGPS.Frontier.STR029.str029_33_fourier_coefficients_weak_derivative`: for `n ≥ 1`, the cosine coefficient of
  `g` is `n s_n(w)`, the sine coefficient of `g` is `-n c_n(w)`, and `∫ g dm = 0`.
* `DGPS.Frontier.STR029.str029_33_fourier_coefficients_weak_derivative_mean`: `∫ g dm = 0`, the constant-test part.
* `DGPS.Frontier.STR029.normInt_mul_const_STR02933`: `∫ c f dm = c ∫ f dm`.
* `DGPS.Frontier.STR029.cos_test_STR02933`: `cos(n·)` is a smooth periodic test.
* `DGPS.Frontier.STR029.sin_test_STR02933`: `sin(n·)` is a smooth periodic test.
* `DGPS.Frontier.STR029.const_test_STR02933`: the constant `1` is a smooth periodic test.
* `DGPS.Frontier.STR029.deriv_cos_STR02933`: `d/dt cos(nt) = -n sin(nt)`.
* `DGPS.Frontier.STR029.deriv_sin_STR02933`: `d/dt sin(nt) = n cos(nt)`.
* `DGPS.Frontier.STR029.normInt_weight_cos_STR02933`: `∫ w cos'(nt) dm = -n ∫ w sin(nt) dm`.
* `DGPS.Frontier.STR029.normInt_weight_sin_STR02933`: `∫ w sin'(nt) dm = n ∫ w cos(nt) dm`.

R5 notes:
* Carriers: concrete functions `ℝ → ℝ` that are `2π`-periodic (`Function.Periodic`), not functions on
  `Torus 1`. The derivative is the derivative in the variable `t = 2πx` (no factor `2π` from `x`), as stated.
* The circle is the period `(0, 2π]`, with `dm = dt/(2π)` realized as the factor `(2π)⁻¹` times Lebesgue
  integration over `Ioc 0 (2π)` (the specification writes `[0, 2π)`; the endpoint is a null set).
  Integrals are Bochner integrals with the Mathlib convention (value `0` if not integrable). The `L²` hypotheses make the test integrands integrable (bounded smooth tests),
  but that integrability is not formalized: the proof uses only the test identity and linearity.
* "Periodic `H¹`" is read as: `w` periodic and in `L²`, and `g` periodic and in `L²`, with the weak identity
  `∫ g φ dm = -∫ w φ' dm` for every `C^∞` `2π`-periodic `φ`. The weak derivative is the given `g`; no
  existence or a.e.-uniqueness of the weak derivative is asserted or needed.
* The specification's tests are "smooth periodic"; read as `ContDiff ℝ ∞` together with `Function.Periodic φ (2π)`.
* `n` is a natural number with `1 ≤ n`, as specified. The identities also hold for `n = 0`; the hypothesis is kept
  as stated and is not used by the proof. Its binder is spelled `_hn` only to silence the unused-variable linter.
* Coefficients use the factor `2` and the cast `(n : ℝ)`, matching `c_n = 2∫w cos nt dm` and `s_n = 2∫w sin nt dm`.
-/

open MeasureTheory Set Real
open scoped ContDiff

namespace DGPS.Frontier.STR029

/-- The normalized integral `∫ f dm = (2π)⁻¹ ∫_{(0, 2π]} f(t) dt` over one period. -/
noncomputable def normInt_STR02933 (f : ℝ → ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in Ioc 0 (2 * π), f t

/-- The Fourier cosine coefficient `c_n(w) = 2 ∫ w(t) cos(nt) dm`. -/
noncomputable def cosCoeff_STR02933 (w : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 * normInt_STR02933 (fun t => w t * Real.cos (n * t))

/-- The Fourier sine coefficient `s_n(w) = 2 ∫ w(t) sin(nt) dm`. -/
noncomputable def sinCoeff_STR02933 (w : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 * normInt_STR02933 (fun t => w t * Real.sin (n * t))

/-- `φ` is a `C^∞` function on `ℝ` with period `2π`. -/
def IsSmoothPeriodicTest_STR02933 (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Function.Periodic φ (2 * π)

/-- `w` is a periodic `H¹` function with weak derivative `g`: both are `2π`-periodic and `L²` on the
period, and `∫ g φ dm = -∫ w φ' dm` for every smooth periodic test `φ`. -/
def IsPeriodicWeakDerivative_STR02933 (w g : ℝ → ℝ) : Prop :=
  (Function.Periodic w (2 * π) ∧ MemLp w 2 (volume.restrict (Ioc 0 (2 * π)))) ∧
    (Function.Periodic g (2 * π) ∧ MemLp g 2 (volume.restrict (Ioc 0 (2 * π)))) ∧
    ∀ φ : ℝ → ℝ, IsSmoothPeriodicTest_STR02933 φ →
      normInt_STR02933 (fun t => g t * φ t) = -normInt_STR02933 (fun t => w t * deriv φ t)

theorem normInt_mul_const_STR02933 (c : ℝ) (f : ℝ → ℝ) :
    normInt_STR02933 (fun t => c * f t) = c * normInt_STR02933 f := by
  unfold normInt_STR02933
  rw [integral_const_mul]
  ring

theorem cos_test_STR02933 (n : ℕ) : IsSmoothPeriodicTest_STR02933 (fun t => Real.cos (n * t)) := by
  refine ⟨Real.contDiff_cos.comp (contDiff_const.mul contDiff_id), fun t => ?_⟩
  show Real.cos (n * (t + 2 * π)) = Real.cos (n * t)
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

theorem sin_test_STR02933 (n : ℕ) : IsSmoothPeriodicTest_STR02933 (fun t => Real.sin (n * t)) := by
  refine ⟨Real.contDiff_sin.comp (contDiff_const.mul contDiff_id), fun t => ?_⟩
  show Real.sin (n * (t + 2 * π)) = Real.sin (n * t)
  rw [mul_add, Real.sin_add_nat_mul_two_pi]

theorem const_test_STR02933 : IsSmoothPeriodicTest_STR02933 (fun _ : ℝ => (1 : ℝ)) :=
  ⟨contDiff_const, fun _ => rfl⟩

theorem deriv_cos_STR02933 (n : ℕ) (t : ℝ) :
    deriv (fun s => Real.cos (n * s)) t = -((n : ℝ) * Real.sin (n * t)) := by
  have h : HasDerivAt (fun s : ℝ => Real.cos ((n : ℝ) * s))
      (-Real.sin ((n : ℝ) * t) * ((n : ℝ) * 1)) t :=
    ((hasDerivAt_id' t).const_mul (n : ℝ)).cos
  rw [h.deriv]
  ring

theorem deriv_sin_STR02933 (n : ℕ) (t : ℝ) :
    deriv (fun s => Real.sin (n * s)) t = (n : ℝ) * Real.cos (n * t) := by
  have h : HasDerivAt (fun s : ℝ => Real.sin ((n : ℝ) * s))
      (Real.cos ((n : ℝ) * t) * ((n : ℝ) * 1)) t :=
    ((hasDerivAt_id' t).const_mul (n : ℝ)).sin
  rw [h.deriv]
  ring

theorem normInt_weight_cos_STR02933 (w : ℝ → ℝ) (n : ℕ) :
    normInt_STR02933 (fun t => w t * deriv (fun s => Real.cos (n * s)) t)
      = -((n : ℝ) * normInt_STR02933 (fun t => w t * Real.sin (n * t))) := by
  have e : (fun t => w t * deriv (fun s => Real.cos (n * s)) t)
      = fun t => (-(n : ℝ)) * (w t * Real.sin (n * t)) := by
    funext t
    rw [deriv_cos_STR02933]
    ring
  rw [e, normInt_mul_const_STR02933]
  ring

theorem normInt_weight_sin_STR02933 (w : ℝ → ℝ) (n : ℕ) :
    normInt_STR02933 (fun t => w t * deriv (fun s => Real.sin (n * s)) t)
      = (n : ℝ) * normInt_STR02933 (fun t => w t * Real.cos (n * t)) := by
  have e : (fun t => w t * deriv (fun s => Real.sin (n * s)) t)
      = fun t => (n : ℝ) * (w t * Real.cos (n * t)) := by
    funext t
    rw [deriv_sin_STR02933]
    ring
  rw [e, normInt_mul_const_STR02933]

/-- The constant test gives `∫ g dm = 0`. -/
theorem str029_33_fourier_coefficients_weak_derivative_mean
    (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g) :
    normInt_STR02933 g = 0 := by
  have h := hwg.2.2 (fun _ : ℝ => (1 : ℝ)) const_test_STR02933
  have hz : normInt_STR02933 (fun t => w t * deriv (fun _ : ℝ => (1 : ℝ)) t) = 0 := by
    simp [normInt_STR02933]
  have h1 : normInt_STR02933 (fun t => g t * (1 : ℝ)) = normInt_STR02933 g := by
    simp
  rw [h1, hz, neg_zero] at h
  exact h

/-- Main statement: for `n ≥ 1`, the cosine coefficient of `g` is `n s_n(w)`, the sine coefficient
of `g` is `-n c_n(w)`, and `∫ g dm = 0`. -/
theorem str029_33_fourier_coefficients_weak_derivative
    (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g) (n : ℕ) (_hn : 1 ≤ n) :
    cosCoeff_STR02933 g n = (n : ℝ) * sinCoeff_STR02933 w n ∧
      sinCoeff_STR02933 g n = -((n : ℝ) * cosCoeff_STR02933 w n) ∧
      normInt_STR02933 g = 0 := by
  have hcos : normInt_STR02933 (fun t => g t * Real.cos (n * t))
      = -normInt_STR02933 (fun t => w t * deriv (fun s => Real.cos (n * s)) t) :=
    hwg.2.2 _ (cos_test_STR02933 n)
  have hsin : normInt_STR02933 (fun t => g t * Real.sin (n * t))
      = -normInt_STR02933 (fun t => w t * deriv (fun s => Real.sin (n * s)) t) :=
    hwg.2.2 _ (sin_test_STR02933 n)
  refine ⟨?_, ?_, str029_33_fourier_coefficients_weak_derivative_mean w g hwg⟩
  · unfold cosCoeff_STR02933 sinCoeff_STR02933
    rw [hcos, normInt_weight_cos_STR02933]
    ring
  · unfold cosCoeff_STR02933 sinCoeff_STR02933
    rw [hsin, normInt_weight_sin_STR02933]
    ring

end DGPS.Frontier.STR029
