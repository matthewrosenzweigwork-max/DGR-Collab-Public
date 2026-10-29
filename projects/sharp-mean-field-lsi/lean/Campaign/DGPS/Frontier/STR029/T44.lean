import DGPS.Frontier.STR029.T33
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# STR029.44: Uniform exponential and normalizer expansions

Task id: STR029.44. Title: Uniform exponential and normalizer expansions (node STR029, size L).

Provides:
* `DGPS.Frontier.STR029.str029_44_uniform_exponential_normalizer_expansions`: for every `M` there are `h0 > 0`
  and `C ≥ 0` such that for all periodic mean-zero `C²` functions `v`, `q` with `C²` norm at most `M` and all
  `|h| ≤ h0`: `exp(h v + h² q)` equals its degree-four polynomial in `h` up to `C |h|⁵` (uniformly in `t`);
  `Z(h) = ∫ exp(x_h) dm`, `1/Z(h)` and `log Z(h)` equal their degree-four polynomials in `h` up to `C |h|⁵`;
  `|Z(h) - 1| ≤ C h²` and `|Z(h) - 1| ≤ 1/2`; and the coefficients satisfy `|z₂|, |z₃|, |z₄| ≤ C`.
* `DGPS.Frontier.STR029.C2NormLE_STR02944`: `‖f‖∞ + ‖f'‖∞ + ‖f''‖∞ ≤ M`, as bounds `A + B + C ≤ M`.
* `DGPS.Frontier.STR029.IsAdmissible_STR02944`: `f` is `2π`-periodic, mean zero, `C²`, with `C²` norm at most `M`.
* `DGPS.Frontier.STR029.expArg_STR02944`: the exponent `x_h(t) = h v(t) + h² q(t)`.
* `DGPS.Frontier.STR029.expPoly_STR02944`: the degree-four polynomial in `h` approximating `exp(x_h(t))`.
* `DGPS.Frontier.STR029.normalizer_STR02944`: the normalizer `Z(h) = ∫ exp(x_h) dm`.
* `DGPS.Frontier.STR029.z2_STR02944`, `z3_STR02944`, `z4_STR02944`: the coefficients of `h²`, `h³`, `h⁴` in `Z(h)`.
* `DGPS.Frontier.STR029.normInt_const_STR02944`, `normInt_add_STR02944`, `normInt_sub_STR02944`,
  `abs_normInt_le_STR02944`: the normalized integral of a constant, of sums and differences of continuous
  functions, and its bound by a uniform pointwise bound.
* `DGPS.Frontier.STR029.mono_bound_STR02944`, `exp_scalar_STR02944`: a monomial bound and the scalar degree-four
  expansion of `exp(h a + h² b)` with remainder `(N³ + N⁴ + N⁵) |h|⁵`.
* `DGPS.Frontier.STR029.sigma_bound_STR02944`, `Zm1_bound_STR02944`: `|Z - 1 - z₂ h²| = O(|h|³)` and
  `|Z - 1| = O(h²)` from the degree-four expansion of `Z`.
* `DGPS.Frontier.STR029.inv_expansion_STR02944`, `log_expansion_STR02944`: the scalar degree-four expansions of
  `Z⁻¹` and `log Z` from that of `Z` when `|Z - 1| ≤ 1/2`.
* `DGPS.Frontier.STR029.pt_bounds_STR02944`, `coeff_bounds_STR02944`: pointwise and integrated bounds for the
  coefficients `z₂, z₃, z₄`.
* `DGPS.Frontier.STR029.normInt_expPoly_STR02944`, `normalizer_expansion_STR02944`: the normalized integral of
  `expPoly` and the degree-four expansion of `Z(h)` with remainder `(N³ + N⁴ + N⁵) |h|⁵`.
* `DGPS.Frontier.STR029.admissible_bounds_STR02944`: an admissible function is continuous, has mean zero and
  is bounded by `max M 0`.

R5 notes:
* Carriers: concrete functions `ℝ → ℝ` that are `2π`-periodic (`Function.Periodic`), not functions on a torus,
  and `dm` is the normalized integral `normInt_STR02933` of T33, i.e. `(2π)⁻¹` times Lebesgue integration over
  `Ioc 0 (2π)`. Derivatives are derivatives in the angle `t`. All integrands used are continuous, hence
  integrable over the bounded interval, so the Bochner convention for non-integrable functions never enters.
* "`C²` norm at most `M`" is read as `‖f‖∞ + ‖f'‖∞ + ‖f''‖∞ ≤ M` (a sum of three sup norms over `ℝ`) and is
  stated as the existence of bounds `A, B, C` for `|f|`, `|f'|`, `|f''|` with `A + B + C ≤ M`; this is
  equivalent to the sum of suprema being at most `M`. The `C²` property is the hypothesis `ContDiff ℝ 2 f`,
  `deriv` is the real derivative, and `M` is an arbitrary real number (no admissible function exists for
  `M < 0`; the proof uses `N = max M 0`). Another standard `C²` norm changes only the value of `M`.
* "Periodic mean-zero" is read as `Function.Periodic f (2π)` and `normInt_STR02933 f = 0`.
* Quantifier order: `∃ h0 > 0, ∃ C ≥ 0, ∀ v q admissible, ∀ |h| ≤ h0, ...`, so the interval `[-h0, h0]` and the
  constant `C` depend only on `M`, and every smaller interval works as well. The statement does not name the
  explicit `h0`; the proof takes `h0 = 1 / (4 (N + 1) + 2 D1)` with `N = max M 0`, `B = N² + N³ + N⁴`,
  `C5 = N³ + N⁴ + N⁵` and `D1 = 3 B + C5`.
* The degree-four polynomials are written out. For the exponential it is
  `1 + h v + h² (q + v²/2) + h³ (v q + v³/6) + h⁴ (q²/2 + v² q/2 + v⁴/24)` pointwise in `t`. Integrating, the
  `h` term vanishes because `v` has mean zero, which gives `Z = 1 + z₂ h² + z₃ h³ + z₄ h⁴ + O(|h|⁵)` (the
  quadratic start). The specification does not name coefficients; `z₂, z₃, z₄` are the normalized integrals of the
  `h², h³, h⁴` coefficients. The expansions of `1/Z` and `log Z` are the fourth Taylor polynomials, written in
  `z₂, z₃, z₄` as `1 - z₂ h² - z₃ h³ + (z₂² - z₄) h⁴` and `z₂ h² + z₃ h³ + (z₄ - z₂²/2) h⁴`.
* Remainders are stated as `≤ C |h|⁵` (not as `O(|h|⁵)` in the filter sense), uniformly in `t` for the pointwise
  one. `Z(h) = 1 + O(h²)` is `|Z - 1| ≤ C h²`. The conclusion `|Z - 1| ≤ 1/2` records the smallness used in the
  specification's proof; it makes `Z ≥ 1/2` so that `1/Z` and `log Z` are the genuine reciprocal and logarithm.
  The bounds `|z₂|, |z₃|, |z₄| ≤ C` are extra by-products (they make the constants uniform in the coefficients).
* Deviation from the specification's proof: the specification bounds the derivatives `B_k`, `b_k` and applies a
  Taylor formula with differentiation under the integral. Here the argument is derivative-free: the scalar bound
  `Real.exp_bound` (degree four, remainder `|x|⁵/100` for `|x| ≤ 1`) plus a polynomial identity gives the
  pointwise expansion, which is integrated (`normInt` is linear on continuous functions and bounded by uniform
  pointwise bounds); `1/Z` and `log Z` come from `1/Z = 1 - w + w² - w³/Z` and
  `Real.abs_log_sub_add_sum_range_le`, with `w = Z - 1` and `|w| ≤ 1/2`. The constants therefore are explicit
  polynomials in `N = max M 0` rather than the `e^{2M}`-type constants of the sketch; only dependence on `M` is
  claimed. The conclusion is the one specified. The periodicity hypothesis and the derivative bounds in the `C²`
  norm are not needed by this route (they enter only through the hypothesis `IsAdmissible_STR02944`, from which
  continuity, mean zero and the sup bound `|f| ≤ max M 0` are read off).
* The mean-zero hypothesis on `q` is used only to bound `|z₂|` (via `∫ q dm = 0`); that on `v` kills the linear
  term of `Z`.
-/

open MeasureTheory Set Real

namespace DGPS.Frontier.STR029

/-- The `C²` norm bound: there are sup-norm bounds `A`, `B`, `C` for `f`, `f'`, `f''` on all of `ℝ`
with `A + B + C ≤ M`; that is, `‖f‖∞ + ‖f'‖∞ + ‖f''‖∞ ≤ M`. -/
def C2NormLE_STR02944 (M : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ A B C : ℝ, A + B + C ≤ M ∧ (∀ t, |f t| ≤ A) ∧ (∀ t, |deriv f t| ≤ B) ∧
    ∀ t, |deriv (deriv f) t| ≤ C

/-- `f` is a periodic mean-zero real `C²` function with `C²` norm at most `M`: `2π`-periodic,
`∫ f dm = 0`, `C²` on `ℝ`, and `‖f‖_{C²} ≤ M`. -/
def IsAdmissible_STR02944 (M : ℝ) (f : ℝ → ℝ) : Prop :=
  Function.Periodic f (2 * π) ∧ normInt_STR02933 f = 0 ∧ ContDiff ℝ 2 f ∧ C2NormLE_STR02944 M f

/-- The exponent `x_h(t) = h v(t) + h² q(t)`. -/
def expArg_STR02944 (v q : ℝ → ℝ) (h t : ℝ) : ℝ :=
  h * v t + h ^ 2 * q t

/-- The degree-four Taylor polynomial in `h` of `exp(x_h(t))`, with coefficients written in `v(t)` and
`q(t)`. -/
noncomputable def expPoly_STR02944 (v q : ℝ → ℝ) (h t : ℝ) : ℝ :=
  1 + h * v t + h ^ 2 * (q t + v t ^ 2 / 2) + h ^ 3 * (v t * q t + v t ^ 3 / 6) +
    h ^ 4 * (q t ^ 2 / 2 + v t ^ 2 * q t / 2 + v t ^ 4 / 24)

/-- The normalizer `Z(h) = ∫ exp(x_h) dm`. -/
noncomputable def normalizer_STR02944 (v q : ℝ → ℝ) (h : ℝ) : ℝ :=
  normInt_STR02933 (fun t => Real.exp (expArg_STR02944 v q h t))

/-- The `h²` coefficient `z₂ = ∫ (q + v²/2) dm` of `Z(h)`. -/
noncomputable def z2_STR02944 (v q : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => q t + v t ^ 2 / 2)

/-- The `h³` coefficient `z₃ = ∫ (v q + v³/6) dm` of `Z(h)`. -/
noncomputable def z3_STR02944 (v q : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => v t * q t + v t ^ 3 / 6)

/-- The `h⁴` coefficient `z₄ = ∫ (q²/2 + v² q/2 + v⁴/24) dm` of `Z(h)`. -/
noncomputable def z4_STR02944 (v q : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => q t ^ 2 / 2 + v t ^ 2 * q t / 2 + v t ^ 4 / 24)

theorem normInt_const_STR02944 (c : ℝ) : normInt_STR02933 (fun _ => c) = c := by
  unfold normInt_STR02933
  have hpi : (0:ℝ) < π := Real.pi_pos
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by positivity)]
  field_simp
  ring

theorem normInt_add_STR02944 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    normInt_STR02933 (fun t => f t + g t) = normInt_STR02933 f + normInt_STR02933 g := by
  unfold normInt_STR02933
  rw [integral_add hf.integrableOn_Ioc hg.integrableOn_Ioc]
  ring

theorem normInt_sub_STR02944 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    normInt_STR02933 (fun t => f t - g t) = normInt_STR02933 f - normInt_STR02933 g := by
  unfold normInt_STR02933
  rw [integral_sub hf.integrableOn_Ioc hg.integrableOn_Ioc]
  ring

theorem abs_normInt_le_STR02944 {f : ℝ → ℝ} {c : ℝ} (hf : ∀ t, |f t| ≤ c) :
    |normInt_STR02933 f| ≤ c := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  unfold normInt_STR02933
  have h1 : ‖∫ t in Ioc 0 (2 * π), f t‖ ≤ c * volume.real (Ioc 0 (2 * π)) :=
    norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top (fun t _ => by simpa using hf t)
  rw [Real.volume_real_Ioc_of_le (by positivity)] at h1
  rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity))]
  rw [Real.norm_eq_abs] at h1
  calc (2 * π)⁻¹ * |∫ t in Ioc 0 (2 * π), f t| ≤ (2 * π)⁻¹ * (c * (2 * π - 0)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c := by field_simp; ring


theorem mono_bound_STR02944 {N h a b : ℝ} (hh : |h| ≤ 1) (ha : |a| ≤ N) (hb : |b| ≤ N)
    (k i j : ℕ) : |h ^ k * (a ^ i * b ^ j)| ≤ N ^ (i + j) := by
  have hN : 0 ≤ N := (abs_nonneg a).trans ha
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
  calc |h| ^ k * (|a| ^ i * |b| ^ j) ≤ 1 * (N ^ i * N ^ j) :=
        mul_le_mul (pow_le_one₀ (abs_nonneg h) hh)
          (mul_le_mul (pow_le_pow_left₀ (abs_nonneg a) ha i) (pow_le_pow_left₀ (abs_nonneg b) hb j)
            (by positivity) (by positivity)) (by positivity) (by norm_num)
    _ = N ^ (i + j) := by rw [pow_add]; ring

theorem exp_scalar_STR02944 {N h a b : ℝ} (hh : |h| ≤ 1) (hNh : N * |h| ≤ 1 / 4)
    (ha : |a| ≤ N) (hb : |b| ≤ N) :
    |Real.exp (h * a + h ^ 2 * b) -
        (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) +
          h ^ 4 * (b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24))| ≤ (N ^ 3 + N ^ 4 + N ^ 5) * |h| ^ 5 := by
  have hN : 0 ≤ N := (abs_nonneg a).trans ha
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hh2 : |h| ^ 2 ≤ |h| := by nlinarith
  have hx : |h * a + h ^ 2 * b| ≤ 2 * N * |h| := by
    calc |h * a + h ^ 2 * b| ≤ |h * a| + |h ^ 2 * b| := abs_add_le _ _
      _ = |h| * |a| + |h| ^ 2 * |b| := by rw [abs_mul, abs_mul, abs_pow]
      _ ≤ |h| * N + |h| * N := add_le_add (mul_le_mul_of_nonneg_left ha hh0)
          (mul_le_mul hh2 hb (abs_nonneg b) hh0)
      _ = 2 * N * |h| := by ring
  have hx1 : |h * a + h ^ 2 * b| ≤ 1 := by nlinarith
  have hb5 := Real.exp_bound hx1 (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb5
  have hx5 : |h * a + h ^ 2 * b| ^ 5 ≤ (2 * N * |h|) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hx 5
  have m1 : |a * b ^ 2| ≤ N ^ 3 := by simpa using mono_bound_STR02944 hh ha hb 0 1 2
  have m2 : |a ^ 3 * b| ≤ N ^ 4 := by simpa using mono_bound_STR02944 hh ha hb 0 3 1
  have m3 : |h * b ^ 3| ≤ N ^ 3 := by simpa using mono_bound_STR02944 hh ha hb 1 0 3
  have m4 : |h * (a ^ 2 * b ^ 2)| ≤ N ^ 4 := by simpa using mono_bound_STR02944 hh ha hb 1 2 2
  have m5 : |h ^ 2 * (a * b ^ 3)| ≤ N ^ 4 := by simpa using mono_bound_STR02944 hh ha hb 2 1 3
  have m6 : |h ^ 3 * b ^ 4| ≤ N ^ 4 := by simpa using mono_bound_STR02944 hh ha hb 3 0 4
  have hS : |a * b ^ 2 / 2 + a ^ 3 * b / 6 + h * b ^ 3 / 6 + h * (a ^ 2 * b ^ 2) / 4 +
      h ^ 2 * (a * b ^ 3) / 6 + h ^ 3 * b ^ 4 / 24| ≤ N ^ 3 + N ^ 4 := by
    rw [abs_le] at m1 m2 m3 m4 m5 m6 ⊢
    have : 0 ≤ N ^ 3 := by positivity
    have : 0 ≤ N ^ 4 := by positivity
    constructor <;> linarith
  have hid : (1 + (h * a + h ^ 2 * b) + (h * a + h ^ 2 * b) ^ 2 / 2 + (h * a + h ^ 2 * b) ^ 3 / 6 +
      (h * a + h ^ 2 * b) ^ 4 / 24) -
        (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) +
          h ^ 4 * (b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24)) =
      h ^ 5 * (a * b ^ 2 / 2 + a ^ 3 * b / 6 + h * b ^ 3 / 6 + h * (a ^ 2 * b ^ 2) / 4 +
      h ^ 2 * (a * b ^ 3) / 6 + h ^ 3 * b ^ 4 / 24) := by ring
  have h1 : |Real.exp (h * a + h ^ 2 * b) - (1 + (h * a + h ^ 2 * b) + (h * a + h ^ 2 * b) ^ 2 / 2 +
      (h * a + h ^ 2 * b) ^ 3 / 6 + (h * a + h ^ 2 * b) ^ 4 / 24)| ≤ N ^ 5 * |h| ^ 5 := by
    have h5 : 0 ≤ N ^ 5 * |h| ^ 5 := by positivity
    calc _ ≤ |h * a + h ^ 2 * b| ^ 5 * (1 / 100) := hb5
      _ ≤ (2 * N * |h|) ^ 5 * (1 / 100) := mul_le_mul_of_nonneg_right hx5 (by norm_num)
      _ = (32 / 100) * (N ^ 5 * |h| ^ 5) := by ring
      _ ≤ N ^ 5 * |h| ^ 5 := by nlinarith
  have h2 : |(1 + (h * a + h ^ 2 * b) + (h * a + h ^ 2 * b) ^ 2 / 2 + (h * a + h ^ 2 * b) ^ 3 / 6 +
      (h * a + h ^ 2 * b) ^ 4 / 24) -
        (1 + h * a + h ^ 2 * (b + a ^ 2 / 2) + h ^ 3 * (a * b + a ^ 3 / 6) +
          h ^ 4 * (b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24))| ≤ (N ^ 3 + N ^ 4) * |h| ^ 5 := by
    rw [hid, abs_mul, abs_pow]
    calc |h| ^ 5 * _ ≤ |h| ^ 5 * (N ^ 3 + N ^ 4) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ = (N ^ 3 + N ^ 4) * |h| ^ 5 := by ring
  calc _ ≤ _ := abs_sub_le _ _ _
    _ ≤ N ^ 5 * |h| ^ 5 + (N ^ 3 + N ^ 4) * |h| ^ 5 := add_le_add h1 h2
    _ = _ := by ring

theorem sigma_bound_STR02944 {B C5 h Z z2 z3 z4 : ℝ} (hC5 : 0 ≤ C5) (hh : |h| ≤ 1)
    (h3 : |z3| ≤ B) (h4 : |z4| ≤ B)
    (hZ5 : |Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)| ≤ C5 * |h| ^ 5) :
    |Z - 1 - z2 * h ^ 2| ≤ (2 * B + C5) * |h| ^ 3 := by
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hB : 0 ≤ B := (abs_nonneg _).trans h3
  have p4 : |h| ^ 4 ≤ |h| ^ 3 := pow_le_pow_of_le_one hh0 hh (by norm_num)
  have p5 : |h| ^ 5 ≤ |h| ^ 3 := pow_le_pow_of_le_one hh0 hh (by norm_num)
  have e3 : |z3 * h ^ 3| ≤ B * |h| ^ 3 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_right h3 (by positivity)
  have e4 : |z4 * h ^ 4| ≤ B * |h| ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |z4| * |h| ^ 4 ≤ B * |h| ^ 4 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ ≤ B * |h| ^ 3 := mul_le_mul_of_nonneg_left p4 hB
  have e5 : |Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)| ≤ C5 * |h| ^ 3 :=
    hZ5.trans (mul_le_mul_of_nonneg_left p5 hC5)
  have hid : Z - 1 - z2 * h ^ 2 =
      z3 * h ^ 3 + z4 * h ^ 4 + (Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)) := by ring
  rw [hid]
  rw [abs_le] at e3 e4 e5 ⊢
  constructor <;> nlinarith [e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem inv_expansion_STR02944 {B C5 D1 h Z z2 z3 z4 : ℝ} (hC5 : 0 ≤ C5) (hD1 : 0 ≤ D1)
    (hh : |h| ≤ 1) (h2 : |z2| ≤ B) (h3 : |z3| ≤ B) (h4 : |z4| ≤ B)
    (hZ5 : |Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)| ≤ C5 * |h| ^ 5)
    (hZ2 : |Z - 1| ≤ D1 * h ^ 2) (hZ : |Z - 1| ≤ 1 / 2) :
    |Z⁻¹ - (1 - z2 * h ^ 2 - z3 * h ^ 3 + (z2 ^ 2 - z4) * h ^ 4)| ≤
      (C5 + 2 * B * (2 * B + C5) + (2 * B + C5) ^ 2 + 2 * D1 ^ 3) * |h| ^ 5 := by
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hB : 0 ≤ B := (abs_nonneg _).trans h3
  have hσ := sigma_bound_STR02944 hC5 hh h3 h4 hZ5
  have hZhalf : 1 / 2 ≤ Z := by
    have := (abs_le.mp hZ).1; linarith
  have hZne : Z ≠ 0 := by positivity
  have hinv : |Z⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr (by linarith))]
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; linarith
  have p6 : |h| ^ 6 ≤ |h| ^ 5 := pow_le_pow_of_le_one hh0 hh (by norm_num)
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have hρ := hZ5
  have hσ2 : |(Z - 1 - z2 * h ^ 2) ^ 2| ≤ (2 * B + C5) ^ 2 * |h| ^ 5 := by
    rw [abs_pow]
    calc |Z - 1 - z2 * h ^ 2| ^ 2 ≤ ((2 * B + C5) * |h| ^ 3) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hσ 2
      _ = (2 * B + C5) ^ 2 * |h| ^ 6 := by ring
      _ ≤ (2 * B + C5) ^ 2 * |h| ^ 5 := mul_le_mul_of_nonneg_left p6 (by positivity)
  have hcross : |2 * z2 * h ^ 2 * (Z - 1 - z2 * h ^ 2)| ≤ 2 * B * (2 * B + C5) * |h| ^ 5 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow]
    have h2' : |(2 : ℝ)| * |z2| ≤ 2 * B := by
      rw [abs_two]; exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    calc |(2 : ℝ)| * |z2| * |h| ^ 2 * |Z - 1 - z2 * h ^ 2|
        ≤ (2 * B) * |h| ^ 2 * ((2 * B + C5) * |h| ^ 3) := by gcongr
      _ = 2 * B * (2 * B + C5) * |h| ^ 5 := by ring
  have hcube : |(Z - 1) ^ 3 * Z⁻¹| ≤ 2 * D1 ^ 3 * |h| ^ 5 := by
    rw [abs_mul, abs_pow]
    have h1 : |Z - 1| ^ 3 ≤ (D1 * h ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hZ2 3
    calc |Z - 1| ^ 3 * |Z⁻¹| ≤ (D1 * h ^ 2) ^ 3 * 2 :=
          mul_le_mul h1 hinv (abs_nonneg _) (by positivity)
      _ = 2 * D1 ^ 3 * |h| ^ 6 := by rw [hsq]; ring
      _ ≤ 2 * D1 ^ 3 * |h| ^ 5 := mul_le_mul_of_nonneg_left p6 (by positivity)
  have hid : Z⁻¹ - (1 - z2 * h ^ 2 - z3 * h ^ 3 + (z2 ^ 2 - z4) * h ^ 4) =
      -(Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)) +
        2 * z2 * h ^ 2 * (Z - 1 - z2 * h ^ 2) + (Z - 1 - z2 * h ^ 2) ^ 2 -
        (Z - 1) ^ 3 * Z⁻¹ := by
    field_simp
    ring
  rw [hid]
  rw [abs_le] at hρ hσ2 hcross hcube ⊢
  constructor <;> nlinarith [hρ.1, hρ.2, hσ2.1, hσ2.2, hcross.1, hcross.2, hcube.1, hcube.2]

theorem log_expansion_STR02944 {B C5 D1 h Z z2 z3 z4 : ℝ} (hC5 : 0 ≤ C5) (hD1 : 0 ≤ D1)
    (hh : |h| ≤ 1) (h2 : |z2| ≤ B) (h3 : |z3| ≤ B) (h4 : |z4| ≤ B)
    (hZ5 : |Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)| ≤ C5 * |h| ^ 5)
    (hZ2 : |Z - 1| ≤ D1 * h ^ 2) (hZ : |Z - 1| ≤ 1 / 2) :
    |Real.log Z - (z2 * h ^ 2 + z3 * h ^ 3 + (z4 - z2 ^ 2 / 2) * h ^ 4)| ≤
      (C5 + B * (2 * B + C5) + (2 * B + C5) ^ 2 / 2 + 2 * D1 ^ 3) * |h| ^ 5 := by
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hB : 0 ≤ B := (abs_nonneg _).trans h3
  have hσ := sigma_bound_STR02944 hC5 hh h3 h4 hZ5
  have p6 : |h| ^ 6 ≤ |h| ^ 5 := pow_le_pow_of_le_one hh0 hh (by norm_num)
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have hρ := hZ5
  have hx : |1 - Z| < 1 := by
    rw [abs_sub_comm]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le hx 2
  have hx' : |1 - Z| = |Z - 1| := abs_sub_comm _ _
  have hlog1 : |Real.log Z - ((Z - 1) - (Z - 1) ^ 2 / 2)| ≤ 2 * D1 ^ 3 * |h| ^ 5 := by
    have e : (∑ i ∈ Finset.range 2, (1 - Z) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - (1 - Z)) =
        Real.log Z - ((Z - 1) - (Z - 1) ^ 2 / 2) := by
      simp [Finset.sum_range_succ]
      ring
    rw [e, hx'] at hlog
    have hden : 1 / 2 ≤ 1 - |Z - 1| := by linarith
    have hpos : 0 < 1 - |Z - 1| := by linarith
    have h1 : |Z - 1| ^ (2 + 1) / (1 - |Z - 1|) ≤ 2 * |Z - 1| ^ 3 := by
      rw [div_le_iff₀ hpos]
      have h3' : 0 ≤ |Z - 1| ^ 3 := by positivity
      have h4' := mul_nonneg h3' (by linarith : (0 : ℝ) ≤ 2 * (1 - |Z - 1|) - 1)
      have h5' : |Z - 1| ^ (2 + 1) = |Z - 1| ^ 3 := rfl
      rw [h5']
      nlinarith
    have h2' : |Z - 1| ^ 3 ≤ (D1 * h ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hZ2 3
    calc _ ≤ |Z - 1| ^ (2 + 1) / (1 - |Z - 1|) := hlog
      _ ≤ 2 * |Z - 1| ^ 3 := h1
      _ ≤ 2 * (D1 * h ^ 2) ^ 3 := by gcongr
      _ = 2 * D1 ^ 3 * |h| ^ 6 := by rw [hsq]; ring
      _ ≤ 2 * D1 ^ 3 * |h| ^ 5 := mul_le_mul_of_nonneg_left p6 (by positivity)
  have hσ2 : |(Z - 1 - z2 * h ^ 2) ^ 2 / 2| ≤ (2 * B + C5) ^ 2 / 2 * |h| ^ 5 := by
    rw [abs_div, abs_pow, abs_two]
    calc |Z - 1 - z2 * h ^ 2| ^ 2 / 2 ≤ ((2 * B + C5) * |h| ^ 3) ^ 2 / 2 := by
          gcongr
      _ = (2 * B + C5) ^ 2 / 2 * |h| ^ 6 := by ring
      _ ≤ (2 * B + C5) ^ 2 / 2 * |h| ^ 5 := mul_le_mul_of_nonneg_left p6 (by positivity)
  have hcross : |z2 * h ^ 2 * (Z - 1 - z2 * h ^ 2)| ≤ B * (2 * B + C5) * |h| ^ 5 := by
    rw [abs_mul, abs_mul, abs_pow]
    calc |z2| * |h| ^ 2 * |Z - 1 - z2 * h ^ 2|
        ≤ B * |h| ^ 2 * ((2 * B + C5) * |h| ^ 3) := by gcongr
      _ = B * (2 * B + C5) * |h| ^ 5 := by ring
  have hid : Real.log Z - (z2 * h ^ 2 + z3 * h ^ 3 + (z4 - z2 ^ 2 / 2) * h ^ 4) =
      (Real.log Z - ((Z - 1) - (Z - 1) ^ 2 / 2)) +
        (Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)) -
        z2 * h ^ 2 * (Z - 1 - z2 * h ^ 2) - (Z - 1 - z2 * h ^ 2) ^ 2 / 2 := by
    ring
  rw [hid]
  rw [abs_le] at hlog1 hρ hσ2 hcross ⊢
  constructor <;> nlinarith [hlog1.1, hlog1.2, hρ.1, hρ.2, hσ2.1, hσ2.2, hcross.1, hcross.2]

theorem Zm1_bound_STR02944 {B C5 h Z z2 z3 z4 : ℝ} (hC5 : 0 ≤ C5) (hh : |h| ≤ 1)
    (h2 : |z2| ≤ B) (h3 : |z3| ≤ B) (h4 : |z4| ≤ B)
    (hZ5 : |Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)| ≤ C5 * |h| ^ 5) :
    |Z - 1| ≤ (3 * B + C5) * h ^ 2 := by
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hB : 0 ≤ B := (abs_nonneg _).trans h3
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have p3 : |h| ^ 3 ≤ |h| ^ 2 := pow_le_pow_of_le_one hh0 hh (by norm_num)
  have p4 : |h| ^ 4 ≤ |h| ^ 2 := pow_le_pow_of_le_one hh0 hh (by norm_num)
  have p5 : |h| ^ 5 ≤ |h| ^ 2 := pow_le_pow_of_le_one hh0 hh (by norm_num)
  have e2 : |z2 * h ^ 2| ≤ B * |h| ^ 2 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have e3 : |z3 * h ^ 3| ≤ B * |h| ^ 2 := by
    rw [abs_mul, abs_pow]
    calc |z3| * |h| ^ 3 ≤ B * |h| ^ 3 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ ≤ B * |h| ^ 2 := mul_le_mul_of_nonneg_left p3 hB
  have e4 : |z4 * h ^ 4| ≤ B * |h| ^ 2 := by
    rw [abs_mul, abs_pow]
    calc |z4| * |h| ^ 4 ≤ B * |h| ^ 4 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ ≤ B * |h| ^ 2 := mul_le_mul_of_nonneg_left p4 hB
  have e5 : |Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)| ≤ C5 * |h| ^ 2 :=
    hZ5.trans (mul_le_mul_of_nonneg_left p5 hC5)
  have hid : Z - 1 = (Z - (1 + z2 * h ^ 2 + z3 * h ^ 3 + z4 * h ^ 4)) + z2 * h ^ 2 +
      z3 * h ^ 3 + z4 * h ^ 4 := by ring
  rw [hid, hsq]
  rw [abs_le] at e2 e3 e4 e5 ⊢
  constructor <;> nlinarith [e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]

theorem pt_bounds_STR02944 {N a b : ℝ} (ha : |a| ≤ N) (hb : |b| ≤ N) :
    |a ^ 2 / 2| ≤ N ^ 2 ∧ |a * b + a ^ 3 / 6| ≤ N ^ 2 + N ^ 3 ∧
      |b ^ 2 / 2 + a ^ 2 * b / 2 + a ^ 4 / 24| ≤ N ^ 2 + N ^ 3 + N ^ 4 := by
  have hN : 0 ≤ N := (abs_nonneg a).trans ha
  have h0 : |(0 : ℝ)| ≤ 1 := by simp
  have m1 : |a ^ 2| ≤ N ^ 2 := by simpa using mono_bound_STR02944 h0 ha hb 0 2 0
  have m2 : |a * b| ≤ N ^ 2 := by simpa using mono_bound_STR02944 h0 ha hb 0 1 1
  have m3 : |a ^ 3| ≤ N ^ 3 := by simpa using mono_bound_STR02944 h0 ha hb 0 3 0
  have m4 : |b ^ 2| ≤ N ^ 2 := by simpa using mono_bound_STR02944 h0 ha hb 0 0 2
  have m5 : |a ^ 2 * b| ≤ N ^ 3 := by simpa using mono_bound_STR02944 h0 ha hb 0 2 1
  have m6 : |a ^ 4| ≤ N ^ 4 := by simpa using mono_bound_STR02944 h0 ha hb 0 4 0
  have p2 : 0 ≤ N ^ 2 := by positivity
  have p3 : 0 ≤ N ^ 3 := by positivity
  have p4 : 0 ≤ N ^ 4 := by positivity
  rw [abs_le] at m1 m2 m3 m4 m5 m6
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith [m1.1, m1.2, m2.1, m2.2, m3.1,
    m3.2, m4.1, m4.2, m5.1, m5.2, m6.1, m6.2]

theorem coeff_bounds_STR02944 {N : ℝ} {v q : ℝ → ℝ} (hvc : Continuous v) (hqc : Continuous q)
    (hqm : normInt_STR02933 q = 0) (hv : ∀ t, |v t| ≤ N) (hq : ∀ t, |q t| ≤ N) :
    |z2_STR02944 v q| ≤ N ^ 2 + N ^ 3 + N ^ 4 ∧ |z3_STR02944 v q| ≤ N ^ 2 + N ^ 3 + N ^ 4 ∧
      |z4_STR02944 v q| ≤ N ^ 2 + N ^ 3 + N ^ 4 := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hv 0)
  have p2 : 0 ≤ N ^ 2 := by positivity
  have p3 : 0 ≤ N ^ 3 := by positivity
  have p4 : 0 ≤ N ^ 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have key := abs_normInt_le_STR02944 (f := fun t => (q t + v t ^ 2 / 2) - q t) (c := N ^ 2)
      (fun t => by
        have := (pt_bounds_STR02944 (hv t) (hq t)).1
        simpa using this)
    rw [normInt_sub_STR02944 (by fun_prop) hqc, hqm, sub_zero] at key
    unfold z2_STR02944
    linarith
  · unfold z3_STR02944
    have key := abs_normInt_le_STR02944 (f := fun t => v t * q t + v t ^ 3 / 6) (c := N ^ 2 + N ^ 3)
      (fun t => (pt_bounds_STR02944 (hv t) (hq t)).2.1)
    linarith
  · unfold z4_STR02944
    exact abs_normInt_le_STR02944 (fun t => (pt_bounds_STR02944 (hv t) (hq t)).2.2)

theorem normInt_expPoly_STR02944 {v q : ℝ → ℝ} (hvc : Continuous v) (hqc : Continuous q)
    (hvm : normInt_STR02933 v = 0) (h : ℝ) :
    normInt_STR02933 (expPoly_STR02944 v q h) =
      1 + z2_STR02944 v q * h ^ 2 + z3_STR02944 v q * h ^ 3 + z4_STR02944 v q * h ^ 4 := by
  have e : expPoly_STR02944 v q h = fun t => 1 + h * v t + h ^ 2 * (q t + v t ^ 2 / 2) +
      h ^ 3 * (v t * q t + v t ^ 3 / 6) +
        h ^ 4 * (q t ^ 2 / 2 + v t ^ 2 * q t / 2 + v t ^ 4 / 24) := rfl
  rw [e, normInt_add_STR02944 (by fun_prop) (by fun_prop),
    normInt_add_STR02944 (by fun_prop) (by fun_prop),
    normInt_add_STR02944 (by fun_prop) (by fun_prop),
    normInt_add_STR02944 (by fun_prop) (by fun_prop), normInt_const_STR02944,
    normInt_mul_const_STR02933, normInt_mul_const_STR02933, normInt_mul_const_STR02933,
    normInt_mul_const_STR02933, hvm]
  unfold z2_STR02944 z3_STR02944 z4_STR02944
  ring

theorem normalizer_expansion_STR02944 {N : ℝ} {v q : ℝ → ℝ} (hvc : Continuous v)
    (hqc : Continuous q) (hvm : normInt_STR02933 v = 0) (hv : ∀ t, |v t| ≤ N)
    (hq : ∀ t, |q t| ≤ N) {h : ℝ} (hh : |h| ≤ 1) (hNh : N * |h| ≤ 1 / 4) :
    |normalizer_STR02944 v q h -
        (1 + z2_STR02944 v q * h ^ 2 + z3_STR02944 v q * h ^ 3 + z4_STR02944 v q * h ^ 4)| ≤
      (N ^ 3 + N ^ 4 + N ^ 5) * |h| ^ 5 := by
  have hexpc : Continuous (fun t => Real.exp (expArg_STR02944 v q h t)) := by
    unfold expArg_STR02944; fun_prop
  have hPc : Continuous (expPoly_STR02944 v q h) := by
    unfold expPoly_STR02944; fun_prop
  have key := abs_normInt_le_STR02944
    (f := fun t => Real.exp (expArg_STR02944 v q h t) - expPoly_STR02944 v q h t)
    (c := (N ^ 3 + N ^ 4 + N ^ 5) * |h| ^ 5)
    (fun t => exp_scalar_STR02944 hh hNh (hv t) (hq t))
  rw [normInt_sub_STR02944 hexpc hPc, normInt_expPoly_STR02944 hvc hqc hvm h] at key
  exact key

theorem admissible_bounds_STR02944 {M : ℝ} {f : ℝ → ℝ} (hf : IsAdmissible_STR02944 M f) :
    Continuous f ∧ normInt_STR02933 f = 0 ∧ ∀ t, |f t| ≤ max M 0 := by
  obtain ⟨_, hmean, hC2, A, B, C, hsum, hA, hB, hC⟩ := hf
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  exact ⟨hC2.continuous, hmean, fun t => (hA t).trans ((by linarith : A ≤ M).trans (le_max_left _ _))⟩

/-- Uniform degree-four expansions of `exp(x_h)`, `Z(h)`, `1/Z(h)` and `log Z(h)` with `O(|h|⁵)` remainders
on a common interval `|h| ≤ h0`, together with `Z(h) = 1 + O(h²)` and `|Z(h) - 1| ≤ 1/2`.  Both `h0 > 0`
and the constant `C` depend only on `M`; the same `C` also bounds the coefficients `z₂, z₃, z₄`. -/
theorem str029_44_uniform_exponential_normalizer_expansions (M : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ v q : ℝ → ℝ, IsAdmissible_STR02944 M v → IsAdmissible_STR02944 M q →
        ∀ h : ℝ, |h| ≤ h0 →
          (∀ t, |Real.exp (expArg_STR02944 v q h t) - expPoly_STR02944 v q h t| ≤ C * |h| ^ 5) ∧
          |normalizer_STR02944 v q h -
            (1 + z2_STR02944 v q * h ^ 2 + z3_STR02944 v q * h ^ 3 + z4_STR02944 v q * h ^ 4)| ≤
              C * |h| ^ 5 ∧
          |normalizer_STR02944 v q h - 1| ≤ C * h ^ 2 ∧
          |normalizer_STR02944 v q h - 1| ≤ 1 / 2 ∧
          |(normalizer_STR02944 v q h)⁻¹ -
            (1 - z2_STR02944 v q * h ^ 2 - z3_STR02944 v q * h ^ 3 +
              (z2_STR02944 v q ^ 2 - z4_STR02944 v q) * h ^ 4)| ≤ C * |h| ^ 5 ∧
          |Real.log (normalizer_STR02944 v q h) -
            (z2_STR02944 v q * h ^ 2 + z3_STR02944 v q * h ^ 3 +
              (z4_STR02944 v q - z2_STR02944 v q ^ 2 / 2) * h ^ 4)| ≤ C * |h| ^ 5 ∧
          |z2_STR02944 v q| ≤ C ∧ |z3_STR02944 v q| ≤ C ∧ |z4_STR02944 v q| ≤ C := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = max M 0 := ⟨_, rfl⟩
  have hN : 0 ≤ N := hNdef ▸ le_max_right _ _
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = N ^ 2 + N ^ 3 + N ^ 4 := ⟨_, rfl⟩
  obtain ⟨C5, hC5def⟩ : ∃ C5 : ℝ, C5 = N ^ 3 + N ^ 4 + N ^ 5 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hC50 : 0 ≤ C5 := by rw [hC5def]; positivity
  obtain ⟨D1, hD1def⟩ : ∃ D1 : ℝ, D1 = 3 * B + C5 := ⟨_, rfl⟩
  obtain ⟨D3, hD3def⟩ : ∃ D3 : ℝ, D3 = 2 * B + C5 := ⟨_, rfl⟩
  have hD10 : 0 ≤ D1 := by rw [hD1def]; positivity
  have hD30 : 0 ≤ D3 := by rw [hD3def]; positivity
  obtain ⟨Kinv, hKinv⟩ : ∃ K : ℝ, K = C5 + 2 * B * D3 + D3 ^ 2 + 2 * D1 ^ 3 := ⟨_, rfl⟩
  obtain ⟨Klog, hKlog⟩ : ∃ K : ℝ, K = C5 + B * D3 + D3 ^ 2 / 2 + 2 * D1 ^ 3 := ⟨_, rfl⟩
  have hKinv0 : 0 ≤ Kinv := by rw [hKinv]; positivity
  have hKlog0 : 0 ≤ Klog := by rw [hKlog]; positivity
  refine ⟨1 / (4 * (N + 1) + 2 * D1), by positivity, C5 + Kinv + Klog + D1 + B, by positivity, ?_⟩
  intro v q hv hq h hh
  obtain ⟨hvc, hvm, hvb⟩ := admissible_bounds_STR02944 hv
  obtain ⟨hqc, hqm, hqb⟩ := admissible_bounds_STR02944 hq
  rw [← hNdef] at hvb hqb
  have hX : |h| * (4 * (N + 1) + 2 * D1) ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at hh
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hNh : N * |h| ≤ 1 / 4 := by nlinarith [mul_nonneg hN hh0, mul_nonneg hD10 hh0]
  have hh1 : |h| ≤ 1 := by nlinarith [mul_nonneg hN hh0, mul_nonneg hD10 hh0]
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have hD1h : D1 * h ^ 2 ≤ 1 / 2 := by
    have h2 : |h| ^ 2 ≤ |h| := by nlinarith
    rw [hsq]
    nlinarith [mul_nonneg hD10 hh0, mul_le_mul_of_nonneg_left h2 hD10]
  obtain ⟨hz2, hz3, hz4⟩ := coeff_bounds_STR02944 hvc hqc hqm hvb hqb
  rw [← hBdef] at hz2 hz3 hz4
  have hZ5 := normalizer_expansion_STR02944 hvc hqc hvm hvb hqb hh1 hNh
  rw [← hC5def] at hZ5
  have hZ2 := Zm1_bound_STR02944 hC50 hh1 hz2 hz3 hz4 hZ5
  rw [← hD1def] at hZ2
  have hZhalf : |normalizer_STR02944 v q h - 1| ≤ 1 / 2 := hZ2.trans hD1h
  have hinv := inv_expansion_STR02944 hC50 hD10 hh1 hz2 hz3 hz4 hZ5 hZ2 hZhalf
  rw [← hD3def, ← hKinv] at hinv
  have hlog := log_expansion_STR02944 hC50 hD10 hh1 hz2 hz3 hz4 hZ5 hZ2 hZhalf
  rw [← hD3def, ← hKlog] at hlog
  have hh5 : 0 ≤ |h| ^ 5 := by positivity
  have hh2 : 0 ≤ h ^ 2 := by positivity
  refine ⟨fun t => ?_, ?_, ?_, hZhalf, ?_, ?_, ?_, ?_, ?_⟩
  · exact (exp_scalar_STR02944 hh1 hNh (hvb t) (hqb t)).trans
      (mul_le_mul_of_nonneg_right (by rw [hC5def.symm]; linarith) hh5)
  · exact hZ5.trans (mul_le_mul_of_nonneg_right (by linarith) hh5)
  · exact hZ2.trans (mul_le_mul_of_nonneg_right (by linarith) hh2)
  · exact hinv.trans (mul_le_mul_of_nonneg_right (by linarith) hh5)
  · exact hlog.trans (mul_le_mul_of_nonneg_right (by linarith) hh5)
  · linarith
  · linarith
  · linarith

end DGPS.Frontier.STR029
