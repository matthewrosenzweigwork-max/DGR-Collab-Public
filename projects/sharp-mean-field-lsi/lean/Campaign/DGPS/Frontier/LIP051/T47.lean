import Mathlib

/-!
# LIP051.47: Characteristic function of the empirical scalar sum

Task id: LIP051.47 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Characteristic function of the empirical scalar sum.

Provides:
* `DGPS.Frontier.LIP051.lip051_47_characteristic_function_empirical_scalar_sum`: for a probability
  measure `μ` on a measurable space `E`, a measurable `Y : E → ℝ`, a real `t` and `N ≥ 1`, the
  expectation under `μ^N = Measure.pi (fun _ : Fin N => μ)` of
  `exp (I * (t / √N) * ∑ l, Y (x l))` equals `(∫ exp (I * (t / √N) * Y) dμ) ^ N`.
* `DGPS.Frontier.LIP051.lip051_47_characteristic_function_empirical_scalar_sum_rpow`: the same
  identity with the normalisation written as the real power `N ^ (-1/2)` (as in `N^{-1/2} ∑ ...`).
* Helpers (all suffixed `_LIP05147`): `integral_exp_sum_LIP05147` (the identity for an arbitrary
  real scalar `c` in place of `t / √N`; this is the induction statement `I_N(c)` of the proof, here
  obtained from the product formula for integrals over `Measure.pi`),
  `rpow_neg_half_LIP05147` (`N ^ (-1/2 : ℝ) = (√N)⁻¹`).

R5 notes:
* Hypotheses are exactly those of the specification: `μ` a probability measure
  (`[IsProbabilityMeasure μ]`), `Y` measurable real-valued, `t : ℝ`, `N ≥ 1` (`hN : 1 ≤ N`).
  No moment condition on `Y` is assumed.
* The ambient space `E` is an arbitrary measurable space, more general than the torus of the node;
  the node's `Torus d` is an instance.
* Scalars are complex: `Y x` is cast to `ℂ`, and the exponential is `Complex.exp`, with `I` the
  imaginary unit. The integrals are Bochner integrals of `ℂ`-valued functions.
* The sample space is `Fin N → E` with `Q_N = Measure.pi (fun _ => μ)` and coordinates `X_l x = x l`.
* The normalisation is written `t / Real.sqrt N`. The specification's `N^{-1/2}` real power agrees
  with it for `N > 0`; this is stated as the second public declaration, which is the same identity
  after rewriting by `rpow_neg_half_LIP05147`.
* Proof route. The specification proves the identity by induction on the number of coordinates,
  using the factorization of LIP051.37. Here the induction is replaced by the corresponding
  Mathlib product formula `MeasureTheory.integral_fintype_prod_eq_prod`, which is the finite
  product statement for `Measure.pi` itself; the factorization of the exponential of a sum into the
  product of the one-coordinate exponentials is `Complex.exp_sum`. This does not alter the statement.
  The prerequisites LIP051.35-37 are not needed by this route and are not used.
* Unused hypotheses. The Lean proof does not use `Measurable Y` or `1 ≤ N` (Mathlib's product
  formula holds without them, with Bochner integrals); they are kept, as binders `_hY`, `_hN`,
  because the specification lists them. The identity is a fortiori true under them.
* Mode indexing (FD-002). No mode index occurs in this unit: `Y` is an abstract measurable
  function (for the node it is later a basis function `e_j` with `j ≥ 1`). No positive-mode or
  mode-zero reading is adopted, and no mode-zero restriction is added or dropped here.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- The identity for an arbitrary real scalar `c` in place of `t / √N`. -/
lemma integral_exp_sum_LIP05147 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (Y : E → ℝ) (N : ℕ) (c : ℝ) :
    ∫ x, Complex.exp (Complex.I * (c : ℂ) * ∑ l : Fin N, (Y (x l) : ℂ))
        ∂(Measure.pi fun _ : Fin N => μ)
      = (∫ y, Complex.exp (Complex.I * (c : ℂ) * (Y y : ℂ)) ∂μ) ^ N := by
  have h : ∀ x : Fin N → E, Complex.exp (Complex.I * (c : ℂ) * ∑ l : Fin N, (Y (x l) : ℂ))
      = ∏ l : Fin N, Complex.exp (Complex.I * (c : ℂ) * (Y (x l) : ℂ)) := by
    intro x
    rw [Finset.mul_sum, Complex.exp_sum]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun _ : Fin N =>
    fun y => Complex.exp (Complex.I * (c : ℂ) * (Y y : ℂ)))]
  simp

/-- `N ^ (-1/2) = (√N)⁻¹` for a natural number `N`. -/
lemma rpow_neg_half_LIP05147 (N : ℕ) :
    (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg N)]

/-- **LIP051.47.** For a probability measure `μ`, measurable real `Y`, real `t` and `N ≥ 1`,
`E_{μ^N} exp (I * (t / √N) * ∑_{l<N} Y (X_l)) = (∫ exp (I * (t / √N) * Y) dμ) ^ N`. No moment
condition on `Y` is required. -/
theorem lip051_47_characteristic_function_empirical_scalar_sum {E : Type*}
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] {Y : E → ℝ}
    (_hY : Measurable Y) (t : ℝ) {N : ℕ} (_hN : 1 ≤ N) :
    ∫ x, Complex.exp (Complex.I * ((t / Real.sqrt N : ℝ) : ℂ) * ∑ l : Fin N, (Y (x l) : ℂ))
        ∂(Measure.pi fun _ : Fin N => μ)
      = (∫ y, Complex.exp (Complex.I * ((t / Real.sqrt N : ℝ) : ℂ) * (Y y : ℂ)) ∂μ) ^ N :=
  integral_exp_sum_LIP05147 μ Y N (t / Real.sqrt N)

/-- **LIP051.47**, with the normalisation written as the real power `N ^ (-1/2)`. -/
theorem lip051_47_characteristic_function_empirical_scalar_sum_rpow {E : Type*}
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] {Y : E → ℝ}
    (hY : Measurable Y) (t : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x, Complex.exp (Complex.I * ((t * (N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ l : Fin N, (Y (x l) : ℂ)) ∂(Measure.pi fun _ : Fin N => μ)
      = (∫ y, Complex.exp (Complex.I * ((t * (N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Y y : ℂ)) ∂μ)
          ^ N := by
  have e : t * (N : ℝ) ^ (-(1 / 2 : ℝ)) = t / Real.sqrt N := by
    rw [rpow_neg_half_LIP05147, div_eq_mul_inv]
  rw [e]
  exact lip051_47_characteristic_function_empirical_scalar_sum μ hY t hN

end DGPS.Frontier.LIP051
