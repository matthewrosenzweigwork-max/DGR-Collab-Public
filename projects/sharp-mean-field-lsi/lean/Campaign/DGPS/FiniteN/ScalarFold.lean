import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

open MeasureTheory Real
open scoped ContDiff

/-!
# FIN058: positive cubic transformed Dirichlet gap

There is `b₀ > 0` such that for every smooth compactly supported `u : ℝ → ℝ`,
`b₀ ∫ u² ≤ ∫ (u' - y² u / 2)²`, i.e. the operator `-d² + y⁴/4 + y` has strictly positive bottom.
We also record that the formal zero solution `C e^{y³/6}` is not in `L²(ℝ)` unless `C = 0`.

The proof is a multiplier (positive supersolution) argument and needs no compactness: with
`φ(y) = 4 + y/(1+y²)` one has `0 ≤ φ ≤ 9/2` and `φ' + y² φ ≥ 1`; integrating
`(φ u²)' = (φ' + y² φ) u² + 2 φ u (u' - y² u/2)` over `ℝ` gives
`∫ u² ≤ -2 ∫ φ u f ≤ ½ ∫ u² + (81/2) ∫ f²`, so `b₀ = 1/81` works.
-/

namespace DGPS.FiniteN

/-- The bounded multiplier `φ(y) = 4 + y/(1+y²)`. -/
noncomputable def cubicGapMultiplier (y : ℝ) : ℝ := 4 + y / (1 + y ^ 2)

theorem cubicGapMultiplier_hasDerivAt (y : ℝ) :
    HasDerivAt cubicGapMultiplier ((1 - y ^ 2) / (1 + y ^ 2) ^ 2) y := by
  have h1 : (1 + y ^ 2) ≠ 0 := by positivity
  have h := ((hasDerivAt_id y).div (((hasDerivAt_pow 2 y).const_add 1)) h1)
  have : cubicGapMultiplier = fun y => 4 + id y / (1 + y ^ 2) := by
    funext y; simp [cubicGapMultiplier]
  rw [this]
  convert h.const_add 4 using 1
  field_simp
  simp
  ring

theorem cubicGapMultiplier_nonneg (y : ℝ) : 0 ≤ cubicGapMultiplier y := by
  unfold cubicGapMultiplier
  have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have : -(1 / 2 : ℝ) ≤ y / (1 + y ^ 2) := by
    rw [le_div_iff₀ h1]; nlinarith [sq_nonneg (y + 1)]
  linarith

theorem cubicGapMultiplier_le (y : ℝ) : cubicGapMultiplier y ≤ 9 / 2 := by
  unfold cubicGapMultiplier
  have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have : y / (1 + y ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ h1]; nlinarith [sq_nonneg (y - 1)]
  linarith

theorem cubicGapMultiplier_supersolution (y : ℝ) :
    1 ≤ (1 - y ^ 2) / (1 + y ^ 2) ^ 2 + y ^ 2 * cubicGapMultiplier y := by
  unfold cubicGapMultiplier
  have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have h2 : (0 : ℝ) < (1 + y ^ 2) ^ 2 := by positivity
  have key : (1 : ℝ) * (1 + y ^ 2) ^ 2 ≤
      (1 - y ^ 2) + y ^ 2 * (4 * (1 + y ^ 2) ^ 2 + y * (1 + y ^ 2)) := by
    nlinarith [sq_nonneg y, sq_nonneg (y ^ 2), sq_nonneg (y ^ 3), sq_nonneg (y + y ^ 2),
      mul_nonneg (sq_nonneg y) (sq_nonneg (y + 1 / 2)), mul_nonneg (sq_nonneg y) (sq_nonneg (y ^ 2 + y / 2)),
      mul_nonneg (sq_nonneg y) (sq_nonneg (y ^ 2 - 1)), mul_nonneg (sq_nonneg y) (sq_nonneg (y ^ 2))]
  have e : (1 - y ^ 2) / (1 + y ^ 2) ^ 2 + y ^ 2 * (4 + y / (1 + y ^ 2)) =
      ((1 - y ^ 2) + y ^ 2 * (4 * (1 + y ^ 2) ^ 2 + y * (1 + y ^ 2))) / (1 + y ^ 2) ^ 2 := by
    field_simp
  rw [e, le_div_iff₀ h2]
  exact key

/-- **FIN058.** Positive cubic transformed Dirichlet gap: there is `b₀ > 0` with
`b₀ ∫ u² ≤ ∫ (u' - y² u / 2)²` for every smooth compactly supported real `u`. -/
theorem positive_cubic_transformed_dirichlet_gap :
    ∃ b0 : ℝ, 0 < b0 ∧ ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      b0 * ∫ y, u y ^ 2 ≤ ∫ y, (deriv u y - y ^ 2 * u y / 2) ^ 2 := by
  refine ⟨1 / 81, by norm_num, fun u hu hsupp => ?_⟩
  have hdiff : ∀ y, HasDerivAt u (deriv u y) y := fun y =>
    ((hu.differentiable (by simp)) y).hasDerivAt
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hdsupp : HasCompactSupport (deriv u) := hsupp.deriv
  have hφc : Continuous cubicGapMultiplier := by
    unfold cubicGapMultiplier
    refine continuous_const.add (continuous_id.div (by fun_prop) fun y => by positivity)
  have hφ'c : Continuous (fun y : ℝ => (1 - y ^ 2) / (1 + y ^ 2) ^ 2) :=
    (by fun_prop : Continuous fun y : ℝ => 1 - y ^ 2).div (by fun_prop) fun y => by positivity
  have huc : Continuous u := hu.continuous
  let f : ℝ → ℝ := fun y => deriv u y - y ^ 2 * u y / 2
  let G : ℝ → ℝ := fun y => (1 - y ^ 2) / (1 + y ^ 2) ^ 2 * u y ^ 2
      + cubicGapMultiplier y * (2 * u y * deriv u y)
  have hfc : Continuous f := hdc.sub (by fun_prop)
  have hvan : ∀ g : ℝ → ℝ, (∀ y, y ∉ tsupport u → g y = 0) → HasCompactSupport g :=
    fun g hg => hsupp.mono' (fun y hy => by
      by_contra h; exact hy (hg y h))
  have hdz : ∀ y, y ∉ tsupport u → deriv u y = 0 := fun y hy => by
    by_contra h; exact hy (support_deriv_subset (𝕜 := ℝ) h)
  have huz : ∀ y, y ∉ tsupport u → u y = 0 := fun y hy => by
    by_contra h; exact hy (subset_tsupport u h)
  have hu2 : Integrable (fun y => u y ^ 2) :=
    (huc.pow 2).integrable_of_hasCompactSupport (hvan _ fun y hy => by simp [huz y hy])
  have hf2 : Integrable (fun y => f y ^ 2) :=
    (hfc.pow 2).integrable_of_hasCompactSupport
      (hvan _ fun y hy => by simp [f, huz y hy, hdz y hy])
  have hGc : Continuous G := by
    refine (hφ'c.mul (huc.pow 2)).add (hφc.mul ((continuous_const.mul huc).mul hdc))
  have hGs : HasCompactSupport G := hvan _ fun y hy => by simp [G, huz y hy, hdz y hy]
  have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGs
  have hderiv : ∀ y, HasDerivAt (fun y => cubicGapMultiplier y * u y ^ 2) (G y) y := by
    intro y
    have := (cubicGapMultiplier_hasDerivAt y).mul ((hdiff y).pow 2)
    convert this using 1
    simp only [G, Pi.pow_apply]; push_cast; ring
  have hFi : Integrable (fun y => cubicGapMultiplier y * u y ^ 2) :=
    (hφc.mul (huc.pow 2)).integrable_of_hasCompactSupport
      (hvan _ fun y hy => by simp [huz y hy])
  have hG0 : ∫ y, G y = 0 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hGi hFi
  have hpt : ∀ y, u y ^ 2 ≤ G y + (1 / 2 * u y ^ 2 + 81 / 2 * f y ^ 2) := by
    intro y
    have h1 := cubicGapMultiplier_supersolution y
    have h0 := cubicGapMultiplier_nonneg y
    have h9 := cubicGapMultiplier_le y
    have hG : G y = ((1 - y ^ 2) / (1 + y ^ 2) ^ 2 + y ^ 2 * cubicGapMultiplier y) * u y ^ 2
        + 2 * cubicGapMultiplier y * u y * f y := by
      simp only [G, f]; ring
    rw [hG]
    have a1 : u y ^ 2 ≤ ((1 - y ^ 2) / (1 + y ^ 2) ^ 2 + y ^ 2 * cubicGapMultiplier y) * u y ^ 2 := by
      nlinarith [sq_nonneg (u y)]
    have a2 : -(2 * cubicGapMultiplier y * u y * f y) ≤ 1 / 2 * u y ^ 2 + 81 / 2 * f y ^ 2 := by
      nlinarith [sq_nonneg (u y + 2 * cubicGapMultiplier y * f y), mul_nonneg h0 (sub_nonneg.2 h9),
        sq_nonneg (f y), mul_nonneg (sub_nonneg.2 h9) (sq_nonneg (f y)),
        mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h9)) (sq_nonneg (f y)),
        mul_nonneg (sub_nonneg.2 h9) (mul_nonneg (sub_nonneg.2 h9) (sq_nonneg (f y)))]
    linarith
  have hint : ∫ y, u y ^ 2 ≤ ∫ y, (G y + (1 / 2 * u y ^ 2 + 81 / 2 * f y ^ 2)) :=
    integral_mono hu2 (hGi.add ((hu2.const_mul (1 / 2)).add (hf2.const_mul (81 / 2)))) hpt
  have i1 : Integrable (fun y => 1 / 2 * u y ^ 2) := hu2.const_mul (1 / 2)
  have i2 : Integrable (fun y => 81 / 2 * f y ^ 2) := hf2.const_mul (81 / 2)
  have e1 : ∫ y, (G y + (1 / 2 * u y ^ 2 + 81 / 2 * f y ^ 2)) =
      (∫ y, G y) + ∫ y, (1 / 2 * u y ^ 2 + 81 / 2 * f y ^ 2) := integral_add hGi (i1.add i2)
  have e2 : ∫ y, (1 / 2 * u y ^ 2 + 81 / 2 * f y ^ 2) =
      (∫ y, 1 / 2 * u y ^ 2) + ∫ y, 81 / 2 * f y ^ 2 := integral_add i1 i2
  rw [e1, e2, integral_const_mul, integral_const_mul, hG0] at hint
  show 1 / 81 * ∫ y, u y ^ 2 ≤ ∫ y, f y ^ 2
  linarith

/-- The formal zero solution `y ↦ e^{y³/6}` of `u' = y² u / 2` is not in `L²(ℝ)`. -/
theorem cubic_zero_solution_not_square_integrable :
    ¬ Integrable (fun y : ℝ => (exp (y ^ 3 / 6)) ^ 2) := by
  intro h
  have h1 : IntegrableOn (fun y : ℝ => (exp (y ^ 3 / 6)) ^ 2) (Set.Ioi 0) := h.integrableOn
  have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) := by
    refine h1.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have : (1 : ℝ) ≤ exp (y ^ 3 / 6) := one_le_exp (by positivity)
    simp only [norm_one]
    nlinarith
  rw [integrableOn_const_iff] at h2
  simp at h2

end DGPS.FiniteN
