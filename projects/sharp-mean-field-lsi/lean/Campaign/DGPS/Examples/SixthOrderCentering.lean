import DGPS.Examples.PolynomialSpecies
import DGPS.Circle.BesselMoments

/-!
# Sixth-order centering cancellation (EX053)

For the von Mises law `dμ_h = I₀(h)⁻¹ exp(h cos θ) dθ/(2π)` (`besselDensity h` against the
normalized angular Haar measure) and the degree-two feature `P_h = cos 2θ - (h/3) cos θ` of the
canonical elementary polynomial model (EX052), the centering `m_h = μ_h(P_h)` satisfies
`m_h = -h²/24 + h⁶/9216 + O(h⁸)`; in particular there is no `h⁴` term.  The individual expansions
`I₂/I₀ = h²/8 - h⁴/48 + 11h⁶/3072 + O(h⁸)` and `(h/3) I₁/I₀ = h²/6 - h⁴/48 + h⁶/288 + O(h⁸)` are
proved with an explicit bound `C h⁸` on the common interval `|h| ≤ 1`.

Route: the series of EX002 give `I₀ = ∑ a^j/(j!)²` and `I₁/h = ½ ∑ a^j/(j!(j+1)!)` with
`a = h²/4`; the recurrence `I₀ - I₂ = 2 I₁/h` (integration by parts on the circle) gives `I₂`;
the quotient `(I₁/h)/I₀` is expanded after the exact subtraction of the truncated series.

Declarations:

* `vonMisesCentering h`: `μ_h(P_h)` in the angular variable;
* `vonMisesCenteringTorus h`: the same mean on `Torus 1` through `polyFeature` (EX052);
* `sixth_order_centering_cancellation`: the bundled statement.
-/

open MeasureTheory Real Filter Topology
open DGPS DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Examples.SixthOrderCentering

open DGPS.Examples.PolynomialSpecies

/-- The centering `m_h = μ_h(P_h)` of the von Mises law `μ_h` against the feature
`P_h = cos 2θ - (h/3) cos θ`, in the angular variable. -/
noncomputable def vonMisesCentering (h : ℝ) : ℝ :=
  ∫ θ, (angMode 2 θ - h / 3 * angCos θ) * besselDensity h θ ∂angHaar

/-- The same mean on the torus `Torus 1`, using the EX052 feature `polyFeature h`. -/
noncomputable def vonMisesCenteringTorus (h : ℝ) : ℝ :=
  ∫ x, polyFeature h x * besselDensity h (angEquiv x) ∂haar 1

/-! ### Tail of a dominated nonnegative series -/

theorem tail_bound {f : ℕ → ℝ} {s a : ℝ} (hf : HasSum f s) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2)
    (h0 : ∀ j, 0 ≤ f j) (h1 : ∀ j, f j ≤ a ^ j) :
    0 ≤ s - ∑ j ∈ Finset.range 4, f j ∧ s - ∑ j ∈ Finset.range 4, f j ≤ 2 * a ^ 4 := by
  have hs : Summable fun j => f (j + 4) := (summable_nat_add_iff 4).2 hf.summable
  have e : s - ∑ j ∈ Finset.range 4, f j = ∑' j, f (j + 4) := by
    have := hf.summable.sum_add_tsum_nat_add 4
    rw [hf.tsum_eq] at this
    linarith
  rw [e]
  refine ⟨tsum_nonneg fun j => h0 _, ?_⟩
  have hg : Summable fun j : ℕ => a ^ (j + 4) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one ha0 (by linarith)).mul_right (a ^ 4)
  calc ∑' j, f (j + 4) ≤ ∑' j : ℕ, a ^ (j + 4) := hs.tsum_le_tsum (fun j => h1 _) hg
    _ = a ^ 4 * (1 - a)⁻¹ := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one ha0 (by linarith)]
        ring
    _ ≤ 2 * a ^ 4 := by
        have h4 : 0 ≤ a ^ 4 := by positivity
        have : (1 - a)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        nlinarith

/-- `I₀(h) = 1 + a + a²/4 + a³/36 + O(a⁴)` with `a = h²/4`. -/
theorem besselI_zero_expand (h : ℝ) (hh : |h| ≤ 1) :
    0 ≤ besselI 0 h - (1 + h ^ 2 / 4 + (h ^ 2 / 4) ^ 2 / 4 + (h ^ 2 / 4) ^ 3 / 36) ∧
    besselI 0 h - (1 + h ^ 2 / 4 + (h ^ 2 / 4) ^ 2 / 4 + (h ^ 2 / 4) ^ 3 / 36) ≤
      2 * (h ^ 2 / 4) ^ 4 := by
  have ha0 : 0 ≤ h ^ 2 / 4 := by positivity
  have ha : h ^ 2 / 4 ≤ 1 / 2 := by
    have : h ^ 2 ≤ 1 := by nlinarith [abs_nonneg h, sq_abs h]
    linarith
  have hf := hasSum_besselI_zero h
  have key := tail_bound hf ha0 ha (fun j => by positivity) (fun j => by
    have : (1 : ℝ) ≤ (j.factorial : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      nlinarith
    exact div_le_self (by positivity) this)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at key
  norm_num at key
  constructor <;> nlinarith [key.1, key.2]

/-- `I₁(h)/h = 1/2 + a/4 + a²/24 + a³/288 + O(a⁴)` with `a = h²/4`. -/
theorem besselI1Over_expand (h : ℝ) (hh : |h| ≤ 1) :
    0 ≤ besselI1Over h -
      (1 / 2 + (h ^ 2 / 4) / 4 + (h ^ 2 / 4) ^ 2 / 24 + (h ^ 2 / 4) ^ 3 / 288) ∧
    besselI1Over h -
      (1 / 2 + (h ^ 2 / 4) / 4 + (h ^ 2 / 4) ^ 2 / 24 + (h ^ 2 / 4) ^ 3 / 288) ≤
      2 * (h ^ 2 / 4) ^ 4 := by
  have ha0 : 0 ≤ h ^ 2 / 4 := by positivity
  have ha : h ^ 2 / 4 ≤ 1 / 2 := by
    have : h ^ 2 ≤ 1 := by nlinarith [abs_nonneg h, sq_abs h]
    linarith
  have hf := hasSum_besselI1Over h
  have key := tail_bound hf ha0 ha (fun j => by positivity) (fun j => by
    have h1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
    have h2 : (1 : ℝ) ≤ ((j + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero (j + 1))
    have h3 : (1 : ℝ) ≤ (j.factorial : ℝ) * ((j + 1).factorial : ℝ) := by nlinarith
    rw [mul_div_assoc]
    have : (1 / 2 : ℝ) * ((h ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))) ≤
        (h ^ 2 / 4) ^ j := by
      have : (h ^ 2 / 4) ^ j / ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)) ≤ (h ^ 2 / 4) ^ j :=
        div_le_self (by positivity) h3
      have h5 : 0 ≤ (h ^ 2 / 4) ^ j := by positivity
      linarith
    exact this)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at key
  norm_num at key
  constructor <;> nlinarith [key.1, key.2]

/-! ### The recurrence `I₀ - I₂ = 2 I₁/h` -/

theorem besselI_one_eq (t : ℝ) : besselI 1 t = t / 2 * (besselI 0 t - besselI 2 t) := by
  rw [besselI_eq_interval 1 t, besselI_eq_interval 0 t, besselI_eq_interval 2 t]
  have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume 0 (2 * π) :=
    fun g hg => hg.intervalIntegrable _ _
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun s => Real.exp (t * Real.cos s) * Real.sin s)
        (Real.exp (t * Real.cos s) * Real.cos s -
          t * (Real.exp (t * Real.cos s) * (1 - Real.cos (2 * s)) / 2)) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp (t * Real.cos s))
        (Real.exp (t * Real.cos s) * (t * (-Real.sin s))) s :=
      ((Real.hasDerivAt_cos s).const_mul t).exp
    have h2 := h1.mul (Real.hasDerivAt_sin s)
    convert h2 using 1
    have : Real.cos (2 * s) = 1 - 2 * Real.sin s ^ 2 := by
      rw [Real.cos_two_mul, Real.cos_sq']; ring
    rw [this]
    ring
  have hint : IntervalIntegrable (fun s => Real.exp (t * Real.cos s) * Real.cos s -
      t * (Real.exp (t * Real.cos s) * (1 - Real.cos (2 * s)) / 2)) MeasureTheory.volume
      0 (2 * π) := hc _ (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [Real.sin_zero, mul_zero, Real.sin_two_pi, sub_self] at hftc
  rw [intervalIntegral.integral_sub (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_const_mul] at hftc
  have e0 : ∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * (1 - Real.cos (2 * s)) / 2 =
      (∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos (((0 : ℕ) : ℝ) * s)) / 2 -
      (∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos (((2 : ℕ) : ℝ) * s)) / 2 := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div,
      ← intervalIntegral.integral_sub (hc _ (by fun_prop)) (hc _ (by fun_prop))]
    congr 1
    funext s
    push_cast
    rw [zero_mul, Real.cos_zero]
    ring
  rw [e0] at hftc
  have e1 : (∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos (((1 : ℕ) : ℝ) * s)) =
      ∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos s := by
    simp
  rw [e1]
  have hpi : (2 * π)⁻¹ * (2 * π) = 1 := inv_mul_cancel₀ (by positivity)
  generalize (∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos s) = A at *
  generalize (∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos (((0 : ℕ) : ℝ) * s)) = B at *
  generalize (∫ s in (0 : ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos (((2 : ℕ) : ℝ) * s)) = D at *
  have : A = t * (B / 2 - D / 2) := by linarith
  rw [this]
  ring

theorem continuous_besselI (n : ℕ) : Continuous (besselI n) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_besselI n t).continuousAt

theorem besselI_two_eq (t : ℝ) : besselI 2 t = besselI 0 t - 2 * besselI1Over t := by
  have hfun : besselI 2 = fun t => besselI 0 t - 2 * besselI1Over t := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℝ)) (continuous_besselI 2)
      ((continuous_besselI 0).sub (continuous_const.mul continuous_besselI1Over)) ?_
    intro t ht
    have ht' : t ≠ 0 := ht
    have h1 := besselI_one_eq t
    have h2 := besselI1Over_of_ne t ht'
    simp only
    rw [h2]
    field_simp
    linarith
  rw [hfun]

/-! ### Expansion of the quotient `(I₁/h)/I₀` -/

/-- The truncated series of `(I₁/h)/I₀` in `a = h²/4`. -/
noncomputable def quotientPoly (a : ℝ) : ℝ := 1 / 2 - a / 4 + a ^ 2 / 6 - 11 * a ^ 3 / 96

theorem quotient_core (a I0 J : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4)
    (e0 : 0 ≤ I0 - (1 + a + a ^ 2 / 4 + a ^ 3 / 36))
    (e0' : I0 - (1 + a + a ^ 2 / 4 + a ^ 3 / 36) ≤ 2 * a ^ 4)
    (e1 : 0 ≤ J - (1 / 2 + a / 4 + a ^ 2 / 24 + a ^ 3 / 288))
    (e1' : J - (1 / 2 + a / 4 + a ^ 2 / 24 + a ^ 3 / 288) ≤ 2 * a ^ 4) :
    1 ≤ I0 ∧ |J / I0 - quotientPoly a| ≤ 4 * a ^ 4 := by
  have hI : 1 ≤ I0 := by
    have : 0 ≤ a ^ 2 / 4 := by positivity
    have : 0 ≤ a ^ 3 / 36 := by positivity
    linarith
  refine ⟨hI, ?_⟩
  have hI0 : 0 < I0 := by linarith
  have hQ0 : 0 ≤ quotientPoly a := by unfold quotientPoly; nlinarith [sq_nonneg a, pow_nonneg ha0 3]
  have hQ1 : quotientPoly a ≤ 1 / 2 := by unfold quotientPoly; nlinarith [sq_nonneg a, pow_nonneg ha0 3]
  have hA : 0 ≤ a ^ 4 := by positivity
  have hS0 : 0 ≤ 23 / 288 + 83 * a / 3456 + 11 * a ^ 2 / 3456 := by positivity
  have hS1 : 23 / 288 + 83 * a / 3456 + 11 * a ^ 2 / 3456 ≤ 1 / 10 := by nlinarith
  have hid : J - quotientPoly a * I0 =
      a ^ 4 * (23 / 288 + 83 * a / 3456 + 11 * a ^ 2 / 3456) +
      (J - (1 / 2 + a / 4 + a ^ 2 / 24 + a ^ 3 / 288)) -
      quotientPoly a * (I0 - (1 + a + a ^ 2 / 4 + a ^ 3 / 36)) := by
    unfold quotientPoly; ring
  have m1 := mul_le_mul_of_nonneg_left e0' hQ0
  have m2 := mul_nonneg hQ0 e0
  have m3 := mul_le_mul_of_nonneg_left hS1 hA
  have m4 := mul_nonneg hA hS0
  have m5 := mul_le_mul_of_nonneg_right hQ1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
  have hb : |J - quotientPoly a * I0| ≤ 4 * a ^ 4 := by
    rw [abs_le]
    constructor <;> nlinarith
  have : J / I0 - quotientPoly a = (J - quotientPoly a * I0) / I0 := by
    field_simp
  rw [this, abs_div, abs_of_pos hI0, div_le_iff₀ hI0]
  nlinarith

theorem besselI_one_eq_mul (h : ℝ) : besselI 1 h = h * besselI1Over h := by
  by_cases hh : h = 0
  · subst hh
    have := besselI_neg 1 0
    simp at this
    simp
    linarith
  · rw [besselI1Over_of_ne h hh]
    field_simp

theorem quotient_ratio_identities (h : ℝ) (hI : 0 < besselI 0 h) :
    besselI 2 h / besselI 0 h = 1 - 2 * (besselI1Over h / besselI 0 h) ∧
    (h / 3) * besselI 1 h / besselI 0 h = (h ^ 2 / 3) * (besselI1Over h / besselI 0 h) := by
  constructor
  · rw [besselI_two_eq]
    field_simp
  · rw [besselI_one_eq_mul]
    field_simp

/-! ### The centering as a ratio of Bessel functions -/

theorem vonMisesCentering_eq (h : ℝ) :
    vonMisesCentering h = besselI 2 h / besselI 0 h - (h / 3) * besselI 1 h / besselI 0 h := by
  have hI : 0 < besselI 0 h := besselI_zero_pos h
  have hcm2 : Continuous (angMode 2) := continuous_angMode 2
  have hcm1 : Continuous (angMode 1) := continuous_angMode 1
  have i2 := integrable_exp_mul h (angMode 2) hcm2 (abs_angMode_le 2)
  have i1 := integrable_exp_mul h (angMode 1) hcm1 (abs_angMode_le 1)
  have e : ∀ θ, (angMode 2 θ - h / 3 * angCos θ) * besselDensity h θ =
      (Real.exp (h * angCos θ) * angMode 2 θ -
        h / 3 * (Real.exp (h * angCos θ) * angMode 1 θ)) / besselI 0 h := by
    intro θ
    unfold besselDensity
    simp only [angCos]
    ring
  simp_rw [vonMisesCentering, e]
  rw [integral_div, integral_sub i2 (i1.const_mul _), integral_const_mul]
  have hb1 : besselI 1 h = ∫ θ, Real.exp (h * angCos θ) * angMode 1 θ ∂angHaar := rfl
  have hb2 : besselI 2 h = ∫ θ, Real.exp (h * angCos θ) * angMode 2 θ ∂angHaar := rfl
  rw [← hb1, ← hb2]
  ring

theorem polyFeature_eq_ang (h : ℝ) (x : Torus 1) :
    polyFeature h x = angMode 2 (angEquiv x) - h / 3 * angCos (angEquiv x) := by
  obtain ⟨t, rfl⟩ := exists_lift x
  have e : angEquiv (torusLift (fun _ => t)) = ((2 * π * t : ℝ) : AngCircle) := by
    rw [angEquiv_apply]
    exact angRescale_mk t
  rw [e]
  unfold polyFeature
  simp only [cosT_lift, angCos, angMode_coe]
  have h2 : 2 * π * ((2 : ℕ) : ℝ) * t = ((2 : ℕ) : ℝ) * (2 * π * t) := by ring
  have h1 : 2 * π * ((1 : ℕ) : ℝ) * t = ((1 : ℕ) : ℝ) * (2 * π * t) := by ring
  simp only [h1, h2]

theorem vonMisesCenteringTorus_eq (h : ℝ) :
    vonMisesCenteringTorus h = vonMisesCentering h := by
  unfold vonMisesCenteringTorus vonMisesCentering
  rw [← integral_comp_angEquiv (fun θ => (angMode 2 θ - h / 3 * angCos θ) * besselDensity h θ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [polyFeature_eq_ang]

end DGPS.Examples.SixthOrderCentering

namespace DGPS.Examples

open DGPS.Examples.SixthOrderCentering DGPS.Circle.BesselMoments

/-- **EX053.** Sixth-order centering cancellation.  Let `μ_h` be the von Mises law
`dμ_h = I₀(h)⁻¹ exp(h cos θ) dθ/(2π)` (`besselDensity h` against `angHaar`) and `P_h` the feature
`cos 2θ - (h/3) cos θ` of the canonical elementary polynomial model (EX052).  Then the centering
`m_h = μ_h(P_h)` (computed in the angular variable, `vonMisesCentering`, and on `Torus 1` through
`polyFeature`, `vonMisesCenteringTorus`) is `I₂(h)/I₀(h) - (h/3) I₁(h)/I₀(h)` exactly, and on the
common interval `|h| ≤ 1` with explicit constant `C = 1`:

* `I₂/I₀ = h²/8 - h⁴/48 + 11h⁶/3072 + O(h⁸)`,
* `(h/3) I₁/I₀ = h²/6 - h⁴/48 + h⁶/288 + O(h⁸)`,
* `m_h = -h²/24 + h⁶/9216 + O(h⁸)` (no `h⁴` term; `11/3072 - 1/288 = 1/9216`). -/
theorem sixth_order_centering_cancellation :
    (∀ h : ℝ, vonMisesCenteringTorus h = vonMisesCentering h ∧
      vonMisesCentering h =
        besselI 2 h / besselI 0 h - (h / 3) * besselI 1 h / besselI 0 h) ∧
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      |besselI 2 h / besselI 0 h - (h ^ 2 / 8 - h ^ 4 / 48 + 11 * h ^ 6 / 3072)| ≤ C * h ^ 8 ∧
      |(h / 3) * besselI 1 h / besselI 0 h - (h ^ 2 / 6 - h ^ 4 / 48 + h ^ 6 / 288)| ≤
        C * h ^ 8 ∧
      |vonMisesCentering h - (-h ^ 2 / 24 + h ^ 6 / 9216)| ≤ C * h ^ 8 := by
  refine ⟨fun h => ⟨vonMisesCenteringTorus_eq h, vonMisesCentering_eq h⟩, 1, 1, one_pos,
    one_pos, fun h hh => ?_⟩
  have hI0pos : 0 < besselI 0 h := besselI_zero_pos h
  obtain ⟨e0, e0'⟩ := besselI_zero_expand h hh
  obtain ⟨e1, e1'⟩ := besselI1Over_expand h hh
  have ha0 : 0 ≤ h ^ 2 / 4 := by positivity
  have h2 : h ^ 2 ≤ 1 := by nlinarith [abs_nonneg h, sq_abs h]
  have ha : h ^ 2 / 4 ≤ 1 / 4 := by linarith
  obtain ⟨-, hq⟩ := quotient_core (h ^ 2 / 4) (besselI 0 h) (besselI1Over h) ha0 ha e0 e0' e1 e1'
  obtain ⟨r2, r1⟩ := quotient_ratio_identities h hI0pos
  rw [r2, r1]
  set r := besselI1Over h / besselI 0 h with hr
  have hA : 0 ≤ (h ^ 2 / 4) ^ 4 := by positivity
  have hP : (h ^ 2 / 4) ^ 4 = h ^ 8 / 256 := by ring
  have hT2 : h ^ 2 / 8 - h ^ 4 / 48 + 11 * h ^ 6 / 3072 = 1 - 2 * quotientPoly (h ^ 2 / 4) := by
    unfold quotientPoly; ring
  have hT1 : h ^ 2 / 6 - h ^ 4 / 48 + h ^ 6 / 288 =
      (h ^ 2 / 3) * quotientPoly (h ^ 2 / 4) + 11 * (h ^ 2 / 4) ^ 4 / 72 := by
    unfold quotientPoly; ring
  have hTm : -h ^ 2 / 24 + h ^ 6 / 9216 =
      (1 - 2 * quotientPoly (h ^ 2 / 4)) - ((h ^ 2 / 3) * quotientPoly (h ^ 2 / 4)
        + 11 * (h ^ 2 / 4) ^ 4 / 72) := by
    unfold quotientPoly; ring
  rw [abs_le] at hq
  obtain ⟨hq1, hq2⟩ := hq
  have hh2 : 0 ≤ h ^ 2 / 3 := by positivity
  have hh2' : h ^ 2 / 3 ≤ 1 / 3 := by linarith
  have m1 := mul_le_mul_of_nonneg_left hq2 hh2
  have m2 := mul_le_mul_of_nonneg_left hq1 hh2
  have m3 := mul_le_mul_of_nonneg_right hh2' hA
  have hh8 : 0 ≤ h ^ 8 := by positivity
  rw [vonMisesCentering_eq, r2, r1, hT2, hT1, hTm]
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith
