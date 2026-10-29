import DGPS.Frontier.STR029.T07
import DGPS.Frontier.STR029.T08
import DGPS.Frontier.STR029.T10
import DGPS.Frontier.STR029.T35
import DGPS.Frontier.STR029.T45

/-!
# STR029.11: Positive-entropy attainment in the angular finite-information domain

Task id: STR029.11. Title: Positive-entropy attainment in the angular finite-information domain.
Prerequisites: STR029.07, STR029.08, STR029.10 (modules `DGPS.Frontier.STR029.T07`, `T08`, `T10`).

## Provides

* `DGPS.Frontier.STR029.str029_11_positive_entropy_attainment_angular_finite_information`: there is
  `0 < δ ≤ 1/1000` such that every real `h` with `0 < |h| < δ` has an admissible pair `(G, d)` with
  positive angular entropy whose angular quotient equals the infimum of the angular quotients over
  the admissible pairs.
* Helpers, each with the suffix `_STR02911`: the angular entropy, domain, quotient and quotient set;
  the trial function of STR029.10; the chart amplitude `gChart_STR02911`, which realizes a chart
  density as the square of an admissible function; the entropy identity and the vanishing-entropy
  step; and the two cases of the compactness argument.

## R5 notes

1. Domain. `angDom_STR02911 h g d` records `g ≥ 0`, `d` a periodic weak derivative of `g` in the
   STR029.33 convention `IsPeriodicWeakDerivative_STR02933 g d`, `∫ g² q_h dm = 1`, and positive
   angular entropy. Integrals are the STR029.04 interval integrals `normInt_STR02904`, bridged to the
   STR029.33 carrier by `normInt_eq_STR02935` where the chart quantities need it.
2. Quotient. `angQuot_STR02911 h g d = 4 ∫ d² q_h dm / (2 · angEnt h g)`, the STR029.08 quotient.
3. Attainment. The conclusion quantifies over pairs `(G, d)` in the domain. The energy of `G` does
   not depend on the chosen weak derivative (STR029.42 energy uniqueness), so attainment over pairs
   is the intended statement.
4. Chart witness. For a smooth periodic `u` with positive chart entropy, the function
   `G = exp(u/2) sqrt(refNorm / chartNorm)` satisfies `G² = ρ(h,u)/q_h`, hence `∫ G² q_h dm = 1`
   and `angEnt h G = chartEntropy h u`. Its classical derivative is `(u'/2) G`, so the angular
   quotient equals `chartFisher h u / (2 chartEntropy h u)`.
5. Entropy. The integrand `z log z` is not nonnegative on `(0,1)`. The integrand
   `(z log z - z + 1) q_h` is nonnegative and has integral `angEnt h G`, because `∫ G² q_h dm = 1`
   and `∫ q_h dm = 1`. Zero entropy therefore forces `G² = 1` almost everywhere.
6. Case split. A minimizing sequence in the quotient set gives, via STR029.07, a subsequence and a
   limit `G`. If `angEnt h G > 0`, the energy passage gives `angQuot h G d ≤ m` with `m` the infimum.
   If `angEnt h G = 0`, then `G = 1` almost everywhere, the STR029.08 bound forces `m ≥ 1 - h²`, and
   that contradicts the chart bound `m < 1 - h²`.
7. Scope. The step `δ` and the bound `δ ≤ 1/1000` are those of STR029.10, unchanged. The bound
   `|h| ≤ 1/1000` needed by STR029.07 and STR029.08 follows from `δ ≤ 1/1000`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace DGPS.Frontier.STR029

/-- Angular entropy `∫ g² log (g²) q_h dm` on the STR029.04 carrier. -/
noncomputable def angEnt_STR02911 (h : ℝ) (g : ℝ → ℝ) : ℝ :=
  normInt_STR02904 (fun t => g t ^ 2 * Real.log (g t ^ 2) * qT_STR02904 h t)

/-- The angular finite-information domain with positive entropy. -/
abbrev angDom_STR02911 (h : ℝ) (g d : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ g t) ∧ IsPeriodicWeakDerivative_STR02933 g d ∧
    normInt_STR02904 (fun t => g t ^ 2 * qT_STR02904 h t) = 1 ∧ 0 < angEnt_STR02911 h g

/-- The angular quotient `4 ∫ d² q_h dm / (2 · angEnt h g)`. -/
noncomputable def angQuot_STR02911 (h : ℝ) (g d : ℝ → ℝ) : ℝ :=
  4 * normInt_STR02904 (fun t => d t ^ 2 * qT_STR02904 h t) / (2 * angEnt_STR02911 h g)

/-- The set of angular quotients over the domain. -/
abbrev angSet_STR02911 (h : ℝ) : Set ℝ :=
  {q | ∃ g d : ℝ → ℝ, angDom_STR02911 h g d ∧ q = angQuot_STR02911 h g d}

/-- The trial function of STR029.10. -/
noncomputable abbrev trialU_STR02911 (h : ℝ) : ℝ → ℝ := fun t : ℝ =>
  2 * h * Real.cos t + h ^ 2 * ((2 / 3) * Real.cos (2 * t) - (1 / 5) * Real.cos (4 * t))

/-- The chart amplitude `G = exp(u/2) sqrt(refNorm / chartNorm)`. -/
noncomputable def gChart_STR02911 (h : ℝ) (u : ℝ → ℝ) : ℝ → ℝ := fun t =>
  Real.exp (u t / 2) * Real.sqrt (refNorm_STR02945 h / chartNorm_STR02945 h u)

/-! ### Normalization and positivity of the chart quantities -/

theorem refNorm_pos_STR02911 (h : ℝ) : 0 < refNorm_STR02945 h := by
  unfold refNorm_STR02945
  rw [normInt_eq_STR02935]
  exact partition_pos_STR02904 h

theorem chartNorm_pos_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : Continuous u) :
    0 < chartNorm_STR02945 h u := by
  unfold chartNorm_STR02945
  rw [normInt_eq_STR02935]
  unfold normInt_STR02904
  refine mul_pos (inv_pos.mpr (by positivity)) ?_
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ (by positivity)
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro x _
    exact Real.exp_pos _

theorem normInt_div_const_STR02911 (f : ℝ → ℝ) (c : ℝ) :
    normInt_STR02933 (fun t => f t / c) = normInt_STR02933 f / c := by
  unfold normInt_STR02933
  rw [integral_div]
  ring

theorem normInt_const_mul_STR02911 (c : ℝ) (f : ℝ → ℝ) :
    normInt_STR02933 (fun t => c * f t) = c * normInt_STR02933 f := by
  unfold normInt_STR02933
  rw [integral_const_mul]
  ring

theorem normInt_chartDensity_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : Continuous u) :
    normInt_STR02933 (fun t => chartDensity_STR02945 h u t) = 1 := by
  have hC := chartNorm_pos_STR02911 (h := h) hu
  show normInt_STR02933
    (fun t => Real.exp (h * Real.cos (3 * t) + u t) / chartNorm_STR02945 h u) = 1
  rw [normInt_div_const_STR02911]
  exact div_self hC.ne'

theorem qT_eq_ref_STR02911 (h t : ℝ) : qT_STR02904 h t = refDensity_STR02945 h t := by
  unfold qT_STR02904 refDensity_STR02945 refNorm_STR02945
  rw [normInt_eq_STR02935]

/-! ### The chart amplitude -/

theorem gChart_nonneg_STR02911 (h : ℝ) (u : ℝ → ℝ) (t : ℝ) : 0 ≤ gChart_STR02911 h u t := by
  unfold gChart_STR02911
  exact mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

theorem gChart_sq_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    gChart_STR02911 h u t ^ 2 = chartRatio_STR02945 h u t := by
  have hR := refNorm_pos_STR02911 h
  have hC := chartNorm_pos_STR02911 (h := h) hu
  have hR0 := hR.ne'
  have hC0 := hC.ne'
  have he : Real.exp (u t / 2) ^ 2 = Real.exp (u t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hs : Real.sqrt (refNorm_STR02945 h / chartNorm_STR02945 h u) ^ 2 =
      refNorm_STR02945 h / chartNorm_STR02945 h u :=
    Real.sq_sqrt (div_pos hR hC).le
  have h1 := (Real.exp_pos (h * Real.cos (3 * t))).ne'
  have h2 := (Real.exp_pos (u t)).ne'
  unfold gChart_STR02911 chartRatio_STR02945 chartDensity_STR02945 refDensity_STR02945
  rw [mul_pow, he, hs, Real.exp_add]
  field_simp

theorem gChart_sq_qT_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    gChart_STR02911 h u t ^ 2 * qT_STR02904 h t = chartDensity_STR02945 h u t := by
  have hR : refDensity_STR02945 h t ≠ 0 :=
    (div_pos (Real.exp_pos _) (refNorm_pos_STR02911 h)).ne'
  rw [gChart_sq_STR02911 hu, qT_eq_ref_STR02911]
  unfold chartRatio_STR02945
  exact div_mul_cancel₀ _ hR

theorem normInt_gChart_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : Continuous u) :
    normInt_STR02904 (fun t => gChart_STR02911 h u t ^ 2 * qT_STR02904 h t) = 1 := by
  have hfun : (fun t => gChart_STR02911 h u t ^ 2 * qT_STR02904 h t) =
      fun t => chartDensity_STR02945 h u t :=
    funext fun t => gChart_sq_qT_STR02911 hu t
  rw [hfun, ← normInt_eq_STR02935]
  exact normInt_chartDensity_STR02911 hu

theorem gChart_contDiff_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (gChart_STR02911 h u) := by
  unfold gChart_STR02911
  exact (Real.contDiff_exp.comp (hu.div_const 2)).mul contDiff_const

theorem gChart_periodic_STR02911 {h : ℝ} {u : ℝ → ℝ} (hper : Function.Periodic u (2 * π)) :
    Function.Periodic (gChart_STR02911 h u) (2 * π) := by
  intro t
  unfold gChart_STR02911
  rw [hper t]

theorem deriv_gChart_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) :
    deriv (gChart_STR02911 h u) t = deriv u t / 2 * gChart_STR02911 h u t := by
  have hd : HasDerivAt u (deriv u t) t := ((hu.differentiable (by simp)) t).hasDerivAt
  have h1 : HasDerivAt (fun s => Real.exp (u s / 2)) (Real.exp (u t / 2) * (deriv u t / 2)) t :=
    (hd.div_const 2).exp
  have h2 : HasDerivAt (gChart_STR02911 h u)
      (Real.exp (u t / 2) * (deriv u t / 2) *
        Real.sqrt (refNorm_STR02945 h / chartNorm_STR02945 h u)) t :=
    h1.mul_const _
  rw [h2.deriv]
  unfold gChart_STR02911
  ring

theorem gChart_deriv_sq_qT_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) :
    deriv (gChart_STR02911 h u) t ^ 2 * qT_STR02904 h t =
      1 / 4 * (deriv u t ^ 2 * chartDensity_STR02945 h u t) := by
  rw [deriv_gChart_STR02911 hu, ← gChart_sq_qT_STR02911 hu.continuous t]
  ring

theorem angEnt_gChart_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : Continuous u) :
    angEnt_STR02911 h (gChart_STR02911 h u) = chartEntropy_STR02945 h u := by
  have hfun : (fun t => gChart_STR02911 h u t ^ 2 * Real.log (gChart_STR02911 h u t ^ 2) *
        qT_STR02904 h t) =
      fun t => chartRatio_STR02945 h u t * Real.log (chartRatio_STR02945 h u t) *
        refDensity_STR02945 h t := by
    funext t
    rw [gChart_sq_STR02911 hu, qT_eq_ref_STR02911]
  unfold angEnt_STR02911 chartEntropy_STR02945
  rw [hfun, normInt_eq_STR02935]

theorem angQuot_gChart_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    angQuot_STR02911 h (gChart_STR02911 h u) (deriv (gChart_STR02911 h u)) =
      chartFisher_STR02945 h u / (2 * chartEntropy_STR02945 h u) := by
  have hfun : (fun t => deriv (gChart_STR02911 h u) t ^ 2 * qT_STR02904 h t) =
      fun t => 1 / 4 * (deriv u t ^ 2 * chartDensity_STR02945 h u t) :=
    funext fun t => gChart_deriv_sq_qT_STR02911 hu t
  unfold angQuot_STR02911
  rw [angEnt_gChart_STR02911 hu.continuous, hfun, ← normInt_eq_STR02935,
    normInt_const_mul_STR02911]
  unfold chartFisher_STR02945
  ring

/-- Chart witness: a smooth periodic chart with positive entropy gives an admissible pair whose
angular quotient is the chart quotient `I / (2 H)`. -/
theorem chart_witness_STR02911 {h : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u (2 * π)) (hE : 0 < chartEntropy_STR02945 h u) :
    ∃ G d : ℝ → ℝ, angDom_STR02911 h G d ∧
      angQuot_STR02911 h G d = chartFisher_STR02945 h u / (2 * chartEntropy_STR02945 h u) := by
  refine ⟨gChart_STR02911 h u, deriv (gChart_STR02911 h u),
    ⟨fun t => gChart_nonneg_STR02911 h u t,
      weak_of_smooth_STR02935 (gChart_contDiff_STR02911 hu) (gChart_periodic_STR02911 hper),
      normInt_gChart_STR02911 hu.continuous, ?_⟩,
    angQuot_gChart_STR02911 hu⟩
  rw [angEnt_gChart_STR02911 hu.continuous]
  exact hE

/-! ### The trial function -/

theorem trialU_contDiff_STR02911 (h : ℝ) : ContDiff ℝ ∞ (trialU_STR02911 h) := by
  unfold trialU_STR02911
  fun_prop

theorem trialU_periodic_STR02911 (h : ℝ) : Function.Periodic (trialU_STR02911 h) (2 * π) := by
  intro t
  have h2 : Real.cos (2 * (t + 2 * π)) = Real.cos (2 * t) := by
    rw [show 2 * (t + 2 * π) = 2 * t + ((2 : ℕ) : ℝ) * (2 * π) by push_cast; ring]
    exact Real.cos_add_nat_mul_two_pi _ _
  have h4 : Real.cos (4 * (t + 2 * π)) = Real.cos (4 * t) := by
    rw [show 4 * (t + 2 * π) = 4 * t + ((4 : ℕ) : ℝ) * (2 * π) by push_cast; ring]
    exact Real.cos_add_nat_mul_two_pi _ _
  simp only [trialU_STR02911]
  rw [h2, h4, Real.cos_add_two_pi]

/-! ### Entropy identity and the vanishing-entropy step -/

theorem zDiff_nonneg_STR02911 {z : ℝ} (hz : 0 ≤ z) : 0 ≤ z * Real.log z - z + 1 := by
  rcases hz.eq_or_lt with rfl | hpos
  · simp
  · have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h1
    have h2 : z * (-Real.log z) ≤ z * (z⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 hz
    have h3 : z * (z⁻¹ - 1) = 1 - z := by
      rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one]
    have h4 : z * (-Real.log z) = -(z * Real.log z) := by ring
    linarith

theorem zDiff_eq_zero_STR02911 {z : ℝ} (hz : 0 ≤ z) (h0 : z * Real.log z - z + 1 = 0) :
    z = 1 := by
  by_contra hne
  rcases hz.eq_or_lt with rfl | hpos
  · norm_num at h0
  · have h1 := Real.log_lt_sub_one_of_pos (inv_pos.mpr hpos) (inv_ne_one.mpr hne)
    rw [Real.log_inv] at h1
    have h2 : z * (-Real.log z) < z * (z⁻¹ - 1) := mul_lt_mul_of_pos_left h1 hpos
    have h3 : z * (z⁻¹ - 1) = 1 - z := by
      rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one]
    have h4 : z * (-Real.log z) = -(z * Real.log z) := by ring
    linarith

theorem normInt04_lin3_STR02911 {f1 f2 f3 : ℝ → ℝ} (c1 c2 c3 : ℝ) (h1 : Continuous f1)
    (h2 : Continuous f2) (h3 : Continuous f3) :
    normInt_STR02904 (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t) =
      c1 * normInt_STR02904 f1 + c2 * normInt_STR02904 f2 + c3 * normInt_STR02904 f3 := by
  rw [← normInt_eq_STR02935 (fun t => c1 * f1 t + c2 * f2 t + c3 * f3 t),
    normInt_lin3_STR02945 c1 c2 c3 h1 h2 h3, normInt_eq_STR02935 f1,
    normInt_eq_STR02935 f2, normInt_eq_STR02935 f3]

theorem normInt04_nonneg_STR02911 {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) :
    0 ≤ normInt_STR02904 f := by
  unfold normInt_STR02904
  refine mul_nonneg (by positivity) ?_
  exact intervalIntegral.integral_nonneg (by positivity) (fun t _ => hf t)

theorem zDiff_integrand_cont_STR02911 {h : ℝ} {G : ℝ → ℝ} (hG : Continuous G) :
    Continuous (fun t => (G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1) * qT_STR02904 h t) :=
  (((Real.continuous_mul_log.comp (hG.pow 2)).sub (hG.pow 2)).add continuous_const).mul
    (continuous_qT_STR02904 h)

theorem angEnt_eq_zDiff_STR02911 {h : ℝ} {G : ℝ → ℝ} (hG : Continuous G)
    (hn : normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1) :
    normInt_STR02904 (fun t => (G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1) * qT_STR02904 h t) =
      angEnt_STR02911 h G := by
  have hc1 : Continuous (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t) :=
    (Real.continuous_mul_log.comp (hG.pow 2)).mul (continuous_qT_STR02904 h)
  have hc2 : Continuous (fun t => G t ^ 2 * qT_STR02904 h t) :=
    (hG.pow 2).mul (continuous_qT_STR02904 h)
  have hc3 : Continuous (qT_STR02904 h) := continuous_qT_STR02904 h
  have hq : normInt_STR02904 (qT_STR02904 h) = 1 := by
    rw [← normInt_eq_STR02935]
    exact normInt_qT_STR02935 h
  have hfun : (fun t => (G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1) * qT_STR02904 h t) =
      fun t => (1 : ℝ) * (G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t) +
        (-1 : ℝ) * (G t ^ 2 * qT_STR02904 h t) + (1 : ℝ) * qT_STR02904 h t := by
    funext t
    ring
  rw [hfun, normInt04_lin3_STR02911 1 (-1) 1 hc1 hc2 hc3, hn, hq]
  unfold angEnt_STR02911
  ring

theorem angEnt_nonneg_STR02911 {h : ℝ} {G : ℝ → ℝ} (hG : Continuous G)
    (hn : normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1) :
    0 ≤ angEnt_STR02911 h G := by
  rw [← angEnt_eq_zDiff_STR02911 hG hn]
  exact normInt04_nonneg_STR02911 fun t =>
    mul_nonneg (zDiff_nonneg_STR02911 (sq_nonneg _)) (qT_pos_STR02904 h t).le

theorem G_one_ae_STR02911 {h : ℝ} {G : ℝ → ℝ} (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (hn : normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1)
    (hz : angEnt_STR02911 h G = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), G t = 1 := by
  have hid := angEnt_eq_zDiff_STR02911 hG hn
  rw [hz] at hid
  have hnn : (0 : ℝ → ℝ) ≤ fun t =>
      (G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1) * qT_STR02904 h t := by
    intro t
    exact mul_nonneg (zDiff_nonneg_STR02911 (sq_nonneg _)) (qT_pos_STR02904 h t).le
  have hint : Integrable
      (fun t => (G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1) * qT_STR02904 h t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    (zDiff_integrand_cont_STR02911 (h := h) hG).integrableOn_Ioc
  have hI : ∫ t in Ioc 0 (2 * π),
      (G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1) * qT_STR02904 h t = 0 := by
    unfold normInt_STR02904 at hid
    rcases mul_eq_zero.mp hid with h0 | h0
    · exact absurd h0 (inv_ne_zero (by positivity))
    · rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * π by positivity)] at h0
      exact h0
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp hI
  filter_upwards [hae] with t ht
  have ht' : (G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1) * qT_STR02904 h t = 0 := ht
  have hz1 : G t ^ 2 * Real.log (G t ^ 2) - G t ^ 2 + 1 = 0 := by
    rcases mul_eq_zero.mp ht' with h1 | h1
    · exact h1
    · exact absurd h1 (qT_pos_STR02904 h t).ne'
  have hsq : G t ^ 2 = 1 := zDiff_eq_zero_STR02911 (sq_nonneg _) hz1
  have hG0t := hG0 t
  nlinarith

theorem angQuot_nonneg_STR02911 {h : ℝ} {g d : ℝ → ℝ} (hd : angDom_STR02911 h g d) :
    0 ≤ angQuot_STR02911 h g d := by
  obtain ⟨-, -, -, hE⟩ := hd
  unfold angQuot_STR02911
  refine div_nonneg (mul_nonneg (by norm_num) (normInt04_nonneg_STR02911 fun t => ?_))
    (by linarith)
  exact mul_nonneg (sq_nonneg _) (qT_pos_STR02904 h t).le

/-! ### The attainment core -/

/-- Attainment core: if some admissible pair has quotient below `1 - h²`, the infimum of the
quotient set is attained by an admissible pair. -/
theorem attain_core_STR02911 {h : ℝ} (hh : |h| ≤ 1 / 1000)
    (hw : ∃ G d : ℝ → ℝ, angDom_STR02911 h G d ∧ angQuot_STR02911 h G d < 1 - h ^ 2) :
    ∃ G d : ℝ → ℝ, angDom_STR02911 h G d ∧ angQuot_STR02911 h G d = sInf (angSet_STR02911 h) := by
  obtain ⟨G0, d0, hd0, hq0⟩ := hw
  have hne : (angSet_STR02911 h).Nonempty := ⟨angQuot_STR02911 h G0 d0, G0, d0, hd0, rfl⟩
  have hbdd : BddBelow (angSet_STR02911 h) :=
    ⟨0, by rintro q ⟨g, d, hdom, rfl⟩; exact angQuot_nonneg_STR02911 hdom⟩
  have hmle : ∀ q ∈ angSet_STR02911 h, sInf (angSet_STR02911 h) ≤ q :=
    fun q hq => csInf_le hbdd hq
  have hm_lt : sInf (angSet_STR02911 h) < 1 - h ^ 2 :=
    lt_of_le_of_lt (hmle _ ⟨G0, d0, hd0, rfl⟩) hq0
  set m := sInf (angSet_STR02911 h) with hm
  have happrox : ∀ n : ℕ, ∃ q ∈ angSet_STR02911 h, q < m + 1 / ((n : ℝ) + 1) := fun n =>
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right m (by positivity))
  choose qs hqsS hqs using happrox
  have hrep : ∀ n, ∃ g d : ℝ → ℝ, angDom_STR02911 h g d ∧ qs n = angQuot_STR02911 h g d :=
    fun n => hqsS n
  choose gn dn hdom hqeq using hrep
  have hqs2 : ∀ n, qs n ≤ 2 := fun n => by
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : 0 ≤ h ^ 2 := sq_nonneg h
    linarith [hqs n]
  have hqlim : Tendsto qs atTop (𝓝 m) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) atTop (𝓝 m) := by
      simpa using h0.const_add m
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => hmle _ (hqsS n)) (fun n => (hqs n).le)
  have hH0 : ∀ n, 0 < angEnt_STR02911 h (gn n) := fun n => (hdom n).2.2.2
  have hEq : ∀ n, normInt_STR02904 (fun t => dn n t ^ 2 * qT_STR02904 h t) =
      qs n * angEnt_STR02911 h (gn n) / 2 := by
    intro n
    have hne0 : angEnt_STR02911 h (gn n) ≠ 0 := (hH0 n).ne'
    rw [hqeq n]
    unfold angQuot_STR02911
    field_simp
    ring
  have hquot : ∀ n, 4 * normInt_STR02904 (fun t => dn n t ^ 2 * qT_STR02904 h t) /
      (2 * angEnt_STR02911 h (gn n)) ≤ 2 := fun n => by
    have e : angQuot_STR02911 h (gn n) (dn n) =
        4 * normInt_STR02904 (fun t => dn n t ^ 2 * qT_STR02904 h t) /
          (2 * angEnt_STR02911 h (gn n)) := rfl
    rw [← e, ← hqeq n]
    exact hqs2 n
  obtain ⟨F, hF, σ, hσ, G, d, ⟨hGc, -, hG0, hGn, hGu⟩, hd, -, hHlim, henergy⟩ :=
    str029_07_compactness_entropy_energy_passage (g := gn) (g' := dn)
      (E := fun n => normInt_STR02904 (fun t => dn n t ^ 2 * qT_STR02904 h t))
      (H := fun n => angEnt_STR02911 h (gn n)) hh
      (fun n t => (hdom n).1 t) (fun n => (hdom n).2.1) (fun n => (hdom n).2.2.1)
      (fun n => rfl) (fun n => rfl) hH0 hquot rfl rfl
  have hqσ : Tendsto (fun n => qs (σ n)) atTop (𝓝 m) := hqlim.comp hσ.tendsto_atTop
  rcases (angEnt_nonneg_STR02911 hGc hGn).lt_or_eq with hpos | hzero
  · -- Case A: positive entropy of the limit; the energy passage gives the quotient bound.
    have hHσ : Tendsto (fun n => angEnt_STR02911 h (gn (σ n))) atTop
        (𝓝 (angEnt_STR02911 h G)) := hHlim
    have hEσ : Tendsto (fun n => normInt_STR02904 (fun t => dn (σ n) t ^ 2 * qT_STR02904 h t))
        atTop (𝓝 (m * angEnt_STR02911 h G / 2)) := by
      have key : (fun n => normInt_STR02904 (fun t => dn (σ n) t ^ 2 * qT_STR02904 h t)) =
          fun n => qs (σ n) * angEnt_STR02911 h (gn (σ n)) / 2 := funext fun n => hEq (σ n)
      rw [key]
      exact (hqσ.mul hHσ).div_const 2
    have hliminf : liminf (fun n => normInt_STR02904 (fun t => dn n t ^ 2 * qT_STR02904 h t))
        atTop ≤ m * angEnt_STR02911 h G / 2 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hev := hEσ.eventually (Iio_mem_nhds
        (show m * angEnt_STR02911 h G / 2 < m * angEnt_STR02911 h G / 2 + ε by linarith))
      have hfreq : ∃ᶠ n in atTop, normInt_STR02904 (fun t => dn n t ^ 2 * qT_STR02904 h t) <
          m * angEnt_STR02911 h G / 2 + ε :=
        hσ.tendsto_atTop.frequently hev.frequently
      have hbdd : IsBoundedUnder (· ≥ ·) atTop
          (fun n => normInt_STR02904 (fun t => dn n t ^ 2 * qT_STR02904 h t)) :=
        Filter.isBoundedUnder_of ⟨0, fun n => normInt04_nonneg_STR02911 fun t =>
          mul_nonneg (sq_nonneg _) (qT_pos_STR02904 h t).le⟩
      exact liminf_le_of_frequently_le (hfreq.mono fun n hn => hn.le) hbdd
    have hdomG : angDom_STR02911 h G d := ⟨hG0, hd, hGn, hpos⟩
    have hEG : normInt_STR02904 (fun t => d t ^ 2 * qT_STR02904 h t) ≤
        m * angEnt_STR02911 h G / 2 :=
      (henergy d hd).trans hliminf
    have hquotle : angQuot_STR02911 h G d ≤ m := by
      unfold angQuot_STR02911
      rw [div_le_iff₀ (by linarith)]
      linarith
    exact ⟨G, d, hdomG, le_antisymm hquotle (hmle _ ⟨G, d, hdomG, rfl⟩)⟩
  · -- Case B: zero entropy of the limit forces `G = 1`, and then STR029.08 gives `m ≥ 1 - h²`.
    exfalso
    have hG1 := G_one_ae_STR02911 hGc hG0 hGn hzero.symm
    have hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        ∀ᵐ t ∂(volume.restrict (Ioc 0 (2 * π))), |gn (σ n) t - 1| ≤ δ := by
      intro δ hδ
      have hunif := Metric.tendstoUniformly_iff.mp hGu δ hδ
      filter_upwards [hunif] with n hn
      filter_upwards [(hF (σ n)).2.2, hG1] with t h1 h2
      have h3 := hn t
      rw [Real.dist_eq, h2] at h3
      rw [← h1, abs_sub_comm]
      exact h3.le
    have hpos8 : ∀ n, 0 < Hent_STR02908 h (gn (σ n)) := fun n => by
      unfold Hent_STR02908
      rw [normInt_eq_STR02935]
      exact (hdom (σ n)).2.2.2
    have h8 := str029_08_vanishing_entropy_endpoint hh (fun n => gn (σ n))
      (fun n => dn (σ n)) (fun n => (hdom (σ n)).2.1)
      (fun n => Filter.Eventually.of_forall fun t => (hdom (σ n)).1 t)
      (fun n => by rw [normInt_eq_STR02935]; exact (hdom (σ n)).2.2.1)
      hpos8 hconv
    have hfun : ∀ n, 4 * normInt_STR02933 (fun t => dn (σ n) t ^ 2 * qT_STR02904 h t) /
        (2 * Hent_STR02908 h (gn (σ n))) = qs (σ n) := by
      intro n
      have e1 : normInt_STR02933 (fun t => dn (σ n) t ^ 2 * qT_STR02904 h t) =
          normInt_STR02904 (fun t => dn (σ n) t ^ 2 * qT_STR02904 h t) :=
        normInt_eq_STR02935 _
      have e2 : Hent_STR02908 h (gn (σ n)) = angEnt_STR02911 h (gn (σ n)) :=
        normInt_eq_STR02935 _
      rw [e1, e2]
      exact (hqeq (σ n)).symm
    have hlim_eq : liminf (fun n => ((4 * normInt_STR02933
        (fun t => dn (σ n) t ^ 2 * qT_STR02904 h t) /
          (2 * Hent_STR02908 h (gn (σ n))) : ℝ) : EReal)) atTop =
        liminf (fun n => ((qs (σ n) : ℝ) : EReal)) atTop :=
      Filter.liminf_congr (Filter.Eventually.of_forall fun n =>
        congrArg (fun x : ℝ => (x : EReal)) (hfun n))
    have hlimit : Tendsto (fun n => ((qs (σ n) : ℝ) : EReal)) atTop (𝓝 (m : EReal)) :=
      EReal.tendsto_coe.mpr hqσ
    rw [hlim_eq, hlimit.liminf_eq] at h8
    exact (not_le.mpr hm_lt) (EReal.coe_le_coe_iff.mp h8)

/-- **STR029.11.** There is `0 < δ ≤ 1/1000` such that every real `h` with `0 < |h| < δ` has an
admissible pair `(G, d)` whose angular quotient is the infimum of the angular quotient set. -/
theorem str029_11_positive_entropy_attainment_angular_finite_information :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 1000 ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ →
        ∃ G d : ℝ → ℝ, angDom_STR02911 h G d ∧
          angQuot_STR02911 h G d = sInf (angSet_STR02911 h) := by
  obtain ⟨δ, hδ0, hδ1, hT⟩ := str029_10_strict_trial_below_endpoint
  refine ⟨δ, hδ0, hδ1, fun h hpos hlt => ?_⟩
  obtain ⟨hE, hQ⟩ := hT h hpos hlt
  have hh : |h| ≤ 1 / 1000 := le_trans hlt.le hδ1
  obtain ⟨G, d, hdom, hq⟩ := chart_witness_STR02911 (trialU_contDiff_STR02911 h)
    (trialU_periodic_STR02911 h) hE
  exact attain_core_STR02911 hh ⟨G, d, hdom, by rw [hq]; exact hQ⟩

end DGPS.Frontier.STR029
