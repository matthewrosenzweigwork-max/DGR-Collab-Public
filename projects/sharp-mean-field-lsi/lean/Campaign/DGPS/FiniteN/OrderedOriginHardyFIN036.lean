import DGPS.FiniteN.OrderedRadialNormalization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Ordered radial estimates at the unstable origin (FIN036)

The cumulative mass includes the radial Jacobian. The resistance is only used
between strictly positive endpoints. The shift is the same `radialU_orad` as in
FIN034 and FIN035.
-/

open MeasureTheory Set Filter
open scoped ENNReal Interval

namespace DGPS.FiniteN

noncomputable def orderedOriginMass_FIN036 (κ r0 N x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..x, r * Real.exp (-N * radialU_orad κ r0 r)

noncomputable def orderedOriginResistance_FIN036 (κ r0 N x : ℝ) : ℝ :=
  ∫ r in x..r0, Real.exp (N * radialU_orad κ r0 r) / r

noncomputable def orderedOriginProfile_FIN036 (u : ℝ) : ℝ :=
  if u ≤ 1 then 1 + Real.log (1 / u) else 1 / u

/-- Integration of the two derivative comparisons, with the exact half factors. -/
theorem orderedOrigin_potential_comparison_FIN036 {κ r0 c C x r : ℝ}
    (hx : 0 ≤ x) (hxa : x ≤ r0 / 2) (hr : r ∈ Icc 0 x)
    (hd : ∀ t ∈ Icc 0 (r0 / 2),
      c * t ≤ -radialDpsi_orad κ t ∧ -radialDpsi_orad κ t ≤ C * t) :
    c / 2 * (x ^ 2 - r ^ 2) ≤ radialU_orad κ r0 r - radialU_orad κ r0 x ∧
      radialU_orad κ r0 r - radialU_orad κ r0 x ≤ C / 2 * (x ^ 2 - r ^ 2) := by
  have hderiv (k t : ℝ) :
      HasDerivAt (fun z => radialU_orad κ r0 z + k / 2 * z ^ 2)
        (radialDpsi_orad κ t + k * t) t := by
    convert (radialU_hasDerivAt_orad r0 t).add
      ((hasDerivAt_pow 2 t).const_mul (k / 2)) using 1; ring
  have hl := antitoneOn_of_hasDerivAt_orad (convex_Icc 0 x) (hderiv c)
    (fun t ht => by have h := (hd t ⟨ht.1, ht.2.trans hxa⟩).1; linarith)
  have hu := monotoneOn_of_hasDerivAt_orad (convex_Icc 0 x) (hderiv C)
    (fun t ht => by have h := (hd t ⟨ht.1, ht.2.trans hxa⟩).2; linarith)
  have h1 := hl hr ⟨hx, le_rfl⟩ hr.2
  have h2 := hu hr ⟨hx, le_rfl⟩ hr.2
  dsimp only at h1 h2
  constructor <;> nlinarith

/-- The actual cumulative mass is integrable, including its endpoint at zero. -/
theorem orderedOriginMass_integrable_FIN036 (κ r0 N x : ℝ) :
    IntervalIntegrable (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) volume 0 x := by
  have hU : Continuous (radialU_orad κ r0) :=
    continuous_iff_continuousAt.mpr fun r => (radialU_hasDerivAt_orad r0 r).continuousAt
  exact (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul hU))).intervalIntegrable 0 x

/-- Both actual integrals are strictly positive at every allowed endpoint. -/
theorem orderedOrigin_integrals_pos_FIN036 {κ r0 N x : ℝ}
    (hx : 0 < x) (hxr : x < r0) :
    0 < orderedOriginMass_FIN036 κ r0 N x ∧
      0 < orderedOriginResistance_FIN036 κ r0 N x := by
  constructor
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (orderedOriginMass_integrable_FIN036 κ r0 N x)
      (fun r hr => mul_pos hr.1 (Real.exp_pos _)) hx
  · exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (orderedResistance_integrable_FIN035 (hx.trans hxr) hx).symm
      (fun r hr => div_pos (Real.exp_pos _) (hx.trans hr.1)) hxr

/-- The model exponential integral used for both comparisons of the actual mass. -/
theorem orderedOrigin_model_integral_FIN036 {k N x : ℝ} (hk : 0 < k) (hN : 0 < N) :
    (∫ r in (0 : ℝ)..x, r * Real.exp (-(N * k / 2) * (x ^ 2 - r ^ 2))) =
      (1 - Real.exp (-(N * k / 2) * x ^ 2)) / (N * k) := by
  have hkN : N * k ≠ 0 := (mul_pos hN hk).ne'
  have hd (r : ℝ) :
      HasDerivAt (fun t => Real.exp (-(N * k / 2) * (x ^ 2 - t ^ 2)) / (N * k))
        (r * Real.exp (-(N * k / 2) * (x ^ 2 - r ^ 2))) r := by
    have h := (((hasDerivAt_pow 2 r).const_sub (x ^ 2)).const_mul
      (-(N * k / 2))).exp.div_const (N * k)
    convert h using 1
    field_simp
    ring
  have hi : IntervalIntegrable
      (fun r : ℝ => r * Real.exp (-(N * k / 2) * (x ^ 2 - r ^ 2))) volume 0 x := by
    exact (by fun_prop : Continuous (fun r : ℝ =>
      r * Real.exp (-(N * k / 2) * (x ^ 2 - r ^ 2)))).intervalIntegrable 0 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
  simp only [sub_self, mul_zero, Real.exp_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
  ring

/-- The exact elementary exponential brackets, before replacing them by min(Nx²,1). -/
theorem orderedOriginMass_exponential_bounds_FIN036 {κ r0 c C N x : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hN : 0 < N) (hx : 0 ≤ x) (hxa : x ≤ r0 / 2)
    (hd : ∀ t ∈ Icc 0 (r0 / 2),
      c * t ≤ -radialDpsi_orad κ t ∧ -radialDpsi_orad κ t ≤ C * t) :
    Real.exp (-N * radialU_orad κ r0 x) *
        ((1 - Real.exp (-(N * C / 2) * x ^ 2)) / (N * C)) ≤
      orderedOriginMass_FIN036 κ r0 N x ∧
    orderedOriginMass_FIN036 κ r0 N x ≤
      Real.exp (-N * radialU_orad κ r0 x) *
        ((1 - Real.exp (-(N * c / 2) * x ^ 2)) / (N * c)) := by
  have hi := orderedOriginMass_integrable_FIN036 κ r0 N x
  have hcont (k : ℝ) : Continuous (fun r : ℝ =>
      Real.exp (-N * radialU_orad κ r0 x) *
        (r * Real.exp (-(N * k / 2) * (x ^ 2 - r ^ 2)))) := by fun_prop
  have hmodel (k : ℝ) (hk : 0 < k) :
      (∫ r in (0 : ℝ)..x, Real.exp (-N * radialU_orad κ r0 x) *
        (r * Real.exp (-(N * k / 2) * (x ^ 2 - r ^ 2)))) =
      Real.exp (-N * radialU_orad κ r0 x) *
        ((1 - Real.exp (-(N * k / 2) * x ^ 2)) / (N * k)) := by
    rw [intervalIntegral.integral_const_mul, orderedOrigin_model_integral_FIN036 hk hN]
  have hp (r : ℝ) (hr : r ∈ Icc 0 x) :=
    orderedOrigin_potential_comparison_FIN036 hx hxa hr hd
  constructor
  · rw [← hmodel C hC]
    apply intervalIntegral.integral_mono_on hx ((hcont C).intervalIntegrable 0 x) hi
    intro r hr
    rw [mul_comm (Real.exp _) (r * _), mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hr.1
    have h := mul_le_mul_of_nonneg_left (hp r hr).2 hN.le
    nlinarith
  · rw [← hmodel c hc]
    apply intervalIntegral.integral_mono_on hx hi ((hcont c).intervalIntegrable 0 x)
    intro r hr
    rw [mul_comm (Real.exp _) (r * _), mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hr.1
    have h := mul_le_mul_of_nonneg_left (hp r hr).1 hN.le
    nlinarith

/-- Equality with the raw half-line mass, with no change to the density at zero. -/
theorem orderedOriginMass_eq_raw_FIN036 {κ r0 N x : ℝ} (hx : 0 ≤ x) :
    orderedOriginMass_FIN036 κ r0 N x =
      ∫ r in Iic x, orderedRadialWeight_FIN035 κ r0 N r := by
  rw [orderedOriginMass_FIN036, intervalIntegral.integral_of_le hx]
  have he : (Iic x).indicator (orderedRadialWeight_FIN035 κ r0 N) =
      (Ioc 0 x).indicator (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) := by
    ext r
    by_cases hr : 0 < r
    · by_cases hrx : r ≤ x <;> simp [orderedRadialWeight_FIN035, hr, hrx]
    · have hn : ¬ (0 < r ∧ r ≤ x) := fun h => hr h.1
      simp [orderedRadialWeight_FIN035, hr]
  rw [← integral_indicator measurableSet_Iic, he, integral_indicator measurableSet_Ioc]

/-- Exact normalized mass and the normalized-density resistance cancel Z. -/
theorem orderedOrigin_normalization_FIN036 {κ r0 N x : ℝ} (hx : 0 ≤ x)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    (orderedRadialLaw_FIN035 κ r0 N).real (Iic x) =
        orderedOriginMass_FIN036 κ r0 N x / orderedRadialZ_FIN035 κ r0 N ∧
    (orderedRadialLaw_FIN035 κ r0 N).real (Iic x) *
        (orderedRadialZ_FIN035 κ r0 N * orderedOriginResistance_FIN036 κ r0 N x) =
      orderedOriginMass_FIN036 κ r0 N x * orderedOriginResistance_FIN036 κ r0 N x := by
  have he : (orderedRadialLaw_FIN035 κ r0 N).real (Iic x) =
      orderedOriginMass_FIN036 κ r0 N x / orderedRadialZ_FIN035 κ r0 N := by
    rw [orderedRadialLaw_mass_FIN035 hi hZ measurableSet_Iic,
      orderedOriginMass_eq_raw_FIN036 hx]
  refine ⟨he, ?_⟩
  rw [he]
  field_simp



/-- Uniform scalar comparison behind the min(Nx²,1) mass estimate. -/
theorem orderedOrigin_exp_min_FIN036 {k u : ℝ} (hk : 0 < k) (hu : 0 ≤ u) :
    (Real.exp (-k / 2) / 2) * min u 1 ≤
        (1 - Real.exp (-(k / 2) * u)) / k ∧
    (1 - Real.exp (-(k / 2) * u)) / k ≤
        ((1 + k / 2) / k) * min u 1 := by
  have ht : 0 ≤ k / 2 * u := mul_nonneg (by positivity) hu
  have hepos := Real.exp_pos (-(k / 2) * u)
  have heprod : Real.exp (k / 2 * u) * Real.exp (-(k / 2) * u) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2; ring
  have hl : (k / 2 * u) * Real.exp (-(k / 2) * u) ≤
      1 - Real.exp (-(k / 2) * u) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (k / 2 * u)) hepos.le
    rw [heprod] at h
    nlinarith
  have hupper : 1 - Real.exp (-(k / 2) * u) ≤ k / 2 * u := by
    have h := Real.add_one_le_exp (-(k / 2) * u)
    linarith
  have hupper1 : 1 - Real.exp (-(k / 2) * u) ≤ 1 := by linarith
  by_cases hu1 : u ≤ 1
  · rw [min_eq_left hu1]
    have he : Real.exp (-k / 2) ≤ Real.exp (-(k / 2) * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hlow := mul_le_mul_of_nonneg_left he ht
    constructor
    · apply (le_div_iff₀ hk).2
      nlinarith
    · apply (div_le_iff₀ hk).2
      have hcancel : ((1 + k / 2) / k * u) * k = (1 + k / 2) * u := by
        field_simp
      rw [hcancel]
      nlinarith
  · have h1u : 1 ≤ u := (lt_of_not_ge hu1).le
    rw [min_eq_right h1u]
    have he : Real.exp (-(k / 2) * u) ≤ Real.exp (-k / 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hone : k / 2 * Real.exp (-k / 2) ≤ 1 - Real.exp (-k / 2) := by
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (k / 2))
        (Real.exp_pos (-k / 2)).le
      have hp : Real.exp (k / 2) * Real.exp (-k / 2) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 2; ring
      rw [hp] at h
      nlinarith
    constructor
    · apply (le_div_iff₀ hk).2
      nlinarith
    · simp only [mul_one]
      apply div_le_div_of_nonneg_right _ hk.le
      linarith

/-- The actual mass has the exact source scale, uniformly for positive N and x. -/
theorem orderedOriginMass_min_bounds_FIN036 {κ r0 c C N x : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hN : 0 < N) (hx : 0 ≤ x) (hxa : x ≤ r0 / 2)
    (hd : ∀ t ∈ Icc 0 (r0 / 2),
      c * t ≤ -radialDpsi_orad κ t ∧ -radialDpsi_orad κ t ≤ C * t) :
    (Real.exp (-C / 2) / 2) *
        (Real.exp (-N * radialU_orad κ r0 x) / N * min (N * x ^ 2) 1) ≤
      orderedOriginMass_FIN036 κ r0 N x ∧
    orderedOriginMass_FIN036 κ r0 N x ≤
      ((1 + c / 2) / c) *
        (Real.exp (-N * radialU_orad κ r0 x) / N * min (N * x ^ 2) 1) := by
  have hb := orderedOriginMass_exponential_bounds_FIN036 hc hC hN hx hxa hd
  have hu : 0 ≤ N * x ^ 2 := mul_nonneg hN.le (sq_nonneg x)
  have hl := (orderedOrigin_exp_min_FIN036 hC hu).1
  have hh := (orderedOrigin_exp_min_FIN036 hc hu).2
  have hfactor : 0 ≤ Real.exp (-N * radialU_orad κ r0 x) / N := by positivity
  have heq (k : ℝ) :
      Real.exp (-N * radialU_orad κ r0 x) *
          ((1 - Real.exp (-(N * k / 2) * x ^ 2)) / (N * k)) =
        (Real.exp (-N * radialU_orad κ r0 x) / N) *
          ((1 - Real.exp (-(k / 2) * (N * x ^ 2))) / k) := by
    have hexp : -(N * k / 2) * x ^ 2 = -(k / 2) * (N * x ^ 2) := by ring
    rw [hexp]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  constructor
  · have h := mul_le_mul_of_nonneg_left hl hfactor
    calc
      _ = (Real.exp (-N * radialU_orad κ r0 x) / N) *
          ((Real.exp (-C / 2) / 2) * min (N * x ^ 2) 1) := by ring
      _ ≤ _ := h
      _ = _ := (heq C).symm
      _ ≤ _ := hb.1
  · calc
      _ ≤ _ := hb.2
      _ = _ := heq c
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hfactor
      _ = _ := by ring

/-- Resistance for the actual normalized density is exactly Z times raw resistance. -/
theorem orderedOrigin_normalized_resistance_FIN036 {κ r0 N x : ℝ}
    (hx : 0 < x) (hxr : x ≤ r0)
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N)) =
      orderedRadialZ_FIN035 κ r0 N * orderedOriginResistance_FIN036 κ r0 N x := by
  rw [orderedOriginResistance_FIN036, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrpos : 0 < r := hx.trans_le ((uIcc_of_le hxr ▸ hr).1)
  simp only [orderedRadialWeight_FIN035, ite_eq_left hrpos]
  have he : Real.exp (-(N * radialU_orad κ r0 r)) *
      Real.exp (N * radialU_orad κ r0 r) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2; ring
  field_simp
  linarith


/-- The origin comparison extends to r0 when the left endpoint is at most r0/2. -/
theorem orderedOrigin_global_drop_FIN036 {κ r0 c x r : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hx : 0 ≤ x) (hxa : x ≤ r0 / 2)
    (hxr : x ≤ r) (hrr : r ≤ r0)
    (hnear : ∀ t ∈ Icc 0 (r0 / 2), radialDpsi_orad κ t ≤ -c * t)
    (hfar : ∀ t ∈ Icc (r0 / 2) r0,
      radialDpsi_orad κ t ≤ -c * (r0 - t)) :
    c / 6 * (r ^ 2 - x ^ 2) ≤ radialU_orad κ r0 x - radialU_orad κ r0 r := by
  have ha : 0 ≤ r0 / 2 := by positivity
  have hderiv (t : ℝ) :
      HasDerivAt (fun z => radialU_orad κ r0 z + c / 2 * z ^ 2)
        (radialDpsi_orad κ t + c * t) t := by
    convert (radialU_hasDerivAt_orad r0 t).add
      ((hasDerivAt_pow 2 t).const_mul (c / 2)) using 1; ring
  have hn := antitoneOn_of_hasDerivAt_orad (convex_Icc 0 (r0 / 2))
    hderiv (fun t ht => by have h := hnear t ht; linarith)
  by_cases hra : r ≤ r0 / 2
  · have h := hn ⟨hx, hxa⟩ ⟨hx.trans hxr, hra⟩ hxr
    have hsq : 0 ≤ r ^ 2 - x ^ 2 := by nlinarith
    have hp := mul_nonneg hc.le hsq
    dsimp only at h
    nlinarith
  · have har : r0 / 2 ≤ r := (lt_of_not_ge hra).le
    have hf := antitoneOn_of_hasDerivAt_orad (convex_Icc (r0 / 2) r0)
      (radialU_sub_quad_hasDerivAt_orad (κ := κ) r0 (c / 2))
      (fun t ht => by have h := hfar t ht; linarith)
    have h1 := hn ⟨hx, hxa⟩ ⟨ha, le_rfl⟩ hxa
    have h2 := hf ⟨le_rfl, by linarith⟩ ⟨har, hrr⟩ har
    have hsq : 0 ≤ (r0 / 2) ^ 2 - x ^ 2 := by nlinarith
    have hp1 := mul_nonneg hc.le hsq
    have hp2 := mul_nonneg hc.le (mul_nonneg (sub_nonneg.mpr har) (sub_nonneg.mpr hrr))
    dsimp only at h1 h2
    nlinarith

/-- The decreasing Gaussian model has a finite elementary integral on positive intervals. -/
theorem orderedOrigin_decreasing_model_FIN036 {k N x y : ℝ}
    (hk : 0 < k) (hN : 0 < N) :
    (∫ r in x..y, r * Real.exp (-(N * k / 2) * (r ^ 2 - x ^ 2))) =
      (1 - Real.exp (-(N * k / 2) * (y ^ 2 - x ^ 2))) / (N * k) := by
  have hkN : N * k ≠ 0 := (mul_pos hN hk).ne'
  have hd (r : ℝ) :
      HasDerivAt (fun t => -Real.exp (-(N * k / 2) * (t ^ 2 - x ^ 2)) / (N * k))
        (r * Real.exp (-(N * k / 2) * (r ^ 2 - x ^ 2))) r := by
    have h := (((hasDerivAt_pow 2 r).sub_const (x ^ 2)).const_mul
      (-(N * k / 2))).exp.neg.div_const (N * k)
    convert h using 1
    field_simp
    ring
  have hi : IntervalIntegrable
      (fun r : ℝ => r * Real.exp (-(N * k / 2) * (r ^ 2 - x ^ 2))) volume x y :=
    (by fun_prop : Continuous (fun r : ℝ =>
      r * Real.exp (-(N * k / 2) * (r ^ 2 - x ^ 2)))).intervalIntegrable x y
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring


/-- A quantitative resistance bound for a left endpoint in the origin region. -/
theorem orderedOriginResistance_large_bound_FIN036 {κ r0 k N x : ℝ}
    (hk : 0 < k) (hN : 0 < N) (hx : 0 < x) (hxr : x ≤ r0)
    (hdrop : ∀ r ∈ Icc x r0, k / 2 * (r ^ 2 - x ^ 2) ≤
      radialU_orad κ r0 x - radialU_orad κ r0 r) :
    orderedOriginResistance_FIN036 κ r0 N x ≤
      Real.exp (N * radialU_orad κ r0 x) / (k * (N * x ^ 2)) := by
  have hr0 : 0 < r0 := hx.trans_le hxr
  have hxsq : 0 < x ^ 2 := sq_pos_of_pos hx
  have hcont : Continuous (fun r : ℝ =>
      (Real.exp (N * radialU_orad κ r0 x) / x ^ 2) *
        (r * Real.exp (-(N * k / 2) * (r ^ 2 - x ^ 2)))) := by fun_prop
  have hI : orderedOriginResistance_FIN036 κ r0 N x ≤
      ∫ r in x..r0, (Real.exp (N * radialU_orad κ r0 x) / x ^ 2) *
        (r * Real.exp (-(N * k / 2) * (r ^ 2 - x ^ 2))) := by
    apply intervalIntegral.integral_mono_on hxr
      (orderedResistance_integrable_FIN035 hr0 hx).symm (hcont.intervalIntegrable x r0)
    intro r hr
    have hrpos : 0 < r := hx.trans_le hr.1
    have he : Real.exp (N * radialU_orad κ r0 r) ≤
        Real.exp (N * radialU_orad κ r0 x) *
          Real.exp (-(N * k / 2) * (r ^ 2 - x ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (hdrop r hr) hN.le
      nlinarith
    have hs : x ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hx.le hr.1 2
    apply (div_le_iff₀ hrpos).2
    have h1 := mul_le_mul_of_nonneg_right he hxsq.le
    have h2 := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (Real.exp_pos (N * radialU_orad κ r0 x)).le
        (Real.exp_pos (-(N * k / 2) * (r ^ 2 - x ^ 2))).le)
    have hh := (le_div_iff₀ hxsq).2 (h1.trans h2)
    convert hh using 1; ring
  rw [intervalIntegral.integral_const_mul,
    orderedOrigin_decreasing_model_FIN036 hk hN] at hI
  have hfrac : (1 - Real.exp (-(N * k / 2) * (r0 ^ 2 - x ^ 2))) / (N * k) ≤
      1 / (N * k) := div_le_div_of_nonneg_right
    (by have := Real.exp_pos (-(N * k / 2) * (r0 ^ 2 - x ^ 2)); linarith) (by positivity)
  calc
    _ ≤ _ := hI
    _ ≤ (Real.exp (N * radialU_orad κ r0 x) / x ^ 2) * (1 / (N * k)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The resistance integrand is integrable between any two positive endpoints. -/
theorem orderedOriginResistance_integrable_gen_FIN036 {κ r0 N x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fun r => Real.exp (N * radialU_orad κ r0 r) / r) volume x y := by
  have hU : Continuous (radialU_orad κ r0) :=
    continuous_iff_continuousAt.mpr fun r => (radialU_hasDerivAt_orad r0 r).continuousAt
  have hpos : ∀ r ∈ uIcc x y, r ≠ 0 := by
    intro r hr
    exact ((lt_min hx hy).trans_le hr.1).ne'
  exact ((Real.continuous_exp.comp (continuous_const.mul hU)).continuousOn.div
    continuousOn_id hpos).intervalIntegrable

/-- On a positive interval the monotonic-potential bound has precisely a logarithm. -/
theorem orderedOriginResistance_log_bound_FIN036 {κ r0 N x y : ℝ}
    (hN : 0 ≤ N) (hx : 0 < x) (hxy : x ≤ y)
    (hU : ∀ r ∈ Icc x y, radialU_orad κ r0 r ≤ radialU_orad κ r0 x) :
    (∫ r in x..y, Real.exp (N * radialU_orad κ r0 r) / r) ≤
      Real.exp (N * radialU_orad κ r0 x) * Real.log (y / x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hi : IntervalIntegrable (fun r : ℝ => 1 / r) volume x y := by
    apply (continuousOn_const.div continuousOn_id _).intervalIntegrable
    intro r hr
    rw [uIcc_of_le hxy] at hr
    exact (hx.trans_le hr.1).ne'
  rw [← integral_one_div_of_pos hx hy, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hxy
    (orderedOriginResistance_integrable_gen_FIN036 hx hy) (hi.const_mul _)
  intro r hr
  have hrpos := hx.trans_le hr.1
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hU r hr) hN)
  simpa only [mul_one_div] using div_le_div_of_nonneg_right he hrpos.le


/-- The logarithmic singularity is cancelled by the radial mass scale. -/
theorem orderedOrigin_log_cancellation_FIN036 {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    u * (1 + Real.log (1 / u)) ^ 2 ≤ 4 := by
  let t := Real.log (1 / u)
  have ht : 0 ≤ t := Real.log_nonneg (by
    apply (le_div_iff₀ hu).2
    simpa using hu1)
  have hp := Real.exp_pos (t / 2)
  have h1 : 1 + t ≤ 2 * Real.exp (t / 2) := by
    have := Real.add_one_le_exp (t / 2)
    linarith
  have he : Real.exp (t / 2) ^ 2 = 1 / u := by
    rw [pow_two, ← Real.exp_add]
    have heq : t / 2 + t / 2 = t := by ring
    rw [heq, Real.exp_log (div_pos zero_lt_one hu)]
  have hs : (1 + t) ^ 2 ≤ 4 / u := by
    have h := mul_le_mul h1 h1 (by linarith : 0 ≤ 1 + t) (by positivity)
    calc (1 + t) ^ 2 = (1 + t) * (1 + t) := sq _
      _ ≤ 2 * Real.exp (t / 2) * (2 * Real.exp (t / 2)) := h
      _ = 4 * Real.exp (t / 2) ^ 2 := by ring
      _ = 4 / u := by rw [he]; ring
  have h := mul_le_mul_of_nonneg_left hs hu.le
  have hc : u * (4 / u) = 4 := by field_simp
  rw [hc] at h
  exact h

/-- The cancellation is uniform also in the particle number in the small-u regime. -/
theorem orderedOrigin_small_profile_bound_FIN036 {u N K : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hN : 1 ≤ N) (hK : 0 ≤ K) :
    (min u 1 * orderedOriginProfile_FIN036 u / N) *
        (K * N + Real.log (1 / u)) ≤ 4 * (K + 1) := by
  have hN0 : 0 < N := by linarith
  have ht : 0 ≤ Real.log (1 / u) := Real.log_nonneg (by
    apply (le_div_iff₀ hu).2
    simpa using hu1)
  have hprof : orderedOriginProfile_FIN036 u = 1 + Real.log (1 / u) := by
    unfold orderedOriginProfile_FIN036
    simp [hu1]
  rw [min_eq_left hu1, hprof]
  have h1 : K * N + Real.log (1 / u) ≤
      N * ((K + 1) * (1 + Real.log (1 / u))) := by
    have hnt := mul_nonneg (sub_nonneg.mpr hN) ht
    have hkt := mul_nonneg hK ht
    have hNkt := mul_nonneg hN0.le hkt
    nlinarith
  calc
    _ ≤ (u * (1 + Real.log (1 / u)) / N) *
        (N * ((K + 1) * (1 + Real.log (1 / u)))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (u * (1 + Real.log (1 / u)) ^ 2) * (K + 1) := by field_simp
    _ ≤ 4 * (K + 1) := mul_le_mul_of_nonneg_right
      (orderedOrigin_log_cancellation_FIN036 hu hu1) (by linarith)




/-- The exact source resistance profile, after one split at N^(-1/2). -/
theorem orderedOriginResistance_profile_FIN036 {κ r0 a k N x : ℝ}
    (hk : 0 < k) (hN : 0 < N) (ha : 0 < a) (har : a < r0)
    (hscale : 1 / Real.sqrt N ≤ a) (hx : 0 < x) (hxa : x ≤ a)
    (hdrop : ∀ y ∈ Ioc 0 a, ∀ r ∈ Icc y r0,
      k / 2 * (r ^ 2 - y ^ 2) ≤ radialU_orad κ r0 y - radialU_orad κ r0 r) :
    orderedOriginResistance_FIN036 κ r0 N x ≤
      (1 + 1 / k) * Real.exp (N * radialU_orad κ r0 x) *
        orderedOriginProfile_FIN036 (N * x ^ 2) := by
  have hr0 : 0 < r0 := ha.trans har
  have hxr : x ≤ r0 := hxa.trans har.le
  have hu : 0 < N * x ^ 2 := mul_pos hN (sq_pos_of_pos hx)
  by_cases hu1 : N * x ^ 2 ≤ 1
  · obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = 1 / Real.sqrt N := ⟨_, rfl⟩
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    have hz : 0 < z := by rw [hzdef]; exact div_pos zero_lt_one hs
    have hza : z ≤ a := by rw [hzdef]; exact hscale
    have hzr : z ≤ r0 := hza.trans har.le
    have hNz : N * z ^ 2 = 1 := by
      rw [hzdef, div_pow, one_pow, Real.sq_sqrt hN.le]
      field_simp
    have hxz : x ≤ z := by
      have hsq : (x * Real.sqrt N) ^ 2 = N * x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hN.le]; ring
      have hprod : 0 ≤ x * Real.sqrt N := mul_nonneg hx.le hs.le
      have hbound : x * Real.sqrt N ≤ 1 := by nlinarith
      rw [hzdef]
      exact (le_div_iff₀ hs).2 hbound
    have hUx (r : ℝ) (hr : r ∈ Icc x r0) :
        radialU_orad κ r0 r ≤ radialU_orad κ r0 x := by
      have h := hdrop x ⟨hx, hxa⟩ r hr
      have hsq : 0 ≤ r ^ 2 - x ^ 2 := by nlinarith [hr.1]
      have hpos := mul_nonneg (by positivity : 0 ≤ k / 2) hsq
      linarith
    have hlog := orderedOriginResistance_log_bound_FIN036 hN.le hx hxz
      (fun r hr => hUx r ⟨hr.1, hr.2.trans hzr⟩)
    have htail := orderedOriginResistance_large_bound_FIN036 hk hN hz hzr
      (hdrop z ⟨hz, hza⟩)
    rw [hNz, mul_one] at htail
    have he : Real.exp (N * radialU_orad κ r0 z) ≤
        Real.exp (N * radialU_orad κ r0 x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hUx z ⟨hxz, hzr⟩) hN.le)
    have htail' : orderedOriginResistance_FIN036 κ r0 N z ≤
        Real.exp (N * radialU_orad κ r0 x) / k :=
      htail.trans (div_le_div_of_nonneg_right he hk.le)
    have hsplit :
        orderedOriginResistance_FIN036 κ r0 N x =
          (∫ r in x..z, Real.exp (N * radialU_orad κ r0 r) / r) +
            orderedOriginResistance_FIN036 κ r0 N z := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (orderedOriginResistance_integrable_gen_FIN036 hx hz)
        (orderedOriginResistance_integrable_gen_FIN036 hz hr0)).symm
    have hlogeq : Real.log (z / x) = Real.log (1 / (N * x ^ 2)) / 2 := by
      have h1 : Real.log (z / x) = -(Real.log N) / 2 - Real.log x := by
        rw [hzdef, Real.log_div (by positivity) hx.ne', one_div, Real.log_inv,
          Real.log_sqrt hN.le]
        ring
      have h2 : Real.log (1 / (N * x ^ 2)) = -Real.log N - 2 * Real.log x := by
        rw [one_div, Real.log_inv, Real.log_mul hN.ne' (pow_ne_zero 2 hx.ne'),
          Real.log_pow]
        push_cast
        ring
      rw [h1, h2]
      ring
    have ht : 0 ≤ Real.log (1 / (N * x ^ 2)) := Real.log_nonneg
      ((le_div_iff₀ hu).2 (by simpa using hu1))
    have hprof : orderedOriginProfile_FIN036 (N * x ^ 2) =
        1 + Real.log (1 / (N * x ^ 2)) := by
      unfold orderedOriginProfile_FIN036
      simp [hu1]
    rw [hsplit, hprof]
    have hsum := add_le_add hlog htail'
    rw [hlogeq] at hsum
    have hkt : 0 ≤ 1 / k * Real.log (1 / (N * x ^ 2)) :=
      mul_nonneg (by positivity) ht
    have hE := Real.exp_pos (N * radialU_orad κ r0 x)
    have hb : Real.log (1 / (N * x ^ 2)) / 2 + 1 / k ≤
        (1 + 1 / k) * (1 + Real.log (1 / (N * x ^ 2))) := by
      nlinarith
    have hfinal := mul_le_mul_of_nonneg_left hb hE.le
    calc
      _ ≤ _ := hsum
      _ = Real.exp (N * radialU_orad κ r0 x) *
          (Real.log (1 / (N * x ^ 2)) / 2 + 1 / k) := by ring
      _ ≤ _ := hfinal
      _ = _ := by ring
  · have hlarge := orderedOriginResistance_large_bound_FIN036 hk hN hx hxr
      (hdrop x ⟨hx, hxa⟩)
    have hprof : orderedOriginProfile_FIN036 (N * x ^ 2) = 1 / (N * x ^ 2) := by
      unfold orderedOriginProfile_FIN036
      simp [hu1]
    rw [hprof]
    calc
      _ ≤ _ := hlarge
      _ = (1 / k) * Real.exp (N * radialU_orad κ r0 x) * (1 / (N * x ^ 2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith : 1 / k ≤ 1 + 1 / k)
          (Real.exp_pos _).le


/-- Converting the proved mass lower bound into the source logarithmic estimate. -/
theorem orderedOrigin_log_bound_FIN036 {N U V A B L Z u : ℝ}
    (hN : 1 ≤ N) (hV : 0 ≤ V) (hUV : U ≤ V)
    (hA : 0 < A) (hB : 0 < B) (hL : 0 < L) (hZ : 0 ≤ Z) (hZB : Z ≤ B)
    (hu : 0 < u)
    (hlow : A * (Real.exp (-N * U) / N * min u 1) ≤ L) :
    Real.log (1 + Z / L) ≤
      (1 + V + Real.log (1 + B / A)) * N + max 0 (Real.log (1 / u)) := by
  have hN0 : 0 < N := by linarith
  let m := min u 1
  have hm : 0 < m := lt_min hu zero_lt_one
  have hm1 : m ≤ 1 := min_le_right _ _
  let d := A * (Real.exp (-N * U) / N * m)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdl : d ≤ L := hlow
  have hq : B / d = (B / A) * N * Real.exp (N * U) / m := by
    dsimp [d]
    rw [show -N * U = -(N * U) by ring, Real.exp_neg]
    have hE := (Real.exp_pos (N * U)).ne'
    field_simp
  have hfrac : Z / L ≤ (B / A) * N * Real.exp (N * U) / m := by
    calc
      Z / L ≤ B / L := div_le_div_of_nonneg_right hZB hL.le
      _ ≤ B / d := div_le_div_of_nonneg_left hB.le hd hdl
      _ = _ := hq
  let E := Real.exp ((1 + V) * N)
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg (by linarith) hN0.le)
  have hprod : N * Real.exp (N * U) ≤ E := by
    have hn : N ≤ Real.exp N := by have := Real.add_one_le_exp N; linarith
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hUV hN0.le)
    have h := mul_le_mul hn he (Real.exp_pos _).le (Real.exp_pos _).le
    calc
      _ ≤ Real.exp N * Real.exp (N * V) := h
      _ = E := by
        dsimp [E]
        rw [← Real.exp_add]
        congr 1
        ring
  have hfrac' : Z / L ≤ (B / A) * E / m := by
    apply hfrac.trans
    apply div_le_div_of_nonneg_right _ hm.le
    have h := mul_le_mul_of_nonneg_left hprod (div_nonneg hB.le hA.le)
    nlinarith
  have hone : 1 ≤ E / m := (le_div_iff₀ hm).2 (by rw [one_mul]; exact hm1.trans hE)
  have hwhole : 1 + Z / L ≤ (1 + B / A) * E / m := by
    exact (add_le_add hone hfrac').trans_eq (by ring)
  have hleft : 0 < 1 + Z / L := by positivity
  have hco : 0 < 1 + B / A := by positivity
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hlog := Real.log_le_log hleft hwhole
  rw [Real.log_div (mul_ne_zero hco.ne' hE0.ne') hm.ne',
    Real.log_mul hco.ne' hE0.ne'] at hlog
  have hlogE : Real.log E = (1 + V) * N := Real.log_exp _
  rw [hlogE] at hlog
  have hlogm : -Real.log m = max 0 (Real.log (1 / u)) := by
    by_cases hu1 : u ≤ 1
    · have ht : 0 ≤ Real.log (1 / u) := Real.log_nonneg
        ((le_div_iff₀ hu).2 (by simpa using hu1))
      dsimp [m]
      rw [min_eq_left hu1, max_eq_right ht, Real.log_div one_ne_zero hu.ne', Real.log_one]
      ring
    · have h1u : 1 ≤ u := (lt_of_not_ge hu1).le
      have ht : Real.log (1 / u) ≤ 0 := Real.log_nonpos (by positivity)
        ((div_le_iff₀ hu).2 (by simpa using h1u))
      dsimp [m]
      rw [min_eq_right h1u, Real.log_one, neg_zero, max_eq_left ht]
  have hclog : 0 ≤ Real.log (1 + B / A) := Real.log_nonneg (by
    have := div_nonneg hB.le hA.le
    linarith)
  have hcn := mul_nonneg (sub_nonneg.mpr hN) hclog
  rw [sub_eq_add_neg, hlogm] at hlog
  nlinarith


theorem orderedOrigin_profile_bound_FIN036 {u N K : ℝ}
    (hu : 0 < u) (hN : 1 ≤ N) (hK : 0 ≤ K) :
    (min u 1 * orderedOriginProfile_FIN036 u / N) *
        (K * N + max 0 (Real.log (1 / u))) ≤ 4 * (K + 1) := by
  by_cases hu1 : u ≤ 1
  · have ht : 0 ≤ Real.log (1 / u) := Real.log_nonneg
      ((le_div_iff₀ hu).2 (by simpa using hu1))
    rw [max_eq_right ht]
    exact orderedOrigin_small_profile_bound_FIN036 hu hu1 hN hK
  · have h1u : 1 ≤ u := (lt_of_not_ge hu1).le
    have ht : Real.log (1 / u) ≤ 0 := Real.log_nonpos (by positivity)
      ((div_le_iff₀ hu).2 (by simpa using h1u))
    have hprof : orderedOriginProfile_FIN036 u = 1 / u := by
      unfold orderedOriginProfile_FIN036
      simp [hu1]
    rw [min_eq_right h1u, hprof, max_eq_left ht]
    have hN0 : N ≠ 0 := by linarith
    have heq : (1 * (1 / u) / N) * (K * N + 0) = K / u := by
      field_simp
      ring
    rw [heq]
    have hKu : K / u ≤ K := (div_le_iff₀ hu).2 (by nlinarith)
    linarith

/-- Scalar assembly of the proved source estimates. -/
theorem orderedOrigin_product_from_estimates_FIN036 {N U u L J Z A D K : ℝ}
    (hN : 1 ≤ N) (hu : 0 < u) (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hJ : 0 ≤ J) (hZ : 0 ≤ Z)
    (hmass : L ≤ A * (Real.exp (-N * U) / N * min u 1))
    (hres : J ≤ D * Real.exp (N * U) * orderedOriginProfile_FIN036 u)
    (hlog : Real.log (1 + Z / L) ≤
      K * N + max 0 (Real.log (1 / u))) :
    L * J * Real.log (1 + Z / L) ≤ 4 * A * D * (K + 1) := by
  have hN0 : 0 < N := by linarith
  have hb : 0 ≤ orderedOriginProfile_FIN036 u := by
    unfold orderedOriginProfile_FIN036
    split_ifs with hu1
    · have ht : 0 ≤ Real.log (1 / u) := Real.log_nonneg
        ((le_div_iff₀ hu).2 (by simpa using hu1))
      linarith
    · positivity
  have hm : 0 ≤ min u 1 := le_min hu.le zero_le_one
  have hlow : 0 ≤ A * (Real.exp (-N * U) / N * min u 1) := by positivity
  have hprod := mul_le_mul hmass hres hJ hlow
  have he : Real.exp (-N * U) * Real.exp (N * U) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2; ring
  have heq :
      (A * (Real.exp (-N * U) / N * min u 1)) *
          (D * Real.exp (N * U) * orderedOriginProfile_FIN036 u) =
        A * D * (min u 1 * orderedOriginProfile_FIN036 u / N) := by
    calc
      _ = A * D * (min u 1 * orderedOriginProfile_FIN036 u / N) *
          (Real.exp (-N * U) * Real.exp (N * U)) := by ring
      _ = _ := by rw [he]; ring
  rw [heq] at hprod
  have hlog0 : 0 ≤ Real.log (1 + Z / L) := Real.log_nonneg (by
    have := div_nonneg hZ hL
    linarith)
  have hfactor : 0 ≤ A * D * (min u 1 * orderedOriginProfile_FIN036 u / N) := by positivity
  calc
    _ ≤ (A * D * (min u 1 * orderedOriginProfile_FIN036 u / N)) *
        Real.log (1 + Z / L) := mul_le_mul_of_nonneg_right hprod hlog0
    _ ≤ (A * D * (min u 1 * orderedOriginProfile_FIN036 u / N)) *
        (K * N + max 0 (Real.log (1 / u))) :=
      mul_le_mul_of_nonneg_left hlog hfactor
    _ = A * D * ((min u 1 * orderedOriginProfile_FIN036 u / N) *
        (K * N + max 0 (Real.log (1 / u)))) := by ring
    _ ≤ A * D * (4 * (K + 1)) := mul_le_mul_of_nonneg_left
      (orderedOrigin_profile_bound_FIN036 hu hN hK) (mul_nonneg hA hD)
    _ = _ := by ring


/-- A vanishing bound makes the origin cancellation explicit, beyond uniform boundedness. -/
theorem orderedOrigin_log_cancellation_vanishing_FIN036 {u : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) :
    u * (1 + Real.log (1 / u)) ^ 2 ≤ 16 * Real.sqrt u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hs1 : Real.sqrt u ≤ 1 := by
    have := Real.sqrt_le_sqrt hu1
    simpa using this
  have ht : 0 ≤ Real.log (1 / Real.sqrt u) := Real.log_nonneg
    ((le_div_iff₀ hs).2 (by simpa using hs1))
  have hlog : Real.log (1 / u) = 2 * Real.log (1 / Real.sqrt u) := by
    rw [Real.log_div one_ne_zero hu.ne', Real.log_div one_ne_zero hs.ne',
      Real.log_sqrt hu.le, Real.log_one]
    ring
  have hsq : (1 + Real.log (1 / u)) ^ 2 ≤
      4 * (1 + Real.log (1 / Real.sqrt u)) ^ 2 := by
    rw [hlog]
    nlinarith
  have h := orderedOrigin_log_cancellation_FIN036 hs hs1
  have hscaled := mul_le_mul_of_nonneg_left h hs.le
  have heq : Real.sqrt u * (Real.sqrt u *
      (1 + Real.log (1 / Real.sqrt u)) ^ 2) =
      u * (1 + Real.log (1 / Real.sqrt u)) ^ 2 := by
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt hu.le]
  rw [heq] at hscaled
  have hscaled' := mul_le_mul_of_nonneg_left hsq hu.le
  nlinarith


theorem orderedOrigin_reciprocal_value_FIN036 {κ r0 N r : ℝ}
    (hr : 0 < r) (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    1 / (orderedRadialWeight_FIN035 κ r0 N r / orderedRadialZ_FIN035 κ r0 N) =
      orderedRadialZ_FIN035 κ r0 N * (Real.exp (N * radialU_orad κ r0 r) / r) := by
  simp only [orderedRadialWeight_FIN035, ite_eq_left hr]
  rw [show -N * radialU_orad κ r0 r = -(N * radialU_orad κ r0 r) by ring,
    Real.exp_neg]
  field_simp [hr.ne', hZ.ne']

/-- Integrability of the reciprocal of the actual normalized density, before integration. -/
theorem orderedOrigin_reciprocal_integrable_FIN036 {κ r0 N x : ℝ}
    (hx : 0 < x) (hxr : x ≤ r0)
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    IntervalIntegrable (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 N r /
      orderedRadialZ_FIN035 κ r0 N)) volume x r0 := by
  have heq : EqOn (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 N r /
      orderedRadialZ_FIN035 κ r0 N))
      (fun r => orderedRadialZ_FIN035 κ r0 N *
        (Real.exp (N * radialU_orad κ r0 r) / r)) (Ι x r0) := by
    intro r hr
    have hr' := uIoc_subset_uIcc hr
    rw [uIcc_of_le hxr] at hr'
    exact orderedOrigin_reciprocal_value_FIN036 (hx.trans_le hr'.1) hZ
  rw [intervalIntegrable_congr heq]
  exact ((orderedResistance_integrable_FIN035 (hx.trans_le hxr) hx).symm).const_mul _


/-- FIN036: the actual origin mass and resistance have the source scales and a
uniform logarithmic Hardy product. All constants and the threshold depend only
on the fixed ordered coupling. -/
theorem ordered_origin_logarithmic_hardy_product {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    ∃ A B D H Km Dm N0 : ℝ,
      0 < A ∧ 0 < B ∧ 0 < D ∧ 0 < H ∧ 0 < Km ∧ 0 < Dm ∧ 0 < N0 ∧
      ∀ N : ℕ+, N0 ≤ (N : ℝ) →
      (∀ x : ℝ, 0 < x → x ≤ r0 / 2 →
        IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        IntervalIntegrable (fun r => r * Real.exp (-(N : ℝ) * radialU_orad κ r0 r))
          volume 0 x ∧
        IntervalIntegrable (fun r => Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r)
          volume x r0 ∧
        IntervalIntegrable (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
            orderedRadialZ_FIN035 κ r0 (N : ℝ))) volume x r0 ∧
        0 < orderedOriginMass_FIN036 κ r0 (N : ℝ) x ∧
        0 < orderedOriginResistance_FIN036 κ r0 (N : ℝ) x ∧
        A * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) / (N : ℝ) *
            min ((N : ℝ) * x ^ 2) 1) ≤ orderedOriginMass_FIN036 κ r0 (N : ℝ) x ∧
        orderedOriginMass_FIN036 κ r0 (N : ℝ) x ≤
          B * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) / (N : ℝ) *
            min ((N : ℝ) * x ^ 2) 1) ∧
        orderedOriginResistance_FIN036 κ r0 (N : ℝ) x ≤
          D * Real.exp ((N : ℝ) * radialU_orad κ r0 x) *
            orderedOriginProfile_FIN036 ((N : ℝ) * x ^ 2) ∧
        orderedOriginMass_FIN036 κ r0 (N : ℝ) x *
          orderedOriginResistance_FIN036 κ r0 (N : ℝ) x *
          Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) /
            orderedOriginMass_FIN036 κ r0 (N : ℝ) x) ≤ H ∧
        (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) =
          orderedOriginMass_FIN036 κ r0 (N : ℝ) x / orderedRadialZ_FIN035 κ r0 (N : ℝ) ∧
        (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
            orderedRadialZ_FIN035 κ r0 (N : ℝ))) =
          orderedRadialZ_FIN035 κ r0 (N : ℝ) *
            orderedOriginResistance_FIN036 κ r0 (N : ℝ) x ∧
        (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) *
          (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
            orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
          Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x)) =
          orderedOriginMass_FIN036 κ r0 (N : ℝ) x *
            orderedOriginResistance_FIN036 κ r0 (N : ℝ) x *
            Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) /
              orderedOriginMass_FIN036 κ r0 (N : ℝ) x)) ∧
        (∀ m : ℝ,
          ((1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic m) ∧
            (1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici m)) →
          |m - r0| ≤ Km / Real.sqrt (N : ℝ) ∧
          orderedRadialZ_FIN035 κ r0 (N : ℝ) *
            |∫ r in r0..m, Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r| ≤ Dm / (N : ℝ)) := by
  obtain ⟨r0, hr0, hroot, LZ, ZB, M, Km, Dm, N35,
    hLZ, hZB, _, hKm, hDm, hN35, hest⟩ :=
    ordered_radial_normalization_moments_median hκ
  obtain ⟨c, C, hc, hcC, hnear, hfar, hquad⟩ := well_estimates_orad hκ hr0 hroot
  have hC : 0 < C := hc.trans_le hcC
  have ha : 0 < r0 / 2 := by positivity
  have har : r0 / 2 < r0 := by linarith
  let A := Real.exp (-C / 2) / 2
  let B := (1 + c / 2) / c
  let k := c / 3
  let D := 1 + 1 / k
  let V := C * r0 ^ 2
  let K := 1 + V + Real.log (1 + ZB / A)
  let H := 4 * B * D * (K + 1)
  let N0 := max N35 (max 1 ((1 / (r0 / 2)) ^ 2))
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hK : 0 < K := by
    have hlog : 0 ≤ Real.log (1 + ZB / A) := Real.log_nonneg (by
      have := div_pos hZB hA
      linarith)
    dsimp [K]
    linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hN0 : 0 < N0 := hN35.trans_le (le_max_left _ _)
  have hκ0 : 0 < κ := by linarith
  have hfroot : radialDpsi_orad κ r0 = 0 := by
    unfold radialDpsi_orad
    apply sub_eq_zero.mpr
    apply (div_eq_iff hκ0.ne').2
    nlinarith [hroot]
  have hfar' (t : ℝ) (ht : t ∈ Icc (r0 / 2) r0) :
      radialDpsi_orad κ t ≤ -c * (r0 - t) := by
    rcases ht.2.eq_or_lt with he | he
    · simp [he, hfroot]
    · have h := (hfar t ht.1).1
      have hneg := (hfar t ht.1).2.2.1 he
      rw [abs_of_neg hneg, abs_of_nonpos (by linarith : t - r0 ≤ 0)] at h
      linarith
  have hdrop (y : ℝ) (hy : y ∈ Ioc 0 (r0 / 2)) (r : ℝ) (hr : r ∈ Icc y r0) :
      k / 2 * (r ^ 2 - y ^ 2) ≤ radialU_orad κ r0 y - radialU_orad κ r0 r := by
    have h := orderedOrigin_global_drop_FIN036 hr0 hc hy.1.le hy.2 hr.1 hr.2
      (fun t ht => by have h := (hnear t ht).1; linarith) hfar'
    convert h using 1
    dsimp [k]
    ring
  refine ⟨r0, hr0, hroot, A, B, D, H, Km, Dm, N0,
    hA, hB, hD, hH, hKm, hDm, hN0, ?_⟩
  intro N hN
  have hN35' : N35 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    have h := Real.sqrt_le_sqrt hN1
    simpa using h
  have hNsq : (1 / (r0 / 2)) ^ 2 ≤ (N : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hss : 1 / (r0 / 2) ≤ Real.sqrt (N : ℝ) := by
    have h := Real.sqrt_le_sqrt hNsq
    rwa [Real.sqrt_sq (by positivity : 0 ≤ 1 / (r0 / 2))] at h
  have hscale : 1 / Real.sqrt (N : ℝ) ≤ r0 / 2 := by
    apply (div_le_iff₀ hs).2
    have h := (div_le_iff₀ ha).mp hss
    nlinarith
  obtain ⟨hprob, hZlow, hZupp, _, hmed⟩ := hest N hN35'
  have hZ : 0 < orderedRadialZ_FIN035 κ r0 (N : ℝ) :=
    (div_pos hLZ hs).trans_le hZlow
  have hZupper : orderedRadialZ_FIN035 κ r0 (N : ℝ) ≤ ZB := by
    apply hZupp.trans
    apply (div_le_iff₀ hs).2
    nlinarith [mul_nonneg hZB.le (sub_nonneg.mpr hs1)]
  have hi : Integrable (orderedRadialWeight_FIN035 κ r0 (N : ℝ)) := by
    have h := orderedRadialWeight_integrable_FIN035 hr0 hc hs1
      (fun r hr => (hquad r hr).1)
    simpa only [Real.sq_sqrt hNpos.le] using h
  refine ⟨?_, hmed⟩
  intro x hx hxa
  have hxr : x < r0 := hxa.trans_lt har
  obtain ⟨hLpos, hJpos⟩ := orderedOrigin_integrals_pos_FIN036 hx hxr
  have hmass := orderedOriginMass_min_bounds_FIN036 hc hC hNpos hx.le hxa hnear
  change A * _ ≤ _ ∧ _ ≤ B * _ at hmass
  have hres := orderedOriginResistance_profile_FIN036 hk hNpos ha har hscale hx hxa hdrop
  change orderedOriginResistance_FIN036 κ r0 (N : ℝ) x ≤
    D * Real.exp ((N : ℝ) * radialU_orad κ r0 x) *
      orderedOriginProfile_FIN036 ((N : ℝ) * x ^ 2) at hres
  have hUV : radialU_orad κ r0 x ≤ V := by
    have hsq : (x - r0) ^ 2 ≤ r0 ^ 2 := by nlinarith [hx.le, hxr.le]
    exact (hquad x hx.le).2.trans (mul_le_mul_of_nonneg_left hsq hC.le)
  have hu : 0 < (N : ℝ) * x ^ 2 := mul_pos hNpos (sq_pos_of_pos hx)
  have hlog := orderedOrigin_log_bound_FIN036 hN1 hV hUV hA hZB hLpos hZ.le hZupper hu hmass.1
  change Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) /
    orderedOriginMass_FIN036 κ r0 (N : ℝ) x) ≤
      K * (N : ℝ) + max 0 (Real.log (1 / ((N : ℝ) * x ^ 2))) at hlog
  have hhardy := orderedOrigin_product_from_estimates_FIN036 hN1 hu hB.le hD.le hK.le
    hLpos.le hJpos.le hZ.le hmass.2 hres hlog
  change _ ≤ H at hhardy
  have hnorm := orderedOrigin_normalization_FIN036 hx.le hi hZ
  have hrec := orderedOrigin_normalized_resistance_FIN036 hx hxr.le hZ
  refine ⟨hprob, orderedOriginMass_integrable_FIN036 _ _ _ _,
    (orderedResistance_integrable_FIN035 hr0 hx).symm,
    orderedOrigin_reciprocal_integrable_FIN036 hx hxr.le hZ, hLpos, hJpos,
    hmass.1, hmass.2, hres, hhardy, hnorm.1, hrec, ?_⟩
  rw [hnorm.1, hrec]
  have hlogarg :
      1 + 1 / (orderedOriginMass_FIN036 κ r0 (N : ℝ) x /
        orderedRadialZ_FIN035 κ r0 (N : ℝ)) =
      1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) /
        orderedOriginMass_FIN036 κ r0 (N : ℝ) x := by field_simp [hLpos.ne', hZ.ne']
  rw [hlogarg]
  field_simp [hZ.ne']


end DGPS.FiniteN
