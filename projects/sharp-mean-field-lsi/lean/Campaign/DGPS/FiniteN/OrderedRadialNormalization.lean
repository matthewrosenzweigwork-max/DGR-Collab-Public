import DGPS.FiniteN.OrderedRadialEstimates
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Gaussian comparison for the ordered radial law (FIN035)

The density is kept on the positive half-line, including its radial Jacobian.
The Gaussian envelope controls the normalization, raw moments through order two,
and the second moment about the positive minimizer.
-/

open MeasureTheory Set Filter
open scoped ENNReal Interval

namespace DGPS.FiniteN

/-- Unnormalized ordered radial density, extended by zero off its domain. -/
noncomputable def orderedRadialWeight_FIN035 (κ r0 N r : ℝ) : ℝ :=
  if 0 < r then r * Real.exp (-N * radialU_orad κ r0 r) else 0

/-- The actual radial partition function, including the factor r. -/
noncomputable def orderedRadialZ_FIN035 (κ r0 N : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r * Real.exp (-N * radialU_orad κ r0 r)

/-- A common integrable majorant after the change of variable u = √N (r-r0). -/
noncomputable def orderedEnvelope_FIN035 (r0 c u : ℝ) : ℝ :=
  (r0 + 1 + |u|) ^ 3 * Real.exp (-c * u ^ 2)

theorem orderedRadialWeight_nonneg_FIN035 (κ r0 N r : ℝ) :
    0 ≤ orderedRadialWeight_FIN035 κ r0 N r := by
  unfold orderedRadialWeight_FIN035
  split_ifs with h
  · positivity
  · exact le_rfl

theorem orderedRadialWeight_integral_FIN035 (κ r0 N : ℝ) :
    ∫ r, orderedRadialWeight_FIN035 κ r0 N r = orderedRadialZ_FIN035 κ r0 N := by
  change ∫ r, (Ioi (0 : ℝ)).indicator
    (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) r = _
  rw [integral_indicator measurableSet_Ioi]
  rfl

theorem orderedEnvelope_integrable_FIN035 (r0 : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (orderedEnvelope_FIN035 r0 c) := by
  have hm (k : ℕ) :
      Integrable (fun u : ℝ => |u| ^ k * Real.exp (-c * u ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq hc
      (s := (k : ℝ)) (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using h.norm
  have h := ((hm 0).const_mul ((r0 + 1) ^ 3)).add
    (((hm 1).const_mul (3 * (r0 + 1) ^ 2)).add
      (((hm 2).const_mul (3 * (r0 + 1))).add (hm 3)))
  convert h using 1
  ext u
  unfold orderedEnvelope_FIN035
  simp only [Pi.add_apply]
  ring

theorem orderedRadialWeight_continuousOn_FIN035 (κ r0 N : ℝ) :
    ContinuousOn (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) (Ici 0) := by
  have hU : Continuous (radialU_orad κ r0) :=
    continuous_iff_continuousAt.mpr fun r => (radialU_hasDerivAt_orad r0 r).continuousAt
  exact (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul hU))).continuousOn

/-- Pointwise Gaussian comparison in the scaled coordinate. -/
theorem orderedRadialWeight_scaled_le_FIN035 {κ r0 c s u p : ℝ}
    (hr0 : 0 < r0) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r)
    (hp : p ≤ (r0 + 1 + |u|) ^ 2) :
    p * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)
      ≤ orderedEnvelope_FIN035 r0 c u := by
  have hs0 : 0 < s := by linarith
  have ha : 0 < r0 + 1 + |u| := by positivity
  unfold orderedRadialWeight_FIN035 orderedEnvelope_FIN035
  split_ifs with hr
  · have hur : u / s ≤ |u| := by
      calc u / s ≤ |u| / s := div_le_div_of_nonneg_right (le_abs_self u) hs0.le
        _ ≤ |u| := (div_le_iff₀ hs0).2 (by nlinarith [abs_nonneg u])
    have hrr : r0 + u / s ≤ r0 + 1 + |u| := by linarith
    have hq := hU (r0 + u / s) hr.le
    have he : -(s ^ 2) * radialU_orad κ r0 (r0 + u / s) ≤ -c * u ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hq (sq_nonneg s)
      have h2 : s ^ 2 * (c * (r0 + u / s - r0) ^ 2) = c * u ^ 2 := by
        field_simp
        ring
      nlinarith
    have hpoly : p * (r0 + u / s) ≤ (r0 + 1 + |u|) ^ 3 := by
      calc p * (r0 + u / s) ≤ (r0 + 1 + |u|) ^ 2 * (r0 + 1 + |u|) :=
          mul_le_mul hp hrr hr.le (sq_nonneg _)
        _ = _ := by ring
    calc p * ((r0 + u / s) * Real.exp (-(s ^ 2) *
          radialU_orad κ r0 (r0 + u / s)))
        = (p * (r0 + u / s)) * Real.exp (-(s ^ 2) *
          radialU_orad κ r0 (r0 + u / s)) := by ring
      _ ≤ (r0 + 1 + |u|) ^ 3 * Real.exp (-c * u ^ 2) :=
        mul_le_mul hpoly (Real.exp_le_exp.mpr he)
          (Real.exp_pos _).le (by positivity)
  · simp only [mul_zero]
    positivity


/-- The Jacobian of the scaled, shifted real coordinate. -/
theorem ordered_scaled_integral_FIN035 (f : ℝ → ℝ) (r0 : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ u, f (r0 + u / s)) = s * ∫ r, f r := by
  calc
    (∫ u, f (r0 + u / s)) =
        |s| • ∫ v, f (r0 + v) :=
      Measure.integral_comp_div (fun v => f (r0 + v)) s
    _ = s * ∫ r, f r := by
      rw [abs_of_pos hs, smul_eq_mul, integral_add_left_eq_self]

theorem ordered_integrable_of_scaled_FIN035 {f : ℝ → ℝ} (r0 : ℝ) {s : ℝ} (hs : 0 < s)
    (hf : Integrable (fun u => f (r0 + u / s))) : Integrable f := by
  have h1 : Integrable (fun v => f (r0 + v)) := by
    apply (integrable_comp_mul_right_iff (fun v => f (r0 + v)) (inv_ne_zero hs.ne')).mp
    simpa only [div_eq_mul_inv] using hf
  have h2 := h1.comp_add_left (-r0)
  convert h2 using 1
  ext r
  congr 1
  ring

theorem orderedRadialWeight_measurable_FIN035 (κ r0 N : ℝ) :
    Measurable (orderedRadialWeight_FIN035 κ r0 N) := by
  have hU : Continuous (radialU_orad κ r0) :=
    continuous_iff_continuousAt.mpr fun r => (radialU_hasDerivAt_orad r0 r).continuousAt
  exact Measurable.ite measurableSet_Ioi
    (measurable_id.mul (Real.measurable_exp.comp (measurable_const.mul hU.measurable)))
    measurable_const

/-- Envelope domination gives integrability of an actual radial observable. -/
theorem ordered_observable_integrable_FIN035 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∀ u, 0 < r0 + u / s → |f (r0 + u / s)| ≤ (r0 + 1 + |u|) ^ 2) :
    Integrable (fun r => f r * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) := by
  have hs0 : 0 < s := by linarith
  apply ordered_integrable_of_scaled_FIN035 r0 hs0
  refine (orderedEnvelope_integrable_FIN035 r0 hc).mono' ?_ ?_
  · exact ((hf.mul (orderedRadialWeight_measurable_FIN035 κ r0 (s ^ 2))).comp
      (measurable_const.add (measurable_id.div_const s))).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (orderedRadialWeight_nonneg_FIN035 κ r0 (s ^ 2) _)]
    by_cases hr : 0 < r0 + u / s
    · exact orderedRadialWeight_scaled_le_FIN035 hr0 hs hU (hb u hr)
    · simp only [orderedRadialWeight_FIN035, ite_eq_right hr, mul_zero]
      unfold orderedEnvelope_FIN035
      positivity

theorem orderedRadialWeight_integrable_FIN035 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r) :
    Integrable (orderedRadialWeight_FIN035 κ r0 (s ^ 2)) := by
  have h := ordered_observable_integrable_FIN035 hr0 hc hs hU (fun _ => 1)
    measurable_const (fun u _ => by
      simp only [abs_one]
      have hu := abs_nonneg u
      nlinarith)
  simpa only [one_mul] using h

/-- Upper normalization comparison with an N-independent Gaussian integral. -/
theorem orderedRadialZ_upper_FIN035 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r) :
    orderedRadialZ_FIN035 κ r0 (s ^ 2) ≤
      (∫ u, orderedEnvelope_FIN035 r0 c u) / s := by
  have hs0 : 0 < s := by linarith
  have hi := orderedRadialWeight_integrable_FIN035 hr0 hc hs hU
  have his : Integrable (fun u => orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)) := by
    have h := (hi.comp_add_left r0).comp_mul_right' (inv_ne_zero hs0.ne')
    simpa only [div_eq_mul_inv] using h
  have hle : (∫ u, orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s))
      ≤ ∫ u, orderedEnvelope_FIN035 r0 c u := by
    apply integral_mono his (orderedEnvelope_integrable_FIN035 r0 hc)
    intro u
    have h1 : (1 : ℝ) ≤ (r0 + 1 + |u|) ^ 2 := by
      have := abs_nonneg u
      nlinarith
    simpa only [one_mul] using
      orderedRadialWeight_scaled_le_FIN035 hr0 hs hU h1
  rw [ordered_scaled_integral_FIN035 _ r0 hs0, orderedRadialWeight_integral_FIN035] at hle
  exact (le_div_iff₀ hs0).2 (by nlinarith)


/-- Uniform upper comparison for any controlled radial observable. -/
theorem ordered_observable_upper_FIN035 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∀ u, 0 < r0 + u / s → |f (r0 + u / s)| ≤ (r0 + 1 + |u|) ^ 2) :
    s * (∫ r, f r * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r)
      ≤ ∫ u, orderedEnvelope_FIN035 r0 c u := by
  have hs0 : 0 < s := by linarith
  have hi := ordered_observable_integrable_FIN035 hr0 hc hs hU f hf hb
  have his : Integrable (fun u =>
      f (r0 + u / s) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)) := by
    have h := (hi.comp_add_left r0).comp_mul_right' (inv_ne_zero hs0.ne')
    simpa only [div_eq_mul_inv] using h
  rw [← ordered_scaled_integral_FIN035 _ r0 hs0]
  apply integral_mono his (orderedEnvelope_integrable_FIN035 r0 hc)
  intro u
  by_cases hr : 0 < r0 + u / s
  · calc
      f (r0 + u / s) * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s)
        ≤ |f (r0 + u / s)| * orderedRadialWeight_FIN035 κ r0 (s ^ 2) (r0 + u / s) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (orderedRadialWeight_nonneg_FIN035 _ _ _ _)
      _ ≤ orderedEnvelope_FIN035 r0 c u :=
        orderedRadialWeight_scaled_le_FIN035 hr0 hs hU (hb u hr)
  · simp only [orderedRadialWeight_FIN035, ite_eq_right hr, mul_zero]
    unfold orderedEnvelope_FIN035
    positivity

/-- Lower normalization comparison, obtained on the interval [r0,r0+1/s]. -/
theorem orderedRadialZ_lower_FIN035 {κ r0 c C s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hC : 0 ≤ C) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r)
    (hUC : ∀ r, 0 ≤ r → radialU_orad κ r0 r ≤ C * (r - r0) ^ 2) :
    r0 * Real.exp (-C) / s ≤ orderedRadialZ_FIN035 κ r0 (s ^ 2) := by
  have hs0 : 0 < s := by linarith
  have hi := orderedRadialWeight_integrable_FIN035 hr0 hc hs hU
  have hsi : 0 < 1 / s := one_div_pos.mpr hs0
  have hlow : ∀ r ∈ Icc r0 (r0 + 1 / s),
      r0 * Real.exp (-C) ≤ orderedRadialWeight_FIN035 κ r0 (s ^ 2) r := by
    intro r hr
    have hrpos : 0 < r := hr0.trans_le hr.1
    have hd0 : 0 ≤ r - r0 := sub_nonneg.mpr hr.1
    have hd1 : r - r0 ≤ 1 / s := by linarith [hr.2]
    have hsd : s * (r - r0) ≤ 1 := by
      have := (le_div_iff₀ hs0).mp hd1
      nlinarith
    have hsd0 : 0 ≤ s * (r - r0) := mul_nonneg hs0.le hd0
    have hsq : s ^ 2 * (r - r0) ^ 2 ≤ 1 := by nlinarith
    have hcu := hUC r hrpos.le
    have hnu : s ^ 2 * radialU_orad κ r0 r ≤ C := by
      have h1 := mul_le_mul_of_nonneg_left hcu (sq_nonneg s)
      have h2 := mul_le_mul_of_nonneg_left hsq hC
      nlinarith
    unfold orderedRadialWeight_FIN035
    rw [ite_eq_left hrpos]
    exact mul_le_mul hr.1 (Real.exp_le_exp.mpr (by linarith))
      (Real.exp_pos _).le hrpos.le
  have hcint : IntegrableOn (fun _ : ℝ => r0 * Real.exp (-C)) (Icc r0 (r0 + 1 / s)) :=
    continuous_const.integrableOn_Icc
  calc r0 * Real.exp (-C) / s =
      ∫ _r in Icc r0 (r0 + 1 / s), r0 * Real.exp (-C) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring
    _ ≤ ∫ r in Icc r0 (r0 + 1 / s), orderedRadialWeight_FIN035 κ r0 (s ^ 2) r :=
      setIntegral_mono_on hcint hi.integrableOn measurableSet_Icc hlow
    _ ≤ ∫ r, orderedRadialWeight_FIN035 κ r0 (s ^ 2) r :=
      setIntegral_le_integral hi (Eventually.of_forall (orderedRadialWeight_nonneg_FIN035 _ _ _))
    _ = orderedRadialZ_FIN035 κ r0 (s ^ 2) := orderedRadialWeight_integral_FIN035 _ _ _

/-- Raw second moment about r0 has the Gaussian N^{-3/2} scale. -/
theorem orderedCentralMoment_upper_FIN035 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r) :
    s ^ 3 * (∫ r, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r)
      ≤ ∫ u, orderedEnvelope_FIN035 r0 c u := by
  have hs0 : 0 < s := by linarith
  have hb : ∀ u, 0 < r0 + u / s →
      |(s * (r0 + u / s - r0)) ^ 2| ≤ (r0 + 1 + |u|) ^ 2 := by
    intro u _
    have he : s * (r0 + u / s - r0) = u := by field_simp; ring
    rw [he, abs_of_nonneg (sq_nonneg _)]
    have := abs_nonneg u
    nlinarith [sq_abs u]
  have h := ordered_observable_upper_FIN035 hr0 hc hs hU
    (fun r => (s * (r - r0)) ^ 2) (by fun_prop) hb
  have he : (∫ r, (s * (r - r0)) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) =
      s ^ 2 * (∫ r, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun r => by ring
  rw [he] at h
  nlinarith


/-- The first two unnormalized moments obey the same Gaussian upper comparison. -/
theorem orderedRawMoment_upper_FIN035 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r)
    (j : ℕ) (hj : j ≤ 2) :
    Integrable (fun r => r ^ j * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) ∧
    s * (∫ r, r ^ j * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r)
      ≤ ∫ u, orderedEnvelope_FIN035 r0 c u := by
  have hs0 : 0 < s := by linarith
  have hb : ∀ u, 0 < r0 + u / s →
      |(r0 + u / s) ^ j| ≤ (r0 + 1 + |u|) ^ 2 := by
    intro u hr
    have hu := abs_nonneg u
    have hur : u / s ≤ |u| := by
      calc u / s ≤ |u| / s := div_le_div_of_nonneg_right (le_abs_self _) hs0.le
        _ ≤ |u| := (div_le_iff₀ hs0).2 (by nlinarith)
    have hrr : r0 + u / s ≤ r0 + 1 + |u| := by linarith
    rw [abs_pow, abs_of_pos hr]
    interval_cases j
    · simp only [pow_zero]
      nlinarith
    · simp only [pow_one]
      nlinarith
    · nlinarith
  exact ⟨ordered_observable_integrable_FIN035 hr0 hc hs hU _ (by fun_prop) hb,
    ordered_observable_upper_FIN035 hr0 hc hs hU _ (by fun_prop) hb⟩

/-- The central second moment is an integrable observable. -/
theorem orderedCentralMoment_integrable_FIN035 {κ r0 c s : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r) :
    Integrable (fun r => (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) := by
  have hs0 : 0 < s := by linarith
  apply ordered_observable_integrable_FIN035 hr0 hc hs hU _ (by fun_prop)
  intro u _
  have h1 : |u / s| ≤ |u| := by
    rw [abs_div, abs_of_pos hs0]
    exact (div_le_iff₀ hs0).2 (by nlinarith [abs_nonneg u])
  have h2 : r0 + u / s - r0 = u / s := by ring
  rw [h2, abs_pow]
  have := abs_nonneg (u / s)
  have := abs_nonneg u
  nlinarith

/-- A median is expressed by its two half-line masses for the actual radial density. -/
def orderedRadialMedian_FIN035 (κ r0 N m : ℝ) : Prop :=
  orderedRadialZ_FIN035 κ r0 N / 2 ≤
      ∫ r in Iic m, orderedRadialWeight_FIN035 κ r0 N r ∧
  orderedRadialZ_FIN035 κ r0 N / 2 ≤
      ∫ r in Ici m, orderedRadialWeight_FIN035 κ r0 N r

/-- One-sided second-moment comparison forces every median toward r0. -/
theorem orderedMedian_moment_FIN035 {κ r0 c s m : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hU : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r)
    (hm : orderedRadialMedian_FIN035 κ r0 (s ^ 2) m) :
    (m - r0) ^ 2 * (orderedRadialZ_FIN035 κ r0 (s ^ 2) / 2) ≤
      ∫ r, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r := by
  have hi := orderedRadialWeight_integrable_FIN035 hr0 hc hs hU
  have hmi := orderedCentralMoment_integrable_FIN035 hr0 hc hs hU
  have hbound (E : Set ℝ) (hE : MeasurableSet E)
      (hE' : ∀ r ∈ E, (m - r0) ^ 2 ≤ (r - r0) ^ 2)
      (hmed : orderedRadialZ_FIN035 κ r0 (s ^ 2) / 2 ≤
        ∫ r in E, orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) :
      (m - r0) ^ 2 * (orderedRadialZ_FIN035 κ r0 (s ^ 2) / 2) ≤
        ∫ r, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r := by
    calc (m - r0) ^ 2 * (orderedRadialZ_FIN035 κ r0 (s ^ 2) / 2)
        ≤ (m - r0) ^ 2 * ∫ r in E, orderedRadialWeight_FIN035 κ r0 (s ^ 2) r :=
          mul_le_mul_of_nonneg_left hmed (sq_nonneg _)
      _ = ∫ r in E, (m - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ r in E, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r :=
        setIntegral_mono_on (hi.const_mul _).integrableOn hmi.integrableOn hE
          (fun r hr => mul_le_mul_of_nonneg_right (hE' r hr)
            (orderedRadialWeight_nonneg_FIN035 _ _ _ _))
      _ ≤ ∫ r, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r :=
        setIntegral_le_integral hmi (Eventually.of_forall fun r =>
          mul_nonneg (sq_nonneg _) (orderedRadialWeight_nonneg_FIN035 _ _ _ _))
  by_cases hmr : r0 ≤ m
  · exact hbound (Ici m) measurableSet_Ici (fun r hr => by
      have : m ≤ r := hr
      nlinarith) hm.2
  · exact hbound (Iic m) measurableSet_Iic (fun r hr => by
      have : r ≤ m := hr
      nlinarith) hm.1


/-- The resistance integrand is genuinely integrable when both endpoints are positive. -/
theorem orderedResistance_integrable_FIN035 {κ r0 N m : ℝ}
    (hr0 : 0 < r0) (hm : 0 < m) :
    IntervalIntegrable (fun r => Real.exp (N * radialU_orad κ r0 r) / r) volume r0 m := by
  have hU : Continuous (radialU_orad κ r0) :=
    continuous_iff_continuousAt.mpr fun r => (radialU_hasDerivAt_orad r0 r).continuousAt
  have hpos : ∀ r ∈ uIcc r0 m, r ≠ 0 := by
    intro r hr
    exact ((lt_min hr0 hm).trans_le hr.1).ne'
  exact ((Real.continuous_exp.comp (continuous_const.mul hU)).continuousOn.div
    continuousOn_id hpos).intervalIntegrable

/-- The resistance integral on the median window, retaining its 1/r factor. -/
theorem orderedResistance_window_FIN035 {κ r0 C s K m : ℝ}
    (hr0 : 0 < r0) (hC : 0 ≤ C) (hs : 0 < s) (hK : 0 ≤ K)
    (hlarge : 2 * K ≤ r0 * s) (hm : |m - r0| ≤ K / s)
    (hUC : ∀ r, 0 ≤ r → radialU_orad κ r0 r ≤ C * (r - r0) ^ 2) :
    IntervalIntegrable (fun r => Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) volume r0 m ∧
    |∫ r in r0..m, Real.exp (s ^ 2 * radialU_orad κ r0 r) / r|
      ≤ (2 * Real.exp (C * K ^ 2) / r0) * (K / s) := by
  have hKs : 0 ≤ K / s := div_nonneg hK hs.le
  have hKs' : K / s ≤ r0 / 2 := by
    apply (div_le_iff₀ hs).2
    nlinarith
  have hmpos : 0 < m := by
    have hmlow := (abs_le.mp hm).1
    linarith
  refine ⟨orderedResistance_integrable_FIN035 hr0 hmpos, ?_⟩
  have hnorm : ∀ r ∈ Ι r0 m,
      ‖Real.exp (s ^ 2 * radialU_orad κ r0 r) / r‖ ≤
        2 * Real.exp (C * K ^ 2) / r0 := by
    intro r hr
    have hr' : r ∈ uIcc r0 m := uIoc_subset_uIcc hr
    have hrlo : r0 - K / s ≤ r := by
      rcases le_total r0 m with h | h
      · rw [uIcc_of_le h] at hr'
        linarith [hr'.1]
      · rw [uIcc_of_ge h] at hr'
        have := (abs_le.mp hm).1
        linarith [hr'.1]
    have hrhi : r ≤ r0 + K / s := by
      rcases le_total r0 m with h | h
      · rw [uIcc_of_le h] at hr'
        have := (abs_le.mp hm).2
        linarith [hr'.2]
      · rw [uIcc_of_ge h] at hr'
        linarith [hr'.2]
    have hrpos : 0 < r := by linarith
    have hrhalf : r0 / 2 ≤ r := by linarith
    have hrd : |r - r0| ≤ K / s := abs_le.mpr ⟨by linarith, by linarith⟩
    have hsrd : s * |r - r0| ≤ K := by
      have := (le_div_iff₀ hs).mp hrd
      nlinarith
    have hq : s ^ 2 * (r - r0) ^ 2 ≤ K ^ 2 := by
      calc
        s ^ 2 * (r - r0) ^ 2 = (s * |r - r0|) * (s * |r - r0|) := by
          rw [← sq_abs (r - r0)]
          ring
        _ ≤ K * K := mul_le_mul hsrd hsrd
          (mul_nonneg hs.le (abs_nonneg _)) hK
        _ = K ^ 2 := by ring
    have he : s ^ 2 * radialU_orad κ r0 r ≤ C * K ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left (hUC r hrpos.le) (sq_nonneg s)
      have h2 := mul_le_mul_of_nonneg_left hq hC
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hrpos)]
    apply (div_le_iff₀ hrpos).2
    have hE : Real.exp (s ^ 2 * radialU_orad κ r0 r) ≤ Real.exp (C * K ^ 2) :=
      Real.exp_le_exp.mpr he
    have hp := Real.exp_pos (C * K ^ 2)
    have : Real.exp (C * K ^ 2) ≤
        (2 * Real.exp (C * K ^ 2) / r0) * r := by
      have hprod : Real.exp (C * K ^ 2) * r0 ≤ 2 * Real.exp (C * K ^ 2) * r := by
        nlinarith
      have hdiv := (le_div_iff₀ hr0).2 hprod
      convert hdiv using 1; ring
    exact hE.trans this
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left hm (by positivity))



/-- The normalized probability measure of the positive radial coordinate. -/
noncomputable def orderedRadialLaw_FIN035 (κ r0 N : ℝ) : Measure ℝ :=
  volume.withDensity (fun r => ENNReal.ofReal
    (orderedRadialWeight_FIN035 κ r0 N r / orderedRadialZ_FIN035 κ r0 N))

theorem orderedRadialLaw_probability_FIN035 {κ r0 N : ℝ}
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 N) := by
  have hρ : ∀ r, 0 ≤ orderedRadialWeight_FIN035 κ r0 N r /
      orderedRadialZ_FIN035 κ r0 N :=
    fun r => div_nonneg (orderedRadialWeight_nonneg_FIN035 _ _ _ _) hZ.le
  refine ⟨?_⟩
  unfold orderedRadialLaw_FIN035
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (Eventually.of_forall hρ),
    integral_div, orderedRadialWeight_integral_FIN035, div_self hZ.ne',
    ENNReal.ofReal_one]

/-- Exact normalized-density representation for every measurable set, in particular intervals. -/
theorem orderedRadialLaw_mass_FIN035 {κ r0 N : ℝ}
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) {E : Set ℝ} (hE : MeasurableSet E) :
    (orderedRadialLaw_FIN035 κ r0 N).real E =
      (∫ r in E, orderedRadialWeight_FIN035 κ r0 N r) /
        orderedRadialZ_FIN035 κ r0 N := by
  have hρ : ∀ r, 0 ≤ orderedRadialWeight_FIN035 κ r0 N r /
      orderedRadialZ_FIN035 κ r0 N :=
    fun r => div_nonneg (orderedRadialWeight_nonneg_FIN035 _ _ _ _) hZ.le
  unfold orderedRadialLaw_FIN035 Measure.real
  rw [withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _).integrableOn
      (Eventually.of_forall hρ),
    ENNReal.toReal_ofReal (integral_nonneg hρ), integral_div]


/-- The normalized law gives full mass to its stated positive-half-line domain. -/
theorem orderedRadialLaw_positive_domain_FIN035 {κ r0 N : ℝ}
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    (orderedRadialLaw_FIN035 κ r0 N).real (Ioi 0) = 1 := by
  rw [orderedRadialLaw_mass_FIN035 hi hZ measurableSet_Ioi]
  have he : (∫ r in Ioi (0 : ℝ), orderedRadialWeight_FIN035 κ r0 N r) =
      orderedRadialZ_FIN035 κ r0 N := by
    unfold orderedRadialZ_FIN035
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hrpos : 0 < r := hr
    simp only [orderedRadialWeight_FIN035, ite_eq_left hrpos]
  rw [he, div_self hZ.ne']

/-- All actual radial expectations are the normalized Lebesgue integrals. -/
theorem orderedRadialLaw_integral_FIN035 {κ r0 N : ℝ}
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) (f : ℝ → ℝ) :
    ∫ r, f r ∂orderedRadialLaw_FIN035 κ r0 N =
      (∫ r, f r * orderedRadialWeight_FIN035 κ r0 N r) /
        orderedRadialZ_FIN035 κ r0 N := by
  unfold orderedRadialLaw_FIN035
  rw [integral_withDensity_eq_integral_toReal_smul
    (((orderedRadialWeight_measurable_FIN035 κ r0 N).div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_div]
  apply integral_congr_ae
  refine Eventually.of_forall fun r => ?_
  dsimp only
  rw [ENNReal.toReal_ofReal (div_nonneg (orderedRadialWeight_nonneg_FIN035 _ _ _ _) hZ.le),
    smul_eq_mul]
  ring

theorem orderedRadialLaw_integrable_FIN035 {κ r0 N : ℝ}
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) (f : ℝ → ℝ)
    (hi : Integrable (fun r => f r * orderedRadialWeight_FIN035 κ r0 N r)) :
    Integrable f (orderedRadialLaw_FIN035 κ r0 N) := by
  unfold orderedRadialLaw_FIN035
  rw [integrable_withDensity_iff_integrable_smul'
    (((orderedRadialWeight_measurable_FIN035 κ r0 N).div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  convert hi.div_const (orderedRadialZ_FIN035 κ r0 N) using 1
  ext r
  rw [ENNReal.toReal_ofReal (div_nonneg (orderedRadialWeight_nonneg_FIN035 _ _ _ _) hZ.le),
    smul_eq_mul]
  ring

/-- Every median of the actual radial probability has the raw half-mass properties. -/
theorem orderedMedian_of_law_FIN035 {κ r0 N m : ℝ}
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N)
    (hm : (1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 N).real (Iic m) ∧
      (1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 N).real (Ici m)) :
    orderedRadialMedian_FIN035 κ r0 N m := by
  rw [orderedRadialLaw_mass_FIN035 hi hZ measurableSet_Iic,
    orderedRadialLaw_mass_FIN035 hi hZ measurableSet_Ici] at hm
  have h1 := (le_div_iff₀ hZ).mp hm.1
  have h2 := (le_div_iff₀ hZ).mp hm.2
  exact ⟨by nlinarith, by nlinarith⟩

/-- FIN035: normalization, first two moments, all medians, and median resistance for
the ordered radial density. The constants depend only on κ. The raw-integral
definition of a median is exactly the usual two half-mass inequalities after
division by the positive partition function. -/
theorem ordered_radial_estimates_raw_FIN035 {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    ∃ L B M K D N0 : ℝ,
      0 < L ∧ 0 < B ∧ 0 < M ∧ 0 < K ∧ 0 < D ∧ 0 < N0 ∧
      ∀ N : ℝ, N0 ≤ N →
        L / Real.sqrt N ≤ orderedRadialZ_FIN035 κ r0 N ∧
        orderedRadialZ_FIN035 κ r0 N ≤ B / Real.sqrt N ∧
        (∀ j : ℕ, j ≤ 2 →
          Integrable (fun r => r ^ j * orderedRadialWeight_FIN035 κ r0 N r) ∧
          (∫ r, r ^ j * orderedRadialWeight_FIN035 κ r0 N r) /
            orderedRadialZ_FIN035 κ r0 N ≤ M) ∧
        (∀ m : ℝ, orderedRadialMedian_FIN035 κ r0 N m →
          |m - r0| ≤ K / Real.sqrt N ∧
          orderedRadialZ_FIN035 κ r0 N *
            |∫ r in r0..m, Real.exp (N * radialU_orad κ r0 r) / r| ≤ D / N) := by
  obtain ⟨r0, hr0, hroot, -, c, C, hc, hcC, -, -, hquad⟩ :=
    ordered_radial_well_geometry hκ
  have hC : 0 ≤ C := hc.le.trans hcC
  have hU := fun r hr => (hquad r hr).1
  have hUC := fun r hr => (hquad r hr).2
  let L := r0 * Real.exp (-C)
  let B := ∫ u, orderedEnvelope_FIN035 r0 c u
  have hL : 0 < L := mul_pos hr0 (Real.exp_pos _)
  have hB : 0 < B := by
    have h1 := orderedRadialZ_lower_FIN035 hr0 hc hC (s := 1) le_rfl hU hUC
    have h2 := orderedRadialZ_upper_FIN035 hr0 hc (s := 1) le_rfl hU
    simp only [one_pow, div_one] at h1 h2
    exact hL.trans_le (h1.trans h2)
  let K := 1 + 2 * B / L
  have hK : 0 < K := by dsimp [K]; positivity
  have hKL : 2 * B < L * K ^ 2 := by
    have hdiv : 2 * B / L * L = 2 * B := div_mul_cancel₀ _ hL.ne'
    have hdiv0 : 0 < 2 * B / L := by positivity
    dsimp [K]
    nlinarith [sq_nonneg (2 * B / L)]
  let s0 := max 1 (2 * K / r0)
  have hs01 : 1 ≤ s0 := le_max_left _ _
  have hs00 : 0 < s0 := lt_of_lt_of_le zero_lt_one hs01
  let D := 2 * B * K * Real.exp (C * K ^ 2) / r0
  have hD : 0 < D := by dsimp [D]; positivity
  have hest (s : ℝ) (hss : s0 ≤ s) :
      L / s ≤ orderedRadialZ_FIN035 κ r0 (s ^ 2) ∧
      orderedRadialZ_FIN035 κ r0 (s ^ 2) ≤ B / s ∧
      (∀ j : ℕ, j ≤ 2 →
        Integrable (fun r => r ^ j * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) ∧
        (∫ r, r ^ j * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) /
          orderedRadialZ_FIN035 κ r0 (s ^ 2) ≤ B / L) ∧
      (∀ m : ℝ, orderedRadialMedian_FIN035 κ r0 (s ^ 2) m →
        |m - r0| ≤ K / s ∧
        orderedRadialZ_FIN035 κ r0 (s ^ 2) *
          |∫ r in r0..m, Real.exp (s ^ 2 * radialU_orad κ r0 r) / r| ≤ D / s ^ 2) := by
    have hs1 : 1 ≤ s := hs01.trans hss
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hlow := orderedRadialZ_lower_FIN035 hr0 hc hC hs1 hU hUC
    have hupp := orderedRadialZ_upper_FIN035 hr0 hc hs1 hU
    have hZpos : 0 < orderedRadialZ_FIN035 κ r0 (s ^ 2) :=
      (div_pos hL hs0).trans_le hlow
    have hZlow : L ≤ s * orderedRadialZ_FIN035 κ r0 (s ^ 2) := by
      have h := (div_le_iff₀ hs0).mp hlow
      change r0 * Real.exp (-C) ≤ s * orderedRadialZ_FIN035 κ r0 (s ^ 2)
      nlinarith
    refine ⟨hlow, hupp, ?_, ?_⟩
    · intro j hj
      obtain ⟨hi, hraw⟩ := orderedRawMoment_upper_FIN035 hr0 hc hs1 hU j hj
      refine ⟨hi, (div_le_div_iff₀ hZpos hL).2 ?_⟩
      have h1 := mul_le_mul_of_nonneg_left hraw hL.le
      have h2 := mul_le_mul_of_nonneg_left hZlow hB.le
      by_contra h
      have hbad := mul_pos hs0 (sub_pos.mpr (lt_of_not_ge h))
      nlinarith
    · intro m hm
      have hmom := orderedMedian_moment_FIN035 hr0 hc hs1 hU hm
      have hcentral := orderedCentralMoment_upper_FIN035 hr0 hc hs1 hU
      have hm2 : L * (s * (m - r0)) ^ 2 ≤ 2 * B := by
        calc L * (s * (m - r0)) ^ 2 ≤
            (s * orderedRadialZ_FIN035 κ r0 (s ^ 2)) * (s * (m - r0)) ^ 2 :=
              mul_le_mul_of_nonneg_right hZlow (sq_nonneg _)
          _ = (2 * s ^ 3) *
              ((m - r0) ^ 2 * (orderedRadialZ_FIN035 κ r0 (s ^ 2) / 2)) := by ring
          _ ≤ (2 * s ^ 3) *
              (∫ r, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (s ^ 2) r) :=
                mul_le_mul_of_nonneg_left hmom (by positivity)
          _ ≤ 2 * B := by nlinarith
      have hwindow : |m - r0| ≤ K / s := by
        apply (le_div_iff₀ hs0).2
        by_contra h
        have hgt : K < |m - r0| * s := lt_of_not_ge h
        have hd := abs_nonneg (m - r0)
        have hsq : K ^ 2 < (s * (m - r0)) ^ 2 := by
          nlinarith [sq_abs (m - r0)]
        have := mul_lt_mul_of_pos_left hsq hL
        linarith
      have hlarge : 2 * K ≤ r0 * s := by
        have h1 : 2 * K / r0 ≤ s := (le_max_right _ _).trans hss
        have := (div_le_iff₀ hr0).mp h1
        nlinarith
      have hres := orderedResistance_window_FIN035 hr0 hC hs0 hK.le hlarge hwindow hUC
      refine ⟨hwindow, ?_⟩
      calc orderedRadialZ_FIN035 κ r0 (s ^ 2) *
          |∫ r in r0..m, Real.exp (s ^ 2 * radialU_orad κ r0 r) / r|
          ≤ (B / s) * ((2 * Real.exp (C * K ^ 2) / r0) * (K / s)) :=
            mul_le_mul hupp hres.2 (abs_nonneg _) (div_nonneg hB.le hs0.le)
        _ = D / s ^ 2 := by dsimp [D]; field_simp
  refine ⟨r0, hr0, hroot, L, B, B / L, K, D, s0 ^ 2,
    hL, hB, div_pos hB hL, hK, hD, sq_pos_of_pos hs00, ?_⟩
  intro N hN
  have hN0 : 0 < N := (sq_pos_of_pos hs00).trans_le hN
  have hss : s0 ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt hN
    rwa [Real.sqrt_sq hs00.le] at h
  have h := hest (Real.sqrt N) hss
  simpa only [Real.sq_sqrt hN0.le] using h


/-- FIN035 with the exact positive-integer quantifier and the actual normalized radial
probability, its moments, and every median. -/
theorem ordered_radial_normalization_moments_median {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    ∃ L B M K D N0 : ℝ,
      0 < L ∧ 0 < B ∧ 0 < M ∧ 0 < K ∧ 0 < D ∧ 0 < N0 ∧
      ∀ N : ℕ+, N0 ≤ (N : ℝ) →
        IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        L / Real.sqrt (N : ℝ) ≤ orderedRadialZ_FIN035 κ r0 (N : ℝ) ∧
        orderedRadialZ_FIN035 κ r0 (N : ℝ) ≤ B / Real.sqrt (N : ℝ) ∧
        (∀ j : ℕ, j ≤ 2 →
          Integrable (fun r : ℝ => r ^ j) (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
          (∫ r, r ^ j ∂orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ≤ M) ∧
        (∀ m : ℝ,
          ((1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic m) ∧
            (1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici m)) →
          |m - r0| ≤ K / Real.sqrt (N : ℝ) ∧
          orderedRadialZ_FIN035 κ r0 (N : ℝ) *
            |∫ r in r0..m, Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r| ≤ D / (N : ℝ)) := by
  obtain ⟨r0, hr0, hroot, L, B, M, K, D, N0,
    hL, hB, hM, hK, hD, hN0, hest⟩ := ordered_radial_estimates_raw_FIN035 hκ
  refine ⟨r0, hr0, hroot, L, B, M, K, D, N0,
    hL, hB, hM, hK, hD, hN0, ?_⟩
  intro N hN
  obtain ⟨hlow, hupp, hmom, hmed⟩ := hest (N : ℝ) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hZ : 0 < orderedRadialZ_FIN035 κ r0 (N : ℝ) :=
    (div_pos hL (Real.sqrt_pos.mpr hNpos)).trans_le hlow
  have hi : Integrable (orderedRadialWeight_FIN035 κ r0 (N : ℝ)) := by
    simpa only [pow_zero, one_mul] using (hmom 0 (by norm_num)).1
  refine ⟨orderedRadialLaw_probability_FIN035 hi hZ, hlow, hupp, ?_, ?_⟩
  · intro j hj
    obtain ⟨hij, hbound⟩ := hmom j hj
    refine ⟨orderedRadialLaw_integrable_FIN035 hZ _ hij, ?_⟩
    rw [orderedRadialLaw_integral_FIN035 hZ]
    exact hbound
  · intro m hm
    exact hmed m (orderedMedian_of_law_FIN035 hi hZ hm)


end DGPS.FiniteN
