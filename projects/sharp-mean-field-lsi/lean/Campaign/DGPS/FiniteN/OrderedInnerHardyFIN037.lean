import DGPS.FiniteN.OrderedRadialNormalization

/-!
# Inner ordered well estimates (FIN037)

The mass below x and the resistance from x to r0 retain the actual radial
Jacobian. Anchored potential differences, rather than Gaussian comparisons
with different exponents, are used throughout.
-/

open MeasureTheory Set Filter
open scoped Interval

namespace DGPS.FiniteN

/-- Actual unnormalized cumulative radial mass. -/
noncomputable def orderedInnerMass_FIN037 (κ r0 N x : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..x, r * Real.exp (-N * radialU_orad κ r0 r)

/-- Actual unnormalized resistance, anchored at the minimum. -/
noncomputable def orderedInnerResistance_FIN037 (κ r0 N x : ℝ) : ℝ :=
  ∫ r in x..r0, Real.exp (N * radialU_orad κ r0 r) / r

theorem orderedU_continuous_FIN037 (κ r0 : ℝ) : Continuous (radialU_orad κ r0) :=
  continuous_iff_continuousAt.mpr fun r => (radialU_hasDerivAt_orad r0 r).continuousAt

theorem orderedWeight_intervalIntegrable_FIN037 (κ r0 N a b : ℝ) :
    IntervalIntegrable (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) volume a b :=
  (continuous_id.mul (Real.continuous_exp.comp
    (continuous_const.mul (orderedU_continuous_FIN037 κ r0)))).intervalIntegrable a b

/-- The derivative lower bound gives a comparison anchored at either endpoint. -/
theorem orderedU_anchored_lower_FIN037 {κ r0 c r x : ℝ}
    (hlow : ∀ t ∈ Icc (r0 / 2) r0, radialDpsi_orad κ t ≤ -c * (r0 - t))
    (hr : r0 / 2 ≤ r) (hrx : r ≤ x) (hx : x ≤ r0) :
    c / 2 * ((r - r0) ^ 2 - (x - r0) ^ 2) ≤
      radialU_orad κ r0 r - radialU_orad κ r0 x := by
  have ha := antitoneOn_of_hasDerivAt_orad (convex_Icc (r0 / 2) r0)
    (radialU_sub_quad_hasDerivAt_orad (κ := κ) r0 (c / 2))
    (fun t ht => by have := hlow t ht; linarith)
  have h := ha ⟨hr, hrx.trans hx⟩ ⟨hr.trans hrx, hx⟩ hrx
  dsimp only at h
  linarith

/-- Global Lipschitz control gives the upper anchored comparison, including the
short window extending below r0/2. -/
theorem orderedU_anchored_upper_FIN037 {κ r0 r x : ℝ}
    (hκ : 2 < κ) (hr0 : 0 < r0)
    (hroot : r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0)
    (hr : 0 ≤ r) (hrx : r ≤ x) (hx : x ≤ r0) :
    radialU_orad κ r0 r - radialU_orad κ r0 x ≤
      (1 / 4 : ℝ) * ((r - r0) ^ 2 - (x - r0) ^ 2) := by
  have hf0 : radialDpsi_orad κ r0 = 0 := by
    unfold radialDpsi_orad
    have hκ0 : κ ≠ 0 := by linarith
    have : r0 / κ = DGPS.Circle.BesselMoments.besselRatio r0 := by
      apply (div_eq_iff hκ0).2
      nlinarith [hroot]
    linarith
  have hmono := monotoneOn_of_hasDerivAt_orad (convex_Icc 0 r0)
    (radialU_sub_quad_hasDerivAt_orad (κ := κ) r0 (1 / 4))
    (fun t ht => by
      have h := dpsi_lipschitz_orad hκ hr0.le ht.1
      rw [hf0, sub_zero, abs_of_nonpos (show t - r0 ≤ 0 by linarith [ht.2])] at h
      have h := (abs_le.mp h).1
      linarith)
  have h := hmono ⟨hr, hrx.trans hx⟩ ⟨hr.trans hrx, hx⟩ hrx
  dsimp only at h
  linarith

/-- The short left window has uniformly bounded potential increase in the scaled
coordinate; no origin-Hardy estimate is used. -/
theorem orderedInner_window_FIN037 {κ r0 s x : ℝ}
    (hκ : 2 < κ) (hr0 : 0 < r0)
    (hroot : r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0)
    (hs : 1 ≤ s) (hlarge : 4 ≤ r0 * s) (hx : x ∈ Icc (r0 / 2) r0) :
    let δ := 1 / (s * (1 + s * (r0 - x)))
    0 < δ ∧ r0 / 4 ≤ x - δ ∧
      ∀ r ∈ Icc (x - δ) x,
        s ^ 2 * (radialU_orad κ r0 r - radialU_orad κ r0 x) ≤ 1 := by
  dsimp only
  let d := r0 - x
  let δ := 1 / (s * (1 + s * d))
  have hs0 : 0 < s := by linarith
  have hd : 0 ≤ d := sub_nonneg.mpr hx.2
  have hq : 0 ≤ s * d := mul_nonneg hs0.le hd
  have hden : 0 < s * (1 + s * d) := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have he : s * (1 + s * d) * δ = 1 := mul_one_div_cancel hden.ne'
  have hsδ : s * δ ≤ 1 := by
    have : 0 ≤ s * d * (s * δ) := mul_nonneg hq (mul_nonneg hs0.le hδ.le)
    nlinarith [he]
  have hqδ : (s * d) * (s * δ) ≤ 1 := by nlinarith [he]
  have hδa : δ ≤ r0 / 4 := by
    have h1 := mul_le_mul_of_nonneg_right hlarge hδ.le
    have h2 := mul_le_mul_of_nonneg_left hsδ hr0.le
    nlinarith
  refine ⟨hδ, by linarith [hx.1], ?_⟩
  intro r hr
  have hr1 : x - δ ≤ r := hr.1
  have hrpos : 0 ≤ r := by linarith [hr.1, hr1, hδa, hx.1]
  have hcomp := orderedU_anchored_upper_FIN037 hκ hr0 hroot hrpos hr.2 hx.2
  have ht : 0 ≤ x - r := sub_nonneg.mpr hr.2
  have htδ : x - r ≤ δ := by linarith [hr1]
  have hpoly : (r - r0) ^ 2 - (x - r0) ^ 2 ≤ 2 * d * δ + δ ^ 2 := by
    have hprod : d * (x - r) ≤ d * δ := mul_le_mul_of_nonneg_left htδ hd
    have hsqr : (x - r) ^ 2 ≤ δ ^ 2 := (sq_le_sq₀ ht hδ.le).2 htδ
    dsimp [d] at *
    nlinarith
  have hsδ0 : 0 ≤ s * δ := mul_nonneg hs0.le hδ.le
  have hsδ2 : (s * δ) ^ 2 ≤ 1 := by nlinarith
  calc
    s ^ 2 * (radialU_orad κ r0 r - radialU_orad κ r0 x)
      ≤ s ^ 2 * ((1 / 4 : ℝ) * (2 * d * δ + δ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hcomp.trans
          (mul_le_mul_of_nonneg_left hpoly (by norm_num))) (sq_nonneg s)
    _ = (2 * ((s * d) * (s * δ)) + (s * δ) ^ 2) / 4 := by ring
    _ ≤ 1 := by linarith

/-- The local window yields the required lower bound for the actual cumulative mass. -/
theorem orderedInnerMass_lower_FIN037 {κ r0 s x : ℝ}
    (hκ : 2 < κ) (hr0 : 0 < r0)
    (hroot : r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0)
    (hs : 1 ≤ s) (hlarge : 4 ≤ r0 * s) (hx : x ∈ Icc (r0 / 2) r0) :
    (r0 / 4 * Real.exp (-1)) *
        (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
          (s * (1 + s * (r0 - x)))) ≤ orderedInnerMass_FIN037 κ r0 (s ^ 2) x := by
  let δ := 1 / (s * (1 + s * (r0 - x)))
  obtain ⟨hδ, hδx, hwindow⟩ := orderedInner_window_FIN037 hκ hr0 hroot hs hlarge hx
  change 0 < δ at hδ
  change r0 / 4 ≤ x - δ at hδx
  have hxl : 0 ≤ x - δ := by linarith
  have hxx : x - δ ≤ x := by linarith
  have hmono := intervalIntegral.integral_mono_on hxx
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => r0 / 4 * Real.exp (-1) *
        Real.exp (-(s ^ 2) * radialU_orad κ r0 x)) volume (x - δ) x)
    (orderedWeight_intervalIntegrable_FIN037 κ r0 (s ^ 2) (x - δ) x) (fun r hr => by
      have hrlo : r0 / 4 ≤ r := hδx.trans hr.1
      have he : -(s ^ 2) * radialU_orad κ r0 x - 1 ≤
          -(s ^ 2) * radialU_orad κ r0 r := by
        have := hwindow r hr
        linarith
      calc
        r0 / 4 * Real.exp (-1) * Real.exp (-(s ^ 2) * radialU_orad κ r0 x)
          = r0 / 4 * Real.exp (-(s ^ 2) * radialU_orad κ r0 x - 1) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
        _ ≤ r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r) :=
          mul_le_mul hrlo (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by linarith))
  have hsubset := intervalIntegral.integral_mono_interval hxl hxx (le_refl x)
    (show 0 ≤ᵐ[volume.restrict (Ioc 0 x)]
      (fun r : ℝ => r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact mul_nonneg hr.1.le (Real.exp_pos _).le)
    (orderedWeight_intervalIntegrable_FIN037 κ r0 (s ^ 2) 0 x)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  dsimp [orderedInnerMass_FIN037]
  calc
    (r0 / 4 * Real.exp (-1)) *
        (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
          (s * (1 + s * (r0 - x))))
        = (x - (x - δ)) * (r0 / 4 * Real.exp (-1) *
            Real.exp (-(s ^ 2) * radialU_orad κ r0 x)) := by dsimp [δ]; ring
    _ ≤ _ := hmono
    _ ≤ _ := hsubset

/-- A one-sided exponential kernel has integral at most the reciprocal slope. -/
theorem ordered_exp_kernel_FIN037 {A B k : ℝ} (_hAB : A ≤ B) (hk : 0 < k) :
    (∫ r in A..B, Real.exp (-k * (B - r))) ≤ 1 / k := by
  have hd (r : ℝ) : HasDerivAt (fun t => Real.exp (-k * (B - t)) / k)
      (Real.exp (-k * (B - r))) r := by
    have h1 : HasDerivAt (fun t : ℝ => -k * (B - t)) k r := by
      simpa using (((hasDerivAt_id r).const_sub B).const_mul (-k))
    have h2 := h1.exp.div_const k
    refine h2.congr_deriv ?_
    field_simp [hk.ne']
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (-k * (B - r))) volume A B :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable A B
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
  simp only [sub_self, mul_zero, Real.exp_zero]
  have : 0 ≤ Real.exp (-k * (B - A)) / k := by positivity
  linarith

/-- The full origin contribution is controlled by the derivative of exp(-NU).
This retains the integral from zero; it does not assume FIN036. -/
theorem orderedInnerMass_origin_upper_FIN037 {κ r0 c N : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hN : 0 < N)
    (horigin : ∀ r ∈ Icc 0 (r0 / 2), c * r ≤ -radialDpsi_orad κ r) :
    orderedInnerMass_FIN037 κ r0 N (r0 / 2) ≤
      Real.exp (-N * radialU_orad κ r0 (r0 / 2)) / (N * c) := by
  let f := fun r => -N * radialDpsi_orad κ r *
    Real.exp (-N * radialU_orad κ r0 r)
  have hi : IntervalIntegrable f volume 0 (r0 / 2) := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul (continuous_iff_continuousAt.mpr
      fun r => (dpsi_hasDerivAt_orad r).continuousAt)).mul
        (Real.continuous_exp.comp (continuous_const.mul (orderedU_continuous_FIN037 κ r0)))
  have hFTC : (∫ r in (0 : ℝ)..(r0 / 2), f r) =
      Real.exp (-N * radialU_orad κ r0 (r0 / 2)) -
        Real.exp (-N * radialU_orad κ r0 0) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun r => Real.exp (-N * radialU_orad κ r0 r)) (fun r _ => ?_) hi
    simpa [f, mul_comm] using ((radialU_hasDerivAt_orad (κ := κ) r0 r).const_mul (-N)).exp
  have hmono := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ r0 / 2)
    (orderedWeight_intervalIntegrable_FIN037 κ r0 N 0 (r0 / 2)) (hi.div_const (N * c))
    (fun r hr => by
      apply (le_div_iff₀ (mul_pos hN hc)).2
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (horigin r hr) hN.le) (Real.exp_pos (-N * radialU_orad κ r0 r)).le
      dsimp [f]
      nlinarith)
  rw [intervalIntegral.integral_div, hFTC] at hmono
  exact hmono.trans ((div_le_div_iff_of_pos_right (mul_pos hN hc)).2
    (sub_le_self _ (Real.exp_pos _).le))

/-- Upper bound on the part of the actual mass lying between a and x. -/
theorem orderedInnerMass_well_upper_FIN037 {κ r0 c s x : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 0 < s)
    (hx : x ∈ Icc (r0 / 2) r0)
    (hlow : ∀ t ∈ Icc (r0 / 2) r0, radialDpsi_orad κ t ≤ -c * (r0 - t)) :
    (∫ r in (r0 / 2)..x, r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r)) ≤
      (2 * r0 * Real.exp (c / 2) / c) *
        (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
          (s * (1 + s * (r0 - x)))) := by
  let q := s * (r0 - x)
  let k := c / 2 * s * (1 + q)
  have hq : 0 ≤ q := mul_nonneg hs.le (sub_nonneg.mpr hx.2)
  have hk : 0 < k := by dsimp [k]; positivity
  have hpoint (r : ℝ) (hr : r ∈ Icc (r0 / 2) x) :
      r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r) ≤
        (r0 * Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2)) *
          Real.exp (-k * (x - r)) := by
    let v := s * (x - r)
    have hv : 0 ≤ v := mul_nonneg hs.le (sub_nonneg.mpr hr.2)
    have hanch := orderedU_anchored_lower_FIN037 hlow hr.1 hr.2 hx.2
    have ha : c / 2 * (2 * q * v + v ^ 2) ≤
        s ^ 2 * (radialU_orad κ r0 r - radialU_orad κ r0 x) := by
      convert mul_le_mul_of_nonneg_left hanch (sq_nonneg s) using 1
      dsimp [q, v]
      ring
    have he : -(s ^ 2) * radialU_orad κ r0 r ≤
        -(s ^ 2) * radialU_orad κ r0 x + c / 2 - k * (x - r) := by
      have h1 := mul_nonneg hc.le (sq_nonneg (v - 1 / 2))
      have h2 := mul_nonneg hc.le (mul_nonneg hq hv)
      dsimp [k, v] at *
      nlinarith
    calc
      r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r)
        ≤ r0 * Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2 - k * (x - r)) :=
          mul_le_mul (hr.2.trans hx.2) (Real.exp_le_exp.mpr he)
            (Real.exp_pos _).le hr0.le
      _ = _ := by
        have h : Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2 - k * (x - r)) =
            Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2) * Real.exp (-k * (x - r)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h]; ring
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (-k * (x - r))) volume (r0 / 2) x :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hI := intervalIntegral.integral_mono_on hx.1
    (orderedWeight_intervalIntegrable_FIN037 κ r0 (s ^ 2) (r0 / 2) x)
    (hi.const_mul (r0 * Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2))) hpoint
  rw [intervalIntegral.integral_const_mul] at hI
  calc
    (∫ r in (r0 / 2)..x, r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r))
      ≤ (r0 * Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2)) * (1 / k) :=
        hI.trans (mul_le_mul_of_nonneg_left (ordered_exp_kernel_FIN037 hx.1 hk) (by positivity))
    _ = _ := by
      rw [Real.exp_add]
      dsimp [k, q]
      field_simp

/-- The full actual cumulative mass, with the zero-to-a contribution preserved. -/
theorem orderedInnerMass_upper_FIN037 {κ r0 c s x : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s)
    (hx : x ∈ Icc (r0 / 2) r0)
    (horigin : ∀ r ∈ Icc 0 (r0 / 2), c * r ≤ -radialDpsi_orad κ r)
    (hlow : ∀ t ∈ Icc (r0 / 2) r0, radialDpsi_orad κ t ≤ -c * (r0 - t)) :
    orderedInnerMass_FIN037 κ r0 (s ^ 2) x ≤
      ((1 + r0) / c + 2 * r0 * Real.exp (c / 2) / c) *
        (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
          (s * (1 + s * (r0 - x)))) := by
  have hs0 : 0 < s := by linarith
  have hx0 : 0 ≤ x := (by linarith [hx.1] : (0 : ℝ) ≤ r0 / 2).trans hx.1
  have hq : 0 ≤ s * (r0 - x) := mul_nonneg hs0.le (sub_nonneg.mpr hx.2)
  have hden : 0 < s * (1 + s * (r0 - x)) := by positivity
  have hanch := orderedU_anchored_lower_FIN037 hlow (le_refl (r0 / 2)) hx.1 hx.2
  have hpot : radialU_orad κ r0 x ≤ radialU_orad κ r0 (r0 / 2) := by
    have hdiff : 0 ≤ (r0 / 2 - r0) ^ 2 - (x - r0) ^ 2 := by nlinarith [hx.1, hx.2]
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ c / 2) hdiff
    linarith
  have horig := orderedInnerMass_origin_upper_FIN037 hr0 hc (sq_pos_of_pos hs0) horigin
  have horig' : orderedInnerMass_FIN037 κ r0 (s ^ 2) (r0 / 2) ≤
      ((1 + r0) / c) * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
        (s * (1 + s * (r0 - x)))) := by
    have he : Real.exp (-(s ^ 2) * radialU_orad κ r0 (r0 / 2)) ≤
        Real.exp (-(s ^ 2) * radialU_orad κ r0 x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpot (by nlinarith))
    have hscale : 1 + s * (r0 - x) ≤ s * (1 + r0) := by
      have := mul_nonneg hs0.le hx0
      nlinarith
    calc
      orderedInnerMass_FIN037 κ r0 (s ^ 2) (r0 / 2)
        ≤ Real.exp (-(s ^ 2) * radialU_orad κ r0 x) / (s ^ 2 * c) :=
          horig.trans (div_le_div_of_nonneg_right he (by positivity))
      _ ≤ _ := by
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (by positivity : 0 < s ^ 2 * c) hden).2
        have hmul := mul_le_mul_of_nonneg_left hscale
          (by positivity : 0 ≤ Real.exp (-(s ^ 2) * radialU_orad κ r0 x) * s)
        convert hmul using 1 <;> field_simp [hc.ne']
  have hwell := orderedInnerMass_well_upper_FIN037 hr0 hc hs0 hx hlow
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (orderedWeight_intervalIntegrable_FIN037 κ r0 (s ^ 2) 0 (r0 / 2))
    (orderedWeight_intervalIntegrable_FIN037 κ r0 (s ^ 2) (r0 / 2) x)
  unfold orderedInnerMass_FIN037 at *
  linarith

/-- The reflected one-sided exponential kernel. -/
theorem ordered_exp_kernel_right_FIN037 {A B k : ℝ} (hk : 0 < k) :
    (∫ r in A..B, Real.exp (-k * (r - A))) ≤ 1 / k := by
  have hd (r : ℝ) : HasDerivAt (fun t => -Real.exp (-k * (t - A)) / k)
      (Real.exp (-k * (r - A))) r := by
    have h1 : HasDerivAt (fun t : ℝ => -k * (t - A)) (-k) r := by
      simpa using (((hasDerivAt_id r).sub_const A).const_mul (-k))
    have h2 := h1.exp.neg.div_const k
    refine h2.congr_deriv ?_
    field_simp [hk.ne']
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (-k * (r - A))) volume A B :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable A B
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
  simp only [sub_self, mul_zero, Real.exp_zero]
  have : 0 ≤ Real.exp (-k * (B - A)) / k := by positivity
  have h3 : -Real.exp (-k * (B - A)) / k = -(Real.exp (-k * (B - A)) / k) := neg_div _ _
  have h4 : (-1 : ℝ) / k = -(1 / k) := neg_div _ _
  linarith

/-- Actual resistance on the entire inner well. -/
theorem orderedInnerResistance_upper_FIN037 {κ r0 c s x : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 0 < s)
    (hx : x ∈ Icc (r0 / 2) r0)
    (hlow : ∀ t ∈ Icc (r0 / 2) r0, radialDpsi_orad κ t ≤ -c * (r0 - t)) :
    orderedInnerResistance_FIN037 κ r0 (s ^ 2) x ≤
      (4 / r0 + 8 / (r0 * c)) *
        (Real.exp (s ^ 2 * radialU_orad κ r0 x) /
          (s * (1 + s * (r0 - x)))) := by
  let d := r0 - x
  let q := s * d
  let E := Real.exp (s ^ 2 * radialU_orad κ r0 x)
  have hE : 0 < E := Real.exp_pos _
  have hd : 0 ≤ d := sub_nonneg.mpr hx.2
  have hq : 0 ≤ q := mul_nonneg hs.le hd
  have hden : 0 < s * (1 + q) := by positivity
  have hxpos : 0 < x := by linarith [hx.1]
  have hi : IntervalIntegrable
      (fun r => Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) volume x r0 :=
    (orderedResistance_integrable_FIN035 hr0 hxpos).symm
  have hrec (r : ℝ) (hr : r ∈ Icc x r0) : 1 / r ≤ 2 / r0 := by
    have hrpos : 0 < r := hxpos.trans_le hr.1
    apply (div_le_div_iff₀ hrpos hr0).2
    linarith [hx.1, hr.1]
  have hbound : orderedInnerResistance_FIN037 κ r0 (s ^ 2) x ≤
      (if q ≤ 1 then 4 / r0 else 8 / (r0 * c)) * (E / (s * (1 + q))) := by
    by_cases hq1 : q ≤ 1
    · simp only [hq1, ↓reduceIte]
      have hpoint (r : ℝ) (hr : r ∈ Icc x r0) :
          Real.exp (s ^ 2 * radialU_orad κ r0 r) / r ≤ (2 / r0) * E := by
        have hanch := orderedU_anchored_lower_FIN037 hlow hx.1 hr.1 hr.2
        have hsq : 0 ≤ (x - r0) ^ 2 - (r - r0) ^ 2 := by nlinarith [hr.1, hr.2]
        have hpot : radialU_orad κ r0 r ≤ radialU_orad κ r0 x := by
          have := mul_nonneg (by positivity : 0 ≤ c / 2) hsq
          linarith
        have hexp : Real.exp (s ^ 2 * radialU_orad κ r0 r) ≤ E :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpot (sq_nonneg s))
        calc
          Real.exp (s ^ 2 * radialU_orad κ r0 r) / r
            = Real.exp (s ^ 2 * radialU_orad κ r0 r) * (1 / r) := by ring
          _ ≤ E * (2 / r0) := mul_le_mul hexp (hrec r hr)
            (by have := hxpos.trans_le hr.1; positivity) hE.le
          _ = _ := by ring
      have hI := intervalIntegral.integral_mono_on hx.2 hi
        (intervalIntegrable_const : IntervalIntegrable
          (fun _ : ℝ => 2 / r0 * E) volume x r0) hpoint
      rw [intervalIntegral.integral_const, smul_eq_mul] at hI
      unfold orderedInnerResistance_FIN037
      calc
        (∫ r in x..r0, Real.exp (s ^ 2 * radialU_orad κ r0 r) / r)
          ≤ (r0 - x) * (2 / r0 * E) := hI
        _ ≤ 4 / r0 * (E / (s * (1 + q))) := by
          rw [← mul_div_assoc]
          apply (le_div_iff₀ hden).2
          have hq2 : q * (1 + q) ≤ 2 := by nlinarith
          have hscale := mul_le_mul_of_nonneg_left hq2 (by positivity : 0 ≤ 2 / r0 * E)
          dsimp [q, d] at *
          convert hscale using 1 <;> ring
    · simp only [hq1, ↓reduceIte]
      have hq1' : 1 < q := lt_of_not_ge hq1
      have hdpos : 0 < d := by
        by_contra h
        have := not_lt.mp h
        have : q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le this
        linarith
      let k := c / 2 * s ^ 2 * d
      have hk : 0 < k := by dsimp [k]; positivity
      have hpoint (r : ℝ) (hr : r ∈ Icc x r0) :
          Real.exp (s ^ 2 * radialU_orad κ r0 r) / r ≤
            (2 / r0 * E) * Real.exp (-k * (r - x)) := by
        have hanch := orderedU_anchored_lower_FIN037 hlow hx.1 hr.1 hr.2
        have hsq : d * (r - x) ≤ (x - r0) ^ 2 - (r - r0) ^ 2 := by
          have := mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
          dsimp [d]
          nlinarith
        have hpot : c / 2 * d * (r - x) ≤
            radialU_orad κ r0 x - radialU_orad κ r0 r :=
          (by nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ c / 2)])
        have he : s ^ 2 * radialU_orad κ r0 r ≤
            s ^ 2 * radialU_orad κ r0 x + (-k * (r - x)) := by
          have h := mul_le_mul_of_nonneg_left hpot (sq_nonneg s)
          dsimp [k]
          nlinarith
        have hexp : Real.exp (s ^ 2 * radialU_orad κ r0 r) ≤
            E * Real.exp (-k * (r - x)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr he
        calc
          Real.exp (s ^ 2 * radialU_orad κ r0 r) / r
            = Real.exp (s ^ 2 * radialU_orad κ r0 r) * (1 / r) := by ring
          _ ≤ (E * Real.exp (-k * (r - x))) * (2 / r0) :=
            mul_le_mul hexp (hrec r hr) (by have := hxpos.trans_le hr.1; positivity)
              (by positivity)
          _ = _ := by ring
      have hik : IntervalIntegrable (fun r : ℝ => Real.exp (-k * (r - x))) volume x r0 :=
        (Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const))).intervalIntegrable _ _
      have hI := intervalIntegral.integral_mono_on hx.2 hi
        (hik.const_mul (2 / r0 * E)) hpoint
      rw [intervalIntegral.integral_const_mul] at hI
      unfold orderedInnerResistance_FIN037
      calc
        (∫ r in x..r0, Real.exp (s ^ 2 * radialU_orad κ r0 r) / r)
          ≤ (2 / r0 * E) * (1 / k) :=
            hI.trans (mul_le_mul_of_nonneg_left (ordered_exp_kernel_right_FIN037 hk) (by positivity))
        _ ≤ 8 / (r0 * c) * (E / (s * (1 + q))) := by
          rw [mul_one_div, ← mul_div_assoc]
          apply (div_le_div_iff₀ hk hden).2
          have hscale : 1 + q ≤ 2 * q := by linarith
          have hmul := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 / r0 * E * s)
          convert hmul using 1 <;> dsimp [k, q]
          <;> (field_simp [hr0.ne', hc.ne'] <;> norm_num)
  have hcoef : (if q ≤ 1 then 4 / r0 else 8 / (r0 * c)) ≤
      4 / r0 + 8 / (r0 * c) := by
    split_ifs
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (div_nonneg hE.le hden.le))


/-- The actual partition function is retained in the logarithm. -/
theorem orderedInner_log_bound_FIN037 {A B C s q U L Z : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 ≤ C) (hs : 0 < s) (hq : 0 ≤ q)
    (hZ : 0 < Z) (hZupper : Z ≤ B / s)
    (hLlower : A * (Real.exp (-(s ^ 2) * U) / (s * (1 + q))) ≤ L)
    (hU : s ^ 2 * U ≤ C * q ^ 2) :
    Real.log (1 + Z / L) ≤
      (1 + Real.log (1 + B / A) + C) * (1 + q ^ 2) + Real.log (1 + q) := by
  have hden : 0 < s * (1 + q) := by positivity
  have hLpos : 0 < L := (mul_pos hA (div_pos (Real.exp_pos _) hden)).trans_le hLlower
  have hlow : A * Real.exp (-(s ^ 2) * U) ≤ L * (s * (1 + q)) := by
    have h := (div_le_iff₀ hden).mp (show
      A * Real.exp (-(s ^ 2) * U) / (s * (1 + q)) ≤ L from by
        simpa only [mul_div_assoc] using hLlower)
    exact h
  have hLexp : A ≤ L * s * (1 + q) * Real.exp (s ^ 2 * U) := by
    calc
      A = (A * Real.exp (-(s ^ 2) * U)) * Real.exp (s ^ 2 * U) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      _ ≤ (L * (s * (1 + q))) * Real.exp (s ^ 2 * U) :=
        mul_le_mul_of_nonneg_right hlow (Real.exp_pos _).le
      _ = _ := by ring
  have hZs : Z * s ≤ B := (le_div_iff₀ hs).mp hZupper
  have hcross : Z * A ≤ B * (1 + q) * Real.exp (s ^ 2 * U) * L := by
    have h1 := mul_le_mul_of_nonneg_left hLexp hZ.le
    have h2 := mul_le_mul_of_nonneg_right hZs
      (by positivity : 0 ≤ L * (1 + q) * Real.exp (s ^ 2 * U))
    nlinarith
  have hratio : Z / L ≤ (B / A) * (1 + q) * Real.exp (C * q ^ 2) := by
    calc
      Z / L ≤ (B * (1 + q) * Real.exp (s ^ 2 * U)) / A :=
        (div_le_div_iff₀ hLpos hA).2 hcross
      _ = (B / A) * (1 + q) * Real.exp (s ^ 2 * U) := by ring
      _ ≤ (B / A) * (1 + q) * Real.exp (C * q ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hU) (by positivity)
  have hP : 1 ≤ (1 + q) * Real.exp (C * q ^ 2) := by
    have hCe : 1 ≤ Real.exp (C * q ^ 2) := Real.one_le_exp (mul_nonneg hC (sq_nonneg q))
    nlinarith
  have harg : 1 + Z / L ≤ (1 + B / A) * (1 + q) * Real.exp (C * q ^ 2) := by
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + Z / L) harg
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) (by positivity), Real.log_exp] at hlog
  have hlB : 0 ≤ Real.log (1 + B / A) := Real.log_nonneg (by have := div_pos hB hA; linarith)
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hprod : 0 ≤ Real.log (1 + B / A) * q ^ 2 := mul_nonneg hlB hq2
  nlinarith

/-- After the true logarithm has been bounded, the two exponential factors cancel. -/
theorem orderedInner_hardy_algebra_FIN037 {A R H s q U L J Z : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hs : 0 < s) (hq : 0 ≤ q) (hL : 0 < L) (hJ : 0 ≤ J) (hZ : 0 < Z)
    (hLu : L ≤ A * (Real.exp (-(s ^ 2) * U) / (s * (1 + q))))
    (hJu : J ≤ R * (Real.exp (s ^ 2 * U) / (s * (1 + q))))
    (hlog : Real.log (1 + Z / L) ≤ H * (1 + q ^ 2) + Real.log (1 + q)) :
    L * J ≤ A * R / (s ^ 2 * (1 + q) ^ 2) ∧
      L * J * Real.log (1 + Z / L) ≤ A * R * (H + 1) / s ^ 2 := by
  have hden : 0 < s * (1 + q) := by positivity
  have hprod : L * J ≤ A * R / (s ^ 2 * (1 + q) ^ 2) := by
    calc
      L * J ≤ (A * (Real.exp (-(s ^ 2) * U) / (s * (1 + q)))) *
          (R * (Real.exp (s ^ 2 * U) / (s * (1 + q)))) :=
        mul_le_mul hLu hJu hJ (by positivity)
      _ = _ := by
        rw [← mul_div_assoc, ← mul_div_assoc, div_mul_div_comm]
        have he : Real.exp (-(s ^ 2) * U) * Real.exp (s ^ 2 * U) = 1 := by
          rw [← Real.exp_add]
          simp
        calc
          (A * Real.exp (-(s ^ 2) * U) * (R * Real.exp (s ^ 2 * U))) /
              (s * (1 + q) * (s * (1 + q))) =
              (A * R * (Real.exp (-(s ^ 2) * U) * Real.exp (s ^ 2 * U))) /
                (s ^ 2 * (1 + q) ^ 2) := by
                  field_simp [hs.ne', (show 1 + q ≠ 0 by positivity)]
          _ = _ := by rw [he, mul_one]
  have hlog0 : 0 ≤ Real.log (1 + Z / L) := Real.log_nonneg (by have := div_pos hZ hL; linarith)
  have hlogq : Real.log (1 + q) ≤ q := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + q)
    linarith
  have hlog' : Real.log (1 + Z / L) ≤ H * (1 + q ^ 2) + q :=
    by linarith
  have hpoly : H * (1 + q ^ 2) + q ≤ (H + 1) * (1 + q) ^ 2 := by
    have := mul_nonneg hH hq
    nlinarith [sq_nonneg q]
  refine ⟨hprod, ?_⟩
  calc
    L * J * Real.log (1 + Z / L)
      ≤ (A * R / (s ^ 2 * (1 + q) ^ 2)) *
        ((H + 1) * (1 + q) ^ 2) :=
          mul_le_mul hprod (hlog'.trans hpoly) hlog0 (by positivity)
    _ = A * R * (H + 1) / s ^ 2 := by field_simp


/-- The cumulative mass is the mass of the actual normalized radial law. -/
theorem orderedInnerMass_law_FIN037 {κ r0 N x : ℝ} (hx : 0 ≤ x)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    (orderedRadialLaw_FIN035 κ r0 N).real (Iic x) =
      orderedInnerMass_FIN037 κ r0 N x / orderedRadialZ_FIN035 κ r0 N := by
  rw [orderedRadialLaw_mass_FIN035 hi hZ measurableSet_Iic]
  congr 1
  change (∫ r in Iic x, (Ioi (0 : ℝ)).indicator
    (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) r) = _
  rw [setIntegral_indicator measurableSet_Ioi]
  have hset : Iic x ∩ Ioi (0 : ℝ) = Ioc 0 x := by ext r; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]; tauto
  rw [hset, ← intervalIntegral.integral_of_le hx]
  rfl

/-- The reciprocal of the actual normalized radial density on its positive domain. -/
theorem orderedInner_reciprocal_value_FIN037 {κ r0 N r : ℝ}
    (hr : 0 < r) (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    1 / (orderedRadialWeight_FIN035 κ r0 N r / orderedRadialZ_FIN035 κ r0 N) =
      orderedRadialZ_FIN035 κ r0 N * (Real.exp (N * radialU_orad κ r0 r) / r) := by
  simp only [orderedRadialWeight_FIN035, ite_eq_left hr]
  rw [show -N * radialU_orad κ r0 r = -(N * radialU_orad κ r0 r) by ring,
    Real.exp_neg]
  field_simp [hr.ne', hZ.ne', (Real.exp_pos (N * radialU_orad κ r0 r)).ne']

/-- The actual normalized resistance is integrable between positive endpoints and
equals the partition function times the raw resistance. -/
theorem orderedInner_normalized_resistance_FIN037 {κ r0 N x : ℝ}
    (hx : 0 < x) (hxr : x ≤ r0) (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    IntervalIntegrable
        (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 N r /
          orderedRadialZ_FIN035 κ r0 N)) volume x r0 ∧
      (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N)) =
        orderedRadialZ_FIN035 κ r0 N * orderedInnerResistance_FIN037 κ r0 N x := by
  have heq : EqOn
      (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N))
      (fun r => orderedRadialZ_FIN035 κ r0 N *
        (Real.exp (N * radialU_orad κ r0 r) / r)) (uIcc x r0) := by
    intro r hr
    rw [uIcc_of_le hxr] at hr
    exact orderedInner_reciprocal_value_FIN037 (hx.trans_le hr.1) hZ
  have hi : IntervalIntegrable
      (fun r => orderedRadialZ_FIN035 κ r0 N *
        (Real.exp (N * radialU_orad κ r0 r) / r)) volume x r0 :=
    ((orderedResistance_integrable_FIN035 (κ := κ) (N := N)
      (hx.trans_le hxr) hx).symm).const_mul (orderedRadialZ_FIN035 κ r0 N)
  refine ⟨(intervalIntegrable_congr (fun r hr => heq (uIoc_subset_uIcc hr))).2 hi, ?_⟩
  calc
    (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N)) =
        ∫ r in x..r0, orderedRadialZ_FIN035 κ r0 N *
          (Real.exp (N * radialU_orad κ r0 r) / r) :=
      intervalIntegral.integral_congr heq
    _ = orderedRadialZ_FIN035 κ r0 N * orderedInnerResistance_FIN037 κ r0 N x := by
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- FIN037: two-sided actual inner mass, actual anchored resistance, and the
logarithmic Hardy product for the ordered radial probability. The constants
and the particle threshold depend only on κ; every actual median retains the
FIN035 window and resistance bounds. -/
theorem ordered_inner_well_logarithmic_hardy_product {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧
      r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    ∃ A B R H Q K D N0 : ℝ,
      0 < A ∧ 0 < B ∧ 0 < R ∧ 0 < H ∧ 0 < Q ∧
      0 < K ∧ 0 < D ∧ 0 < N0 ∧
      ∀ N : ℕ+, N0 ≤ (N : ℝ) →
        IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        0 < orderedRadialZ_FIN035 κ r0 (N : ℝ) ∧
        Integrable (orderedRadialWeight_FIN035 κ r0 (N : ℝ)) ∧
        (∀ x ∈ Icc (r0 / 2) r0,
          let q := Real.sqrt (N : ℝ) * (r0 - x)
          let L := orderedInnerMass_FIN037 κ r0 (N : ℝ) x
          let J := orderedInnerResistance_FIN037 κ r0 (N : ℝ) x
          0 < L ∧
          IntervalIntegrable
            (fun r => Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r) volume x r0 ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) =
            L / orderedRadialZ_FIN035 κ r0 (N : ℝ) ∧
          A * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
            (Real.sqrt (N : ℝ) * (1 + q))) ≤ L ∧
          L ≤ B * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
            (Real.sqrt (N : ℝ) * (1 + q))) ∧
          J ≤ R * (Real.exp ((N : ℝ) * radialU_orad κ r0 x) /
            (Real.sqrt (N : ℝ) * (1 + q))) ∧
          L * J ≤ B * R / ((N : ℝ) * (1 + q) ^ 2) ∧
          Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / L) ≤
            H * (1 + q ^ 2) + Real.log (1 + q) ∧
          L * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / L) ≤ Q / (N : ℝ) ∧
          IntervalIntegrable
            (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) volume x r0 ∧
          (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) =
            orderedRadialZ_FIN035 κ r0 (N : ℝ) * J ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) *
            (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) = L * J ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) *
            (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
            Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x)) =
              L * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / L) ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) *
            (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
            Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x)) ≤
              Q / (N : ℝ)) ∧
        (∀ m : ℝ,
          ((1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic m) ∧
            (1 / 2 : ℝ) ≤ (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici m)) →
          |m - r0| ≤ K / Real.sqrt (N : ℝ) ∧
          orderedRadialZ_FIN035 κ r0 (N : ℝ) *
            |∫ r in r0..m, Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r| ≤ D / (N : ℝ)) := by
  obtain ⟨r0, hr0, hroot, huniq, -, -, -, -, -, -, -⟩ := ordered_radial_well_geometry hκ
  obtain ⟨c, C, hc, hcC, horigin, hwell, hquad⟩ := well_estimates_orad hκ hr0 hroot
  obtain ⟨r1, hr1, hroot1, Ln, Bn, M, K, D, N35,
    hLn, hBn, hM, hK, hD, hN35, h35⟩ := ordered_radial_normalization_moments_median hκ
  have heq : r1 = r0 := huniq r1 hr1 hroot1
  subst r1
  have hC : 0 ≤ C := hc.le.trans hcC
  have hlow : ∀ t ∈ Icc (r0 / 2) r0, radialDpsi_orad κ t ≤ -c * (r0 - t) := by
    intro t ht
    obtain ⟨hl, -, hneg, -⟩ := hwell t ht.1
    rcases ht.2.eq_or_lt with h | h
    · subst t
      have hκ0 : κ ≠ 0 := by linarith
      have hf : radialDpsi_orad κ r0 = 0 := by
        unfold radialDpsi_orad
        have : r0 / κ = DGPS.Circle.BesselMoments.besselRatio r0 :=
          (div_eq_iff hκ0).2 (by nlinarith [hroot])
        linarith
      simp [hf]
    · rw [abs_of_neg (hneg h), abs_of_nonpos (by linarith)] at hl
      linarith
  let A := r0 / 4 * Real.exp (-1)
  let B := (1 + r0) / c + 2 * r0 * Real.exp (c / 2) / c
  let R := 4 / r0 + 8 / (r0 * c)
  let H := 1 + Real.log (1 + Bn / A) + C
  let Q := B * R * (H + 1)
  let s0 := max 1 (4 / r0)
  let N0 := max N35 (s0 ^ 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hH : 0 < H := by
    have hl : 0 ≤ Real.log (1 + Bn / A) := Real.log_nonneg (by have := div_pos hBn hA; linarith)
    dsimp [H]
    linarith
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hs01 : 1 ≤ s0 := le_max_left _ _
  have hs00 : 0 < s0 := lt_of_lt_of_le zero_lt_one hs01
  have hN0 : 0 < N0 := hN35.trans_le (le_max_left _ _)
  refine ⟨r0, hr0, hroot, A, B, R, H, Q, K, D, N0,
    hA, hB, hR, hH, hQ, hK, hD, hN0, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hN35' : N35 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  obtain ⟨hprob, hZl, hZu, hmom, hmed⟩ := h35 N hN35'
  have hZ : 0 < orderedRadialZ_FIN035 κ r0 (N : ℝ) :=
    (div_pos hLn (Real.sqrt_pos.mpr hNpos)).trans_le hZl
  have hss : s0 ≤ Real.sqrt (N : ℝ) := by
    have hN' : s0 ^ 2 ≤ (N : ℝ) := (le_max_right _ _).trans hN
    have := Real.sqrt_le_sqrt hN'
    simpa only [Real.sqrt_sq hs00.le] using this
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := hs01.trans hss
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hlarge : 4 ≤ r0 * Real.sqrt (N : ℝ) := by
    have := (div_le_iff₀ hr0).mp ((le_max_right 1 (4 / r0)).trans hss)
    nlinarith
  have hi : Integrable (orderedRadialWeight_FIN035 κ r0 (N : ℝ)) := by
    simpa only [Real.sq_sqrt hNpos.le] using orderedRadialWeight_integrable_FIN035
      hr0 hc hs1 (fun r hr => (hquad r hr).1)
  refine ⟨hprob, hZ, hi, ?_, hmed⟩
  intro x hx
  dsimp only
  let s := Real.sqrt (N : ℝ)
  let q := s * (r0 - x)
  let L := orderedInnerMass_FIN037 κ r0 (N : ℝ) x
  let J := orderedInnerResistance_FIN037 κ r0 (N : ℝ) x
  have hq : 0 ≤ q := mul_nonneg hs.le (sub_nonneg.mpr hx.2)
  have hs2 : s ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hLlN : A * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
      (s * (1 + q))) ≤ L := by
    have h := orderedInnerMass_lower_FIN037 hκ hr0 hroot hs1 hlarge hx
    rwa [Real.sq_sqrt hNpos.le] at h
  have hLuN : L ≤ B * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
      (s * (1 + q))) := by
    have h := orderedInnerMass_upper_FIN037 hr0 hc hs1 hx
      (fun r hr => (horigin r hr).1) hlow
    rwa [Real.sq_sqrt hNpos.le] at h
  have hJuN : J ≤ R * (Real.exp ((N : ℝ) * radialU_orad κ r0 x) /
      (s * (1 + q))) := by
    have h := orderedInnerResistance_upper_FIN037 hr0 hc hs hx hlow
    rwa [Real.sq_sqrt hNpos.le] at h
  have hLl : A * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
      (s * (1 + q))) ≤ L := by rw [hs2]; exact hLlN
  have hLu : L ≤ B * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
      (s * (1 + q))) := by rw [hs2]; exact hLuN
  have hJu : J ≤ R * (Real.exp (s ^ 2 * radialU_orad κ r0 x) /
      (s * (1 + q))) := by rw [hs2]; exact hJuN
  have hLpos : 0 < L := (mul_pos hA (div_pos (Real.exp_pos _) (by positivity))).trans_le hLl
  have hJ : 0 ≤ J := by
    apply intervalIntegral.integral_nonneg hx.2
    intro r hr
    exact div_nonneg (Real.exp_pos _).le (by linarith [hr.1, hx.1])
  have hU : s ^ 2 * radialU_orad κ r0 x ≤ C * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hquad x (by linarith [hx.1])).2 (sq_nonneg s)
    dsimp [q]
    nlinarith
  have hlog := orderedInner_log_bound_FIN037 hA hBn hC hs hq hZ hZu hLl hU
  have hhardy := orderedInner_hardy_algebra_FIN037 hB.le hR.le hH.le hs hq hLpos hJ hZ hLu hJu hlog
  have hxi : IntervalIntegrable
      (fun r => Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r) volume x r0 :=
    (orderedResistance_integrable_FIN035 hr0 (by linarith [hx.1])).symm
  have hxpos : 0 < x := by linarith [hx.1]
  have hlaw := orderedInnerMass_law_FIN037 (x := x) hxpos.le hi hZ
  have hnormalized := orderedInner_normalized_resistance_FIN037 hxpos hx.2 hZ
  have hcancel :
      (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) *
        (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
          orderedRadialZ_FIN035 κ r0 (N : ℝ))) = L * J := by
    rw [hlaw, hnormalized.2]
    change (L / orderedRadialZ_FIN035 κ r0 (N : ℝ)) *
      (orderedRadialZ_FIN035 κ r0 (N : ℝ) * J) = L * J
    field_simp [hZ.ne']
  have hlognormalized :
      Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x)) =
        Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / L) := by
    rw [hlaw]
    congr 1
    change 1 + 1 / (L / orderedRadialZ_FIN035 κ r0 (N : ℝ)) =
      1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / L
    field_simp [hLpos.ne', hZ.ne']
  have hnormalizedproduct :
      (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x) *
        (∫ r in x..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
          orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
        Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic x)) =
          L * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / L) := by
    rw [hcancel, hlognormalized]
  have hrawhardy : L * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / L) ≤
      Q / (N : ℝ) := by
    have h := hhardy.2
    rw [hs2] at h
    exact h
  have hnormalizedhardy := hnormalizedproduct.le.trans hrawhardy
  refine ⟨hLpos, hxi, hlaw, hLlN, hLuN, hJuN, ?_, hlog, hrawhardy,
    hnormalized.1, hnormalized.2, hcancel, hnormalizedproduct, hnormalizedhardy⟩
  have h := hhardy.1
  rw [hs2] at h
  exact h

end DGPS.FiniteN
