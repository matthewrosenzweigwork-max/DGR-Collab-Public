import DGPS.FiniteN.OrderedInnerHardyFIN037

/-!
# FIN038: ordered full right tail logarithmic Hardy product

For the ordered radial law with weight `r e^{-N U(r)}` on `(0, ∞)` we prove, uniformly in
`x ≥ r0` (including `x → ∞`), that the actual tail mass is comparable to
`x e^{-N U(x)} / (√N (1 + q))`, that the actual resistance integral from `r0` to `x` is
bounded by `e^{N U(x)} / (x √N (1 + q))`, and that the tail Hardy product with the
logarithm is bounded by `Q / N`.
-/

open MeasureTheory Set Filter
open scoped Interval

namespace DGPS.FiniteN

/-- Actual unnormalized right tail mass, with the radial Jacobian retained. -/
noncomputable def orderedTailMass_FIN038 (κ r0 N x : ℝ) : ℝ :=
  ∫ r in Ioi x, r * Real.exp (-N * radialU_orad κ r0 r)

/-- Actual unnormalized resistance from the minimum out to x. -/
noncomputable def orderedTailResistance_FIN038 (κ r0 N x : ℝ) : ℝ :=
  ∫ r in r0..x, Real.exp (N * radialU_orad κ r0 r) / r

/-- Anchored lower comparison on the outer side of the well. -/
theorem orderedU_tail_lower_FIN038 {κ r0 c r x : ℝ}
    (hlow : ∀ t, r0 ≤ t → c * (t - r0) ≤ radialDpsi_orad κ t)
    (hr : r0 ≤ r) (hrx : r ≤ x) :
    c / 2 * ((x - r0) ^ 2 - (r - r0) ^ 2) ≤
      radialU_orad κ r0 x - radialU_orad κ r0 r := by
  have hm := monotoneOn_of_hasDerivAt_orad (convex_Ici r0)
    (radialU_sub_quad_hasDerivAt_orad (κ := κ) r0 (c / 2))
    (fun t ht => by have := hlow t ht; linarith)
  have h := hm (mem_Ici.mpr hr) (mem_Ici.mpr (hr.trans hrx)) hrx
  dsimp only at h
  linarith

/-- Anchored upper comparison on the outer side of the well. -/
theorem orderedU_tail_upper_FIN038 {κ r0 r x : ℝ}
    (hup : ∀ t, r0 ≤ t → radialDpsi_orad κ t ≤ (t - r0) / 2)
    (hr : r0 ≤ r) (hrx : r ≤ x) :
    radialU_orad κ r0 x - radialU_orad κ r0 r ≤
      (1 / 4 : ℝ) * ((x - r0) ^ 2 - (r - r0) ^ 2) := by
  have ha := antitoneOn_of_hasDerivAt_orad (convex_Ici r0)
    (radialU_sub_quad_hasDerivAt_orad (κ := κ) r0 (1 / 4))
    (fun t ht => by have := hup t ht; linarith)
  have h := ha (mem_Ici.mpr hr) (mem_Ici.mpr (hr.trans hrx)) hrx
  dsimp only at h
  linarith

theorem orderedTail_dpsi_upper_FIN038 {κ r0 t : ℝ} (hκ : 2 < κ) (hr0 : 0 < r0)
    (hroot : r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0) (ht : r0 ≤ t) :
    radialDpsi_orad κ t ≤ (t - r0) / 2 := by
  have hf0 : radialDpsi_orad κ r0 = 0 := by
    unfold radialDpsi_orad
    have hκ0 : κ ≠ 0 := by linarith
    have : r0 / κ = DGPS.Circle.BesselMoments.besselRatio r0 := by
      apply (div_eq_iff hκ0).2
      nlinarith [hroot]
    linarith
  have h := dpsi_lipschitz_orad hκ hr0.le (hr0.le.trans ht)
  rw [hf0, sub_zero, abs_of_nonneg (show 0 ≤ t - r0 by linarith)] at h
  have := (abs_le.mp h).2
  linarith

/-- The short right window has uniformly bounded potential increase in scaled coordinates. -/
theorem orderedTail_window_FIN038 {κ r0 s x : ℝ}
    (hup : ∀ t, r0 ≤ t → radialDpsi_orad κ t ≤ (t - r0) / 2)
    (hs : 1 ≤ s) (hx : r0 ≤ x) :
    let δ := 1 / (s * (1 + s * (x - r0)))
    0 < δ ∧ ∀ r ∈ Icc x (x + δ),
        s ^ 2 * (radialU_orad κ r0 r - radialU_orad κ r0 x) ≤ 1 := by
  dsimp only
  let d := x - r0
  let δ := 1 / (s * (1 + s * d))
  have hs0 : 0 < s := by linarith
  have hd : 0 ≤ d := sub_nonneg.mpr hx
  have hq : 0 ≤ s * d := mul_nonneg hs0.le hd
  have hden : 0 < s * (1 + s * d) := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have he : s * (1 + s * d) * δ = 1 := mul_one_div_cancel hden.ne'
  have hsδ : s * δ ≤ 1 := by
    have : 0 ≤ s * d * (s * δ) := mul_nonneg hq (mul_nonneg hs0.le hδ.le)
    nlinarith [he]
  have hqδ : (s * d) * (s * δ) ≤ 1 := by nlinarith [he]
  refine ⟨hδ, ?_⟩
  intro r hr
  have hcomp := orderedU_tail_upper_FIN038 (κ := κ) hup hx hr.1
  have ht : 0 ≤ r - x := sub_nonneg.mpr hr.1
  have htδ : r - x ≤ δ := by linarith [hr.2]
  have hpoly : (r - r0) ^ 2 - (x - r0) ^ 2 ≤ 2 * d * δ + δ ^ 2 := by
    have hprod : d * (r - x) ≤ d * δ := mul_le_mul_of_nonneg_left htδ hd
    have hsqr : (r - x) ^ 2 ≤ δ ^ 2 := (sq_le_sq₀ ht hδ.le).2 htδ
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

theorem orderedTail_weight_integrableOn_FIN038 {κ r0 N x : ℝ} (hx : 0 < x)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N)) :
    IntegrableOn (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) (Ioi x) := by
  refine hi.integrableOn.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have : 0 < r := hx.trans hr
  simp only [orderedRadialWeight_FIN035, this, ↓reduceIte]

theorem orderedTail_weight_intervalIntegrable_FIN038 (κ r0 N a b : ℝ) :
    IntervalIntegrable (fun r => r * Real.exp (-N * radialU_orad κ r0 r)) volume a b :=
  orderedWeight_intervalIntegrable_FIN037 κ r0 N a b

/-- The tail has the reciprocal-slope mass of the exponential majorant. -/
theorem orderedTail_upper_FIN038 {κ r0 c s x : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s) (hx : r0 ≤ x)
    (hlow : ∀ t, r0 ≤ t → c * (t - r0) ≤ radialDpsi_orad κ t)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 (s ^ 2))) :
    orderedTailMass_FIN038 κ r0 (s ^ 2) x ≤
      (Real.exp (c / 2) * (2 / c + 4 / (c ^ 2 * r0))) *
        (x * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) / (s * (1 + s * (x - r0))))) := by
  have hs0 : 0 < s := by linarith
  have hxpos : 0 < x := hr0.trans_le hx
  let q := s * (x - r0)
  let w := s * (1 + q)
  let k := c / 2 * w
  let E := Real.exp (-(s ^ 2) * radialU_orad κ r0 x)
  have hq : 0 ≤ q := mul_nonneg hs0.le (sub_nonneg.mpr hx)
  have hw1 : 1 ≤ w := by
    have : 0 ≤ s * q := mul_nonneg hs0.le hq
    dsimp [w]; nlinarith
  have hw : 0 < w := by linarith
  have hk : 0 < k := by dsimp [k]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hpoint (r : ℝ) (hr : x ≤ r) :
      r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r) ≤
        (E * Real.exp (c / 2)) * (r * Real.exp (-k * (r - x))) := by
    let v := s * (r - x)
    have hv : 0 ≤ v := mul_nonneg hs0.le (sub_nonneg.mpr hr)
    have hanch := orderedU_tail_lower_FIN038 hlow hx hr
    have ha : c / 2 * (2 * q * v + v ^ 2) ≤
        s ^ 2 * (radialU_orad κ r0 r - radialU_orad κ r0 x) := by
      convert mul_le_mul_of_nonneg_left hanch (sq_nonneg s) using 1
      dsimp [q, v]
      ring
    have he : -(s ^ 2) * radialU_orad κ r0 r ≤
        -(s ^ 2) * radialU_orad κ r0 x + c / 2 - k * (r - x) := by
      have h1 := mul_nonneg hc.le (sq_nonneg (v - 1 / 2))
      have h2 := mul_nonneg hc.le (mul_nonneg hq hv)
      dsimp [k, w, v] at *
      nlinarith
    have hrpos : 0 ≤ r := hxpos.le.trans hr
    calc
      r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r)
        ≤ r * Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2 - k * (r - x)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hrpos
      _ = _ := by
        have h : Real.exp (-(s ^ 2) * radialU_orad κ r0 x + c / 2 - k * (r - x)) =
            E * Real.exp (c / 2) * Real.exp (-k * (r - x)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [h]; ring
  -- antiderivative of r * exp(-k (r-x))
  have hd (r : ℝ) : HasDerivAt (fun t => -(t / k + 1 / k ^ 2) * Real.exp (-k * (t - x)))
      (r * Real.exp (-k * (r - x))) r := by
    have h1 : HasDerivAt (fun t : ℝ => -k * (t - x)) (-k) r := by
      simpa using (((hasDerivAt_id r).sub_const x).const_mul (-k))
    have h2 : HasDerivAt (fun t : ℝ => -(t / k + 1 / k ^ 2)) (-(1 / k)) r := by
      exact ((((hasDerivAt_id r).div_const k).add_const (1 / k ^ 2)).neg)
    have h3 := h2.mul h1.exp
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hbound (b : ℝ) (hb : x ≤ b) :
      (∫ r in x..b, r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r)) ≤
        E * Real.exp (c / 2) * (x / k + 1 / k ^ 2) := by
    have hgi : IntervalIntegrable (fun r : ℝ => r * Real.exp (-k * (r - x))) volume x b :=
      (by fun_prop : Continuous fun r : ℝ => r * Real.exp (-k * (r - x))).intervalIntegrable x b
    have hI := intervalIntegral.integral_mono_on hb
      (orderedTail_weight_intervalIntegrable_FIN038 κ r0 (s ^ 2) x b)
      (hgi.const_mul (E * Real.exp (c / 2))) (fun r hr => hpoint r hr.1)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hgi] at hI
    refine hI.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    have : 0 ≤ (b / k + 1 / k ^ 2) * Real.exp (-k * (b - x)) := by
      have : 0 ≤ b := hxpos.le.trans hb
      positivity
    linarith
  have hfi := orderedTail_weight_integrableOn_FIN038 (N := s ^ 2) hxpos hi
  have hlim := intervalIntegral_tendsto_integral_Ioi x hfi (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hT : orderedTailMass_FIN038 κ r0 (s ^ 2) x ≤
      E * Real.exp (c / 2) * (x / k + 1 / k ^ 2) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop x] with b hb
    exact hbound b hb
  refine hT.trans ?_
  have hxr : 1 ≤ x / r0 := (one_le_div hr0).2 hx
  have h1w : 1 / w ^ 2 ≤ 1 / w := by
    apply one_div_le_one_div_of_le hw
    nlinarith
  have hfin : x / k + 1 / k ^ 2 ≤ (2 / c + 4 / (c ^ 2 * r0)) * (x * (1 / w)) := by
    have e1 : x / k = 2 / c * (x * (1 / w)) := by dsimp [k]; field_simp
    have e2 : 1 / k ^ 2 = 4 / c ^ 2 * (1 / w ^ 2) := by dsimp [k]; field_simp; norm_num
    have e3 : 4 / c ^ 2 * (1 / w ^ 2) ≤ 4 / (c ^ 2 * r0) * (x * (1 / w)) := by
      calc
        4 / c ^ 2 * (1 / w ^ 2) ≤ 4 / c ^ 2 * (1 / w * (x / r0)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc 1 / w ^ 2 ≤ 1 / w := h1w
            _ = 1 / w * 1 := by ring
            _ ≤ 1 / w * (x / r0) := mul_le_mul_of_nonneg_left hxr (by positivity)
        _ = 4 / (c ^ 2 * r0) * (x * (1 / w)) := by field_simp
    have : 0 ≤ 4 / (c ^ 2 * r0) * (x * (1 / w)) := by positivity
    rw [e1, e2]
    nlinarith
  calc
    E * Real.exp (c / 2) * (x / k + 1 / k ^ 2)
      ≤ E * Real.exp (c / 2) * ((2 / c + 4 / (c ^ 2 * r0)) * (x * (1 / w))) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = _ := by dsimp [E, w, q]; field_simp
/-- The local window yields the lower bound for the actual tail mass. -/
theorem orderedTail_lower_FIN038 {κ r0 s x : ℝ}
    (hr0 : 0 < r0) (hs : 1 ≤ s) (hx : r0 ≤ x)
    (hup : ∀ t, r0 ≤ t → radialDpsi_orad κ t ≤ (t - r0) / 2)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 (s ^ 2))) :
    Real.exp (-1) *
        (x * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) / (s * (1 + s * (x - r0))))) ≤
      orderedTailMass_FIN038 κ r0 (s ^ 2) x := by
  have hxpos : 0 < x := hr0.trans_le hx
  let δ := 1 / (s * (1 + s * (x - r0)))
  obtain ⟨hδ, hwindow⟩ := orderedTail_window_FIN038 (κ := κ) hup hs hx
  change 0 < δ at hδ
  have hxx : x ≤ x + δ := by linarith
  have hmono := intervalIntegral.integral_mono_on hxx
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => x * Real.exp (-1) *
        Real.exp (-(s ^ 2) * radialU_orad κ r0 x)) volume x (x + δ))
    (orderedTail_weight_intervalIntegrable_FIN038 κ r0 (s ^ 2) x (x + δ)) (fun r hr => by
      have he : -(s ^ 2) * radialU_orad κ r0 x - 1 ≤
          -(s ^ 2) * radialU_orad κ r0 r := by
        have := hwindow r hr
        linarith
      calc
        x * Real.exp (-1) * Real.exp (-(s ^ 2) * radialU_orad κ r0 x)
          = x * Real.exp (-(s ^ 2) * radialU_orad κ r0 x - 1) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            ring
        _ ≤ r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r) :=
          mul_le_mul hr.1 (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by linarith [hr.1]))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfi := orderedTail_weight_integrableOn_FIN038 (N := s ^ 2) hxpos hi
  have hsubset : (∫ r in x..(x + δ), r * Real.exp (-(s ^ 2) * radialU_orad κ r0 r)) ≤
      orderedTailMass_FIN038 κ r0 (s ^ 2) x := by
    rw [intervalIntegral.integral_of_le hxx]
    unfold orderedTailMass_FIN038
    refine setIntegral_mono_set hfi ?_ (Ioc_subset_Ioi_self.eventuallyLE)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have : 0 < r := hxpos.trans hr
    positivity
  calc
    Real.exp (-1) *
        (x * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) / (s * (1 + s * (x - r0)))))
        = (x + δ - x) * (x * Real.exp (-1) *
            Real.exp (-(s ^ 2) * radialU_orad κ r0 x)) := by dsimp [δ]; ring
    _ ≤ _ := hmono
    _ ≤ _ := hsubset
theorem orderedTail_resistance_outer_FIN038 {κ r0 c s x : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 0 < s) (hx : r0 ≤ x)
    (hlow : ∀ t, r0 ≤ t → c * (t - r0) ≤ radialDpsi_orad κ t) :
    (∫ r in ((r0 + x) / 2)..x, Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) ≤
      (2 * (1 + 4 / c)) *
        (Real.exp (s ^ 2 * radialU_orad κ r0 x) / (x * (s * (1 + s * (x - r0))))) := by
  have hxpos : 0 < x := hr0.trans_le hx
  let d := x - r0
  let q := s * d
  let m := (r0 + x) / 2
  let E := Real.exp (s ^ 2 * radialU_orad κ r0 x)
  have hd : 0 ≤ d := sub_nonneg.mpr hx
  have hq : 0 ≤ q := mul_nonneg hs.le hd
  have hE : 0 < E := Real.exp_pos _
  have hmx : m ≤ x := by dsimp [m]; linarith
  have hrm : r0 ≤ m := by dsimp [m]; linarith
  have hmpos : 0 < m := hr0.trans_le hrm
  have hden : 0 < x * (s * (1 + q)) := by positivity
  have hi : IntervalIntegrable
      (fun r => Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) volume m x :=
    ((orderedResistance_integrable_FIN035 (N := s ^ 2) (κ := κ) hr0 hmpos).symm).trans
      (orderedResistance_integrable_FIN035 (N := s ^ 2) (κ := κ) hr0 hxpos)
  have hrec (r : ℝ) (hr : r ∈ Icc m x) : 1 / r ≤ 2 / x := by
    have hrpos : 0 < r := hmpos.trans_le hr.1
    apply (div_le_div_iff₀ hrpos hxpos).2
    have : x ≤ 2 * m := by dsimp [m]; linarith
    linarith [hr.1]
  have hanch (r : ℝ) (hr : r ∈ Icc m x) := orderedU_tail_lower_FIN038 hlow (hrm.trans hr.1) hr.2
  by_cases hq1 : q ≤ 1
  · have hpoint (r : ℝ) (hr : r ∈ Icc m x) :
        Real.exp (s ^ 2 * radialU_orad κ r0 r) / r ≤ (2 / x) * E := by
      have ha := hanch r hr
      have hsq : 0 ≤ (x - r0) ^ 2 - (r - r0) ^ 2 := by nlinarith [hr.1, hr.2]
      have hpot : radialU_orad κ r0 r ≤ radialU_orad κ r0 x := by
        have := mul_nonneg (by positivity : 0 ≤ c / 2) hsq
        linarith
      have hexp : Real.exp (s ^ 2 * radialU_orad κ r0 r) ≤ E :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpot (sq_nonneg s))
      calc
        Real.exp (s ^ 2 * radialU_orad κ r0 r) / r
          = Real.exp (s ^ 2 * radialU_orad κ r0 r) * (1 / r) := by ring
        _ ≤ E * (2 / x) := mul_le_mul hexp (hrec r hr)
          (by have := hmpos.trans_le hr.1; positivity) hE.le
        _ = _ := by ring
    have hI := intervalIntegral.integral_mono_on hmx hi
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => 2 / x * E) volume m x) hpoint
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    refine hI.trans ?_
    have hxm : x - m = q / (2 * s) := by dsimp [m, q, d]; field_simp; ring
    rw [hxm]
    have h2 : q * (1 + q) ≤ 2 := by nlinarith
    have hc4 : 0 ≤ 4 / c := by positivity
    calc
      q / (2 * s) * (2 / x * E) = E * (q * (1 + q)) / (x * (s * (1 + q))) := by
        field_simp
      _ ≤ E * 2 / (x * (s * (1 + q))) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hE.le) hden.le
      _ ≤ _ := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hden.le
        nlinarith
  · have hq1' : 1 < q := lt_of_not_ge hq1
    have hdpos : 0 < d := by
      by_contra h
      have := not_lt.mp h
      have : q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le this
      linarith
    let k := c / 2 * s * q
    have hk : 0 < k := by dsimp [k]; positivity
    have hpoint (r : ℝ) (hr : r ∈ Icc m x) :
        Real.exp (s ^ 2 * radialU_orad κ r0 r) / r ≤
          (2 / x * E) * Real.exp (-k * (x - r)) := by
      have ha := hanch r hr
      have hr1 : r0 ≤ r := hrm.trans hr.1
      have hsq : d * (x - r) ≤ (x - r0) ^ 2 - (r - r0) ^ 2 := by
        have := mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hr1)
        dsimp [d]
        nlinarith
      have hpot : c / 2 * d * (x - r) ≤
          radialU_orad κ r0 x - radialU_orad κ r0 r :=
        (by nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ c / 2)])
      have he : s ^ 2 * radialU_orad κ r0 r ≤
          s ^ 2 * radialU_orad κ r0 x + (-k * (x - r)) := by
        have h := mul_le_mul_of_nonneg_left hpot (sq_nonneg s)
        dsimp [k, q]
        nlinarith
      have hexp : Real.exp (s ^ 2 * radialU_orad κ r0 r) ≤ E * Real.exp (-k * (x - r)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr he
      calc
        Real.exp (s ^ 2 * radialU_orad κ r0 r) / r
          = Real.exp (s ^ 2 * radialU_orad κ r0 r) * (1 / r) := by ring
        _ ≤ (E * Real.exp (-k * (x - r))) * (2 / x) :=
          mul_le_mul hexp (hrec r hr) (by have := hmpos.trans_le hr.1; positivity)
            (by positivity)
        _ = _ := by ring
    have hik : IntervalIntegrable (fun r : ℝ => Real.exp (-k * (x - r))) volume m x :=
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_const.sub continuous_id))).intervalIntegrable _ _
    have hI := intervalIntegral.integral_mono_on hmx hi
      (hik.const_mul (2 / x * E)) hpoint
    rw [intervalIntegral.integral_const_mul] at hI
    refine hI.trans ?_
    calc
      2 / x * E * (∫ r in m..x, Real.exp (-k * (x - r))) ≤ (2 / x * E) * (1 / k) :=
        mul_le_mul_of_nonneg_left (ordered_exp_kernel_FIN037 hmx hk) (by positivity)
      _ = E * (4 / c) / (x * (s * q)) := by dsimp [k]; field_simp; norm_num
      _ ≤ E * (4 / c) * 2 / (x * (s * (1 + q))) := by
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (by positivity) hden).2
        have : (1 + q) ≤ 2 * q := by linarith
        have hmul := mul_le_mul_of_nonneg_left this
          (by positivity : 0 ≤ E * (4 / c) * (x * s))
        convert hmul using 1 <;> ring
      _ ≤ 2 * (1 + 4 / c) * (E / (x * (s * (1 + q)))) := by
        rw [show 2 * (1 + 4 / c) * (E / (x * (s * (1 + q)))) =
          (2 * (1 + 4 / c) * E) / (x * (s * (1 + q))) by ring]
        apply div_le_div_of_nonneg_right _ hden.le
        nlinarith
/-- A cubic polynomial is dominated by a Gaussian factor. -/
theorem orderedTail_poly_gauss_FIN038 {a q : ℝ} (ha : 0 < a) :
    (1 + q) ^ 3 ≤ 4 * (1 + 1 / a + 2 / a ^ 2) * Real.exp (a * q ^ 2) := by
  have hy : 0 ≤ a * q ^ 2 := by positivity
  have hexp := Real.quadratic_le_exp_of_nonneg hy
  have h1 : (1 + q) ^ 3 ≤ 4 * (1 + q ^ 2 + q ^ 4) := by
    nlinarith [sq_nonneg (q ^ 2 - q), sq_nonneg (q - 1), sq_nonneg q, sq_nonneg (q ^ 2)]
  have hp : 0 ≤ 1 / a := by positivity
  have hp2 : 0 ≤ 2 / a ^ 2 := by positivity
  have e1 : 1 / a * (a * q ^ 2) = q ^ 2 := by field_simp
  have e2 : 2 / a ^ 2 * ((a * q ^ 2) ^ 2 / 2) = q ^ 4 := by field_simp
  have h2 : 1 + q ^ 2 + q ^ 4 ≤
      (1 + 1 / a + 2 / a ^ 2) * (1 + a * q ^ 2 + (a * q ^ 2) ^ 2 / 2) := by
    have t4 : 0 ≤ (a * q ^ 2) ^ 2 / 2 := by positivity
    nlinarith [mul_nonneg hp t4, mul_nonneg hp2 hy, mul_nonneg hp hy, hp, hp2, hy, t4]
  have hM : 0 ≤ 1 + 1 / a + 2 / a ^ 2 := by positivity
  calc
    (1 + q) ^ 3 ≤ 4 * (1 + q ^ 2 + q ^ 4) := h1
    _ ≤ 4 * ((1 + 1 / a + 2 / a ^ 2) * (1 + a * q ^ 2 + (a * q ^ 2) ^ 2 / 2)) := by linarith
    _ ≤ 4 * ((1 + 1 / a + 2 / a ^ 2) * Real.exp (a * q ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hM) (by norm_num)
    _ = _ := by ring

theorem orderedTail_resistance_inner_FIN038 {κ r0 c s x : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s) (hx : r0 ≤ x)
    (hlow : ∀ t, r0 ≤ t → c * (t - r0) ≤ radialDpsi_orad κ t) :
    (∫ r in r0..((r0 + x) / 2), Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) ≤
      (2 * (r0 + 1) * (1 + 1 / (3 * c / 8) + 2 / (3 * c / 8) ^ 2) / r0) *
        (Real.exp (s ^ 2 * radialU_orad κ r0 x) / (x * (s * (1 + s * (x - r0))))) := by
  have hs0 : 0 < s := by linarith
  have hxpos : 0 < x := hr0.trans_le hx
  let d := x - r0
  let q := s * d
  let m := (r0 + x) / 2
  let a := 3 * c / 8
  let M := 1 + 1 / a + 2 / a ^ 2
  let E := Real.exp (s ^ 2 * radialU_orad κ r0 x)
  have ha : 0 < a := by dsimp [a]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hd : 0 ≤ d := sub_nonneg.mpr hx
  have hq : 0 ≤ q := mul_nonneg hs0.le hd
  have hE : 0 < E := Real.exp_pos _
  have hrm : r0 ≤ m := by dsimp [m]; linarith
  have hmx : m ≤ x := by dsimp [m]; linarith
  have hG : 0 < Real.exp (a * q ^ 2) := Real.exp_pos _
  have hpoint (r : ℝ) (hr : r ∈ Icc r0 m) :
      Real.exp (s ^ 2 * radialU_orad κ r0 r) / r ≤ (E * Real.exp (-(a * q ^ 2))) / r0 := by
    have ha1 := orderedU_tail_lower_FIN038 hlow hr.1 (hr.2.trans hmx)
    have hrd : r - r0 ≤ d / 2 := by dsimp [d, m] at *; linarith [hr.2]
    have hrd0 : 0 ≤ r - r0 := sub_nonneg.mpr hr.1
    have hsq : (r - r0) ^ 2 ≤ d ^ 2 / 4 := by nlinarith
    have hpot : c / 2 * (3 / 4 * d ^ 2) ≤ radialU_orad κ r0 x - radialU_orad κ r0 r := by
      have : c / 2 * ((x - r0) ^ 2 - (r - r0) ^ 2) ≥ c / 2 * (3 / 4 * d ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [d]; nlinarith
      linarith
    have he : s ^ 2 * radialU_orad κ r0 r ≤ s ^ 2 * radialU_orad κ r0 x + (-(a * q ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hpot (sq_nonneg s)
      dsimp [a, q]
      nlinarith
    have hexp : Real.exp (s ^ 2 * radialU_orad κ r0 r) ≤ E * Real.exp (-(a * q ^ 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr he
    have hrpos : 0 < r := hr0.trans_le hr.1
    calc
      Real.exp (s ^ 2 * radialU_orad κ r0 r) / r
        ≤ (E * Real.exp (-(a * q ^ 2))) / r :=
          div_le_div_of_nonneg_right hexp hrpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hr0 hr.1
  have hi : IntervalIntegrable
      (fun r => Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) volume r0 m :=
    orderedResistance_integrable_FIN035 (N := s ^ 2) (κ := κ) hr0 (hr0.trans_le hrm)
  have hI := intervalIntegral.integral_mono_on hrm hi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (E * Real.exp (-(a * q ^ 2))) / r0) volume r0 m) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI
  refine hI.trans ?_
  -- polynomial domination
  have hxq : x ≤ r0 + q := by
    have : d ≤ q := by
      dsimp [q]; nlinarith
    dsimp [d] at this; linarith
  have hpoly := orderedTail_poly_gauss_FIN038 ha (q := q)
  have hkey : x * (1 + q) * q ≤ 4 * M * (r0 + 1) * Real.exp (a * q ^ 2) := by
    have h1 : x * (1 + q) * q ≤ (r0 + 1) * (1 + q) ^ 3 := by
      have hxq' : x ≤ (r0 + 1) * (1 + q) := by nlinarith
      have : x * (1 + q) * q ≤ ((r0 + 1) * (1 + q)) * (1 + q) * (1 + q) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hxq' (by positivity)) (by linarith)
          hq (by positivity)
      nlinarith
    calc
      x * (1 + q) * q ≤ (r0 + 1) * (1 + q) ^ 3 := h1
      _ ≤ (r0 + 1) * (4 * M * Real.exp (a * q ^ 2)) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  have hmr : m - r0 = q / (2 * s) := by dsimp [m, q, d]; field_simp; ring
  rw [hmr]
  have hexpneg : Real.exp (-(a * q ^ 2)) = 1 / Real.exp (a * q ^ 2) := by
    rw [Real.exp_neg]; ring
  rw [hexpneg]
  have hden : 0 < x * (s * (1 + q)) := by positivity
  have hR : 2 * (r0 + 1) * M / r0 * (E / (x * (s * (1 + q)))) =
      E / (r0 * s) * (2 * (r0 + 1) * M / (x * (1 + q))) := by
    field_simp
  have hL : q / (2 * s) * (E * (1 / Real.exp (a * q ^ 2)) / r0) =
      E / (r0 * s) * (q / (2 * Real.exp (a * q ^ 2))) := by
    field_simp
  change q / (2 * s) * (E * (1 / Real.exp (a * q ^ 2)) / r0) ≤
    2 * (r0 + 1) * M / r0 * (E / (x * (s * (1 + q))))
  rw [hR, hL]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey]

/-- Actual resistance from the minimum to x, split at the midpoint. -/
theorem orderedTailResistance_upper_FIN038 {κ r0 c s x : ℝ}
    (hr0 : 0 < r0) (hc : 0 < c) (hs : 1 ≤ s) (hx : r0 ≤ x)
    (hlow : ∀ t, r0 ≤ t → c * (t - r0) ≤ radialDpsi_orad κ t) :
    orderedTailResistance_FIN038 κ r0 (s ^ 2) x ≤
      ((2 * (r0 + 1) * (1 + 1 / (3 * c / 8) + 2 / (3 * c / 8) ^ 2) / r0) +
          2 * (1 + 4 / c)) *
        (Real.exp (s ^ 2 * radialU_orad κ r0 x) / (x * (s * (1 + s * (x - r0))))) := by
  have hxpos : 0 < x := hr0.trans_le hx
  have hrm : r0 ≤ (r0 + x) / 2 := by linarith
  have hmpos : 0 < (r0 + x) / 2 := hr0.trans_le hrm
  have h1 : IntervalIntegrable
      (fun r => Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) volume r0 ((r0 + x) / 2) :=
    orderedResistance_integrable_FIN035 (N := s ^ 2) (κ := κ) hr0 hmpos
  have h2 : IntervalIntegrable
      (fun r => Real.exp (s ^ 2 * radialU_orad κ r0 r) / r) volume ((r0 + x) / 2) x :=
    h1.symm.trans (orderedResistance_integrable_FIN035 (N := s ^ 2) (κ := κ) hr0 hxpos)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hin := orderedTail_resistance_inner_FIN038 (κ := κ) hr0 hc hs hx hlow
  have hs0 : (0:ℝ) < s := by linarith
  have hout := orderedTail_resistance_outer_FIN038 (κ := κ) (s := s) hr0 hc hs0 hx hlow
  unfold orderedTailResistance_FIN038
  rw [← hsplit, add_mul]
  exact add_le_add hin hout

/-- The tail mass is the mass of the actual normalized radial law on `Ici x`. -/
theorem orderedTailMass_law_FIN038 {κ r0 N x : ℝ} (hx : 0 < x)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    (orderedRadialLaw_FIN035 κ r0 N).real (Ici x) =
      orderedTailMass_FIN038 κ r0 N x / orderedRadialZ_FIN035 κ r0 N := by
  rw [orderedRadialLaw_mass_FIN035 hi hZ measurableSet_Ici]
  congr 1
  rw [integral_Ici_eq_integral_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
    have : 0 < r := hx.trans hr
    simp only [orderedRadialWeight_FIN035, this, ↓reduceIte])

/-- The actual normalized resistance between r0 and x equals the partition function
times the raw resistance. -/
theorem orderedTail_normalized_resistance_FIN038 {κ r0 N x : ℝ}
    (hr0 : 0 < r0) (hx : r0 ≤ x) (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    IntervalIntegrable
        (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 N r /
          orderedRadialZ_FIN035 κ r0 N)) volume r0 x ∧
      (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N)) =
        orderedRadialZ_FIN035 κ r0 N * orderedTailResistance_FIN038 κ r0 N x := by
  have heq : EqOn
      (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N))
      (fun r => orderedRadialZ_FIN035 κ r0 N *
        (Real.exp (N * radialU_orad κ r0 r) / r)) (uIcc r0 x) := by
    intro r hr
    rw [uIcc_of_le hx] at hr
    exact orderedInner_reciprocal_value_FIN037 (hr0.trans_le hr.1) hZ
  have hi : IntervalIntegrable
      (fun r => orderedRadialZ_FIN035 κ r0 N *
        (Real.exp (N * radialU_orad κ r0 r) / r)) volume r0 x :=
    (orderedResistance_integrable_FIN035 (κ := κ) (N := N)
      hr0 (hr0.trans_le hx)).const_mul (orderedRadialZ_FIN035 κ r0 N)
  refine ⟨(intervalIntegrable_congr (fun r hr => heq (uIoc_subset_uIcc hr))).2 hi, ?_⟩
  calc
    (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N)) =
        ∫ r in r0..x, orderedRadialZ_FIN035 κ r0 N *
          (Real.exp (N * radialU_orad κ r0 r) / r) :=
      intervalIntegral.integral_congr heq
    _ = orderedRadialZ_FIN035 κ r0 N * orderedTailResistance_FIN038 κ r0 N x := by
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- FIN038: the full ordered right tail. For every `x ≥ r0` (uniformly, including
`x → ∞`), the actual tail mass of the ordered radial probability is comparable to
`x e^{-N U(x)} / (√N (1 + q))`, the actual resistance integral from `r0` to `x` is
at most a constant times `e^{N U(x)} / (x √N (1 + q))`, and the tail Hardy product
with the logarithm is bounded by `Q / N`. The constants and the particle threshold
depend only on κ; every actual median retains the FIN035 window and resistance
bounds. -/
theorem ordered_full_right_tail_logarithmic_hardy_product {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧
      r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    ∃ A B R H Q K D N0 : ℝ,
      0 < A ∧ 0 < B ∧ 0 < R ∧ 0 < H ∧ 0 < Q ∧
      0 < K ∧ 0 < D ∧ 0 < N0 ∧
      ∀ N : ℕ+, N0 ≤ (N : ℝ) →
        IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        0 < orderedRadialZ_FIN035 κ r0 (N : ℝ) ∧
        Integrable (orderedRadialWeight_FIN035 κ r0 (N : ℝ)) ∧
        (∀ x : ℝ, r0 ≤ x →
          let q := Real.sqrt (N : ℝ) * (x - r0)
          let T := orderedTailMass_FIN038 κ r0 (N : ℝ) x
          let J := orderedTailResistance_FIN038 κ r0 (N : ℝ) x
          0 < T ∧
          IntervalIntegrable
            (fun r => Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r) volume r0 x ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x) =
            T / orderedRadialZ_FIN035 κ r0 (N : ℝ) ∧
          A * (x * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
            (Real.sqrt (N : ℝ) * (1 + q)))) ≤ T ∧
          T ≤ B * (x * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
            (Real.sqrt (N : ℝ) * (1 + q)))) ∧
          J ≤ R * (Real.exp ((N : ℝ) * radialU_orad κ r0 x) /
            (x * (Real.sqrt (N : ℝ) * (1 + q)))) ∧
          T * J ≤ B * R / ((N : ℝ) * (1 + q) ^ 2) ∧
          Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T) ≤
            H * (1 + q ^ 2) + Real.log (1 + q) ∧
          T * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T) ≤ Q / (N : ℝ) ∧
          IntervalIntegrable
            (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) volume r0 x ∧
          (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) =
            orderedRadialZ_FIN035 κ r0 (N : ℝ) * J ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x) *
            (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) = T * J ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x) *
            (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
            Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x)) =
              T * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T) ∧
          (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x) *
            (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
              orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
            Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x)) ≤
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
  have hf0 : radialDpsi_orad κ r0 = 0 := by
    unfold radialDpsi_orad
    have hκ0 : κ ≠ 0 := by linarith
    have : r0 / κ = DGPS.Circle.BesselMoments.besselRatio r0 :=
      (div_eq_iff hκ0).2 (by nlinarith [hroot])
    linarith
  have hlow : ∀ t, r0 ≤ t → c * (t - r0) ≤ radialDpsi_orad κ t := by
    intro t ht
    rcases ht.eq_or_lt with h | h
    · subst t
      rw [hf0]
      simp
    · obtain ⟨hl, -, -, hpos⟩ := hwell t (by linarith)
      rw [abs_of_pos (sub_pos.mpr h), abs_of_pos (hpos h)] at hl
      exact hl
  have hup : ∀ t, r0 ≤ t → radialDpsi_orad κ t ≤ (t - r0) / 2 :=
    fun t ht => orderedTail_dpsi_upper_FIN038 hκ hr0 hroot ht
  let A := Real.exp (-1)
  let B := Real.exp (c / 2) * (2 / c + 4 / (c ^ 2 * r0))
  let R := (2 * (r0 + 1) * (1 + 1 / (3 * c / 8) + 2 / (3 * c / 8) ^ 2) / r0) +
    2 * (1 + 4 / c)
  let H := 1 + Real.log (1 + Bn * Real.exp 1 / r0) + C
  let Q := B * R * (H + 1)
  let N0 := max N35 1
  have hA : 0 < A := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hH : 0 < H := by
    have hl : 0 ≤ Real.log (1 + Bn * Real.exp 1 / r0) :=
      Real.log_nonneg (by have : 0 < Bn * Real.exp 1 / r0 := by positivity
                          linarith)
    dsimp [H]
    linarith
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hN0 : 0 < N0 := hN35.trans_le (le_max_left _ _)
  refine ⟨r0, hr0, hroot, A, B, R, H, Q, K, D, N0,
    hA, hB, hR, hH, hQ, hK, hD, hN0, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hN35' : N35 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  obtain ⟨hprob, hZl, hZu, hmom, hmed⟩ := h35 N hN35'
  have hZ : 0 < orderedRadialZ_FIN035 κ r0 (N : ℝ) :=
    (div_pos hLn (Real.sqrt_pos.mpr hNpos)).trans_le hZl
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := (le_max_right _ _).trans hN
    simpa using Real.sqrt_le_sqrt hN1
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hi2 : Integrable (orderedRadialWeight_FIN035 κ r0 (Real.sqrt (N : ℝ) ^ 2)) :=
    orderedRadialWeight_integrable_FIN035 hr0 hc hs1 (fun r hr => (hquad r hr).1)
  have hi : Integrable (orderedRadialWeight_FIN035 κ r0 (N : ℝ)) := by
    simpa only [Real.sq_sqrt hNpos.le] using hi2
  refine ⟨hprob, hZ, hi, ?_, hmed⟩
  intro x hx
  dsimp only
  let s := Real.sqrt (N : ℝ)
  let q := s * (x - r0)
  let T := orderedTailMass_FIN038 κ r0 (N : ℝ) x
  let J := orderedTailResistance_FIN038 κ r0 (N : ℝ) x
  have hxpos : 0 < x := hr0.trans_le hx
  have hq : 0 ≤ q := mul_nonneg hs.le (sub_nonneg.mpr hx)
  have hs2 : s ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hTl0 := orderedTail_lower_FIN038 hr0 hs1 hx hup hi2
  have hTu0 := orderedTail_upper_FIN038 hr0 hc hs1 hx hlow hi2
  have hJu0 := orderedTailResistance_upper_FIN038 hr0 hc hs1 hx hlow
  have hTlN : A * (x * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
      (s * (1 + q)))) ≤ T := by
    rwa [hs2] at hTl0
  have hTuN : T ≤ B * (x * (Real.exp (-(N : ℝ) * radialU_orad κ r0 x) /
      (s * (1 + q)))) := by
    rwa [hs2] at hTu0
  have hJuN : J ≤ R * (Real.exp ((N : ℝ) * radialU_orad κ r0 x) /
      (x * (s * (1 + q)))) := by
    rwa [hs2] at hJu0
  have hTl : (x * A) * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
      (s * (1 + q))) ≤ T := by
    rw [hs2]
    have h := hTlN
    rw [← mul_assoc, mul_comm A x] at h
    exact h
  have hTu : T ≤ (B * x) * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
      (s * (1 + q))) := by
    rw [hs2]
    have h := hTuN
    rw [← mul_assoc] at h
    exact h
  have hJu : J ≤ (R / x) * (Real.exp (s ^ 2 * radialU_orad κ r0 x) /
      (s * (1 + q))) := by
    rw [hs2]
    refine hJuN.trans (le_of_eq ?_)
    field_simp
  have hden : 0 < s * (1 + q) := by positivity
  have hTpos : 0 < T :=
    (mul_pos hA (mul_pos hxpos (div_pos (Real.exp_pos _) (by positivity)))).trans_le hTlN
  have hJ : 0 ≤ J := by
    apply intervalIntegral.integral_nonneg hx
    intro r hr
    exact div_nonneg (Real.exp_pos _).le (by linarith [hr.1])
  have hU : s ^ 2 * radialU_orad κ r0 x ≤ C * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hquad x hxpos.le).2 (sq_nonneg s)
    calc
      s ^ 2 * radialU_orad κ r0 x ≤ s ^ 2 * (C * (x - r0) ^ 2) := this
      _ = C * q ^ 2 := by dsimp [q]; ring
  have hlog0 := orderedInner_log_bound_FIN037 (A := x * A) (mul_pos hxpos hA) hBn hC hs hq
    hZ hZu hTl hU
  have hlogstep : Real.log (1 + Bn / (x * A)) ≤ Real.log (1 + Bn * Real.exp 1 / r0) := by
    apply Real.log_le_log (by have : 0 < Bn / (x * A) := by positivity
                              linarith)
    have : Bn / (x * A) = Bn * Real.exp 1 / x := by
      dsimp [A]
      rw [Real.exp_neg]
      field_simp
    rw [this]
    have h2 : Bn * Real.exp 1 / x ≤ Bn * Real.exp 1 / r0 :=
      div_le_div_of_nonneg_left (by positivity) hr0 hx
    linarith
  have hlog : Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T) ≤
      H * (1 + q ^ 2) + Real.log (1 + q) := by
    have hq2 : 0 ≤ 1 + q ^ 2 := by positivity
    have hcoef : 1 + Real.log (1 + Bn / (x * A)) + C ≤ H := by
      dsimp [H]; linarith
    calc
      Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T)
          ≤ (1 + Real.log (1 + Bn / (x * A)) + C) * (1 + q ^ 2) + Real.log (1 + q) :=
        hlog0
      _ ≤ H * (1 + q ^ 2) + Real.log (1 + q) := by
        have := mul_le_mul_of_nonneg_right hcoef hq2
        linarith
  have hhardy := orderedInner_hardy_algebra_FIN037 (mul_pos hB hxpos).le
    (div_pos hR hxpos).le hH.le hs hq hTpos hJ hZ hTu hJu hlog
  have hxR : B * x * (R / x) = B * R := by field_simp
  have hhprod : T * J ≤ B * R / ((N : ℝ) * (1 + q) ^ 2) := by
    have h := hhardy.1
    rw [hxR, hs2] at h
    exact h
  have hrawhardy : T * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T) ≤
      Q / (N : ℝ) := by
    have h := hhardy.2
    rw [hxR, hs2] at h
    exact h
  have hxi : IntervalIntegrable
      (fun r => Real.exp ((N : ℝ) * radialU_orad κ r0 r) / r) volume r0 x :=
    orderedResistance_integrable_FIN035 hr0 hxpos
  have hlaw := orderedTailMass_law_FIN038 (κ := κ) (r0 := r0) (N := (N : ℝ)) hxpos hi hZ
  have hnormalized := orderedTail_normalized_resistance_FIN038 (κ := κ) (N := (N : ℝ))
    hr0 hx hZ
  have hcancel :
      (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x) *
        (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
          orderedRadialZ_FIN035 κ r0 (N : ℝ))) = T * J := by
    rw [hlaw, hnormalized.2]
    change (T / orderedRadialZ_FIN035 κ r0 (N : ℝ)) *
      (orderedRadialZ_FIN035 κ r0 (N : ℝ) * J) = T * J
    field_simp [hZ.ne']
  have hlognormalized :
      Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x)) =
        Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T) := by
    rw [hlaw]
    congr 1
    change 1 + 1 / (T / orderedRadialZ_FIN035 κ r0 (N : ℝ)) =
      1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T
    field_simp [hTpos.ne', hZ.ne']
  have hnormalizedproduct :
      (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x) *
        (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
          orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
        Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Ici x)) =
          T * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 (N : ℝ) / T) := by
    rw [hcancel, hlognormalized]
  have hnormalizedhardy := hnormalizedproduct.le.trans hrawhardy
  exact ⟨hTpos, hxi, hlaw, hTlN, hTuN, hJuN, hhprod, hlog, hrawhardy,
    hnormalized.1, hnormalized.2, hcancel, hnormalizedproduct, hnormalizedhardy⟩

end DGPS.FiniteN
