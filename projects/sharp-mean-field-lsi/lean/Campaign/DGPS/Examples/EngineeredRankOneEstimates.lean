import DGPS.Examples.EngineeredRankOneEndpoints

open MeasureTheory Real Set Filter Topology
open scoped ContDiff

/-!
# Engineered `Ein` representation (EX035)

With `Ein z = ∫₀^z (1 - e^{-t}) / t dt` (`ein`, integrand `einIntegrand` continuously extended by `1`
at `0`), the engineered correction `R_h = corr h` (EX030/EX031) satisfies, for `h ≥ 2`,
`u ∈ [0,2]`: `R_h(u) = [Ein(h u) + e^{-2h}(Ein(-2h) - Ein(-h(2-u)))] / (1 - e^{-2h})`,
`R_h(u) = Ein(h u) + O(1/h)`, and `exp (R_h u) ≍ 1 + h u`. The representation is proved for all
`h > 0`, `u ∈ ℝ` (`corr_eq_einRep`) by matching derivatives; the `O(1/h)` bound uses
`-8 e^s/(2+s) ≤ Ein(-s) ≤ 0` and `log(1+z) - 2 ≤ Ein z ≤ log(1+z) + 1` for `z ≥ 0`.
Main output: `DGPS.Examples.engineered_ein_representation`.
-/

namespace DGPS.Examples.EngineeredRankOne

/-- Integrand of `Ein`, continuously extended by `1` at the origin. -/
noncomputable def einIntegrand (t : ℝ) : ℝ := if t = 0 then 1 else (1 - exp (-t)) / t

/-- `Ein z = ∫₀^z (1 - e^{-t}) / t dt`. -/
noncomputable def ein (z : ℝ) : ℝ := ∫ t in (0:ℝ)..z, einIntegrand t

theorem einIntegrand_of_ne {t : ℝ} (h : t ≠ 0) : einIntegrand t = (1 - exp (-t)) / t := by
  simp [einIntegrand, h]

theorem einIntegrand_zero : einIntegrand 0 = 1 := by simp [einIntegrand]

theorem einIntegrand_eq_dslope (t : ℝ) :
    einIntegrand t = - dslope (fun s : ℝ => exp (-s)) 0 t := by
  by_cases h : t = 0
  · subst h
    have : HasDerivAt (fun s : ℝ => exp (-s)) (-1) 0 := by
      simpa using (hasDerivAt_neg (0:ℝ)).exp
    rw [dslope_same, this.deriv]; simp [einIntegrand]
  · rw [dslope_of_ne _ h, slope_def_field]
    rw [einIntegrand_of_ne h]
    simp only [neg_zero, exp_zero]
    field_simp
    ring

theorem contDiff_einIntegrand : ContDiff ℝ ∞ einIntegrand := by
  have e : einIntegrand = fun t => - dslope (fun s : ℝ => exp (-s)) 0 t := funext einIntegrand_eq_dslope
  rw [e]
  refine ContDiff.neg ?_
  rw [contDiff_iff_contDiffAt]
  intro x
  refine (analyticAt_dslope ?_ 0 x).contDiffAt
  intro y
  exact (analyticAt_rexp).comp analyticAt_id.neg

theorem continuous_einIntegrand : Continuous einIntegrand := contDiff_einIntegrand.continuous

theorem hasDerivAt_ein (z : ℝ) : HasDerivAt ein (einIntegrand z) z :=
  (continuous_einIntegrand.integral_hasStrictDerivAt 0 z).hasDerivAt

theorem continuous_ein : Continuous ein := continuous_iff_continuousAt.2 fun z => (hasDerivAt_ein z).continuousAt

theorem einIntegrand_pos (t : ℝ) : 0 < einIntegrand t := by
  by_cases h : t = 0
  · simp [einIntegrand, h]
  · rw [einIntegrand_of_ne h]
    rcases lt_or_gt_of_ne h with h1 | h1
    · have : exp (-t) > 1 := by rw [gt_iff_lt, one_lt_exp_iff]; linarith
      exact div_pos_of_neg_of_neg (by linarith) h1
    · have : exp (-t) < 1 := by rw [exp_lt_one_iff]; linarith
      exact div_pos (by linarith) h1

theorem einIntegrand_le_one {t : ℝ} (ht : 0 ≤ t) : einIntegrand t ≤ 1 := by
  by_cases h : t = 0
  · simp [einIntegrand, h]
  · rw [einIntegrand_of_ne h]
    have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    rw [div_le_one hp]
    have := Real.add_one_le_exp (-t)
    linarith

theorem einIntegrand_le_inv {t : ℝ} (ht : 0 < t) : einIntegrand t ≤ 1 / t := by
  rw [einIntegrand_of_ne ht.ne']
  rw [div_le_div_iff_of_pos_right ht]
  have := exp_pos (-t)
  linarith

theorem einIntegrand_neg (s : ℝ) : einIntegrand (-s) = exp s * einIntegrand s := by
  by_cases h : s = 0
  · simp [einIntegrand, h]
  · have h' : -s ≠ 0 := neg_ne_zero.2 h
    rw [einIntegrand_of_ne h', einIntegrand_of_ne h, neg_neg]
    have : exp s * exp (-s) = 1 := by rw [← exp_add]; simp
    field_simp
    linear_combination this

theorem ein_zero : ein 0 = 0 := by simp [ein]

theorem monotone_ein : Monotone ein :=
  monotone_of_deriv_nonneg (fun z => (hasDerivAt_ein z).differentiableAt)
    (fun z => by rw [(hasDerivAt_ein z).deriv]; exact (einIntegrand_pos z).le)

theorem ein_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ ein z := by
  have := monotone_ein hz; rwa [ein_zero] at this

theorem ein_nonpos {z : ℝ} (hz : z ≤ 0) : ein z ≤ 0 := by
  have := monotone_ein hz; rwa [ein_zero] at this

theorem ein_le_self {z : ℝ} (hz : 0 ≤ z) : ein z ≤ z := by
  have hd : ∀ x, HasDerivAt (fun x => x - ein x) (1 - einIntegrand x) x :=
    fun x => (hasDerivAt_id x).sub (hasDerivAt_ein x)
  have hm : MonotoneOn (fun x => x - ein x) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_id.sub continuous_ein).continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      linarith [einIntegrand_le_one (le_of_lt (mem_Ioi.1 hx))]
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
  simp only [ein_zero] at this
  linarith


theorem aH_eq (h : ℝ) (hh : 0 < h) : aH h = 2 / (1 - exp (-2 * h)) := by
  have h1 : 0 < 1 - exp (-2 * h) := by
    have : exp (-2 * h) < 1 := by rw [exp_lt_one_iff]; linarith
    linarith
  have := aH_mul h hh
  have e : exp (-h * 2) = exp (-2 * h) := by ring_nf
  rw [e] at this
  rw [eq_div_iff h1.ne']
  exact this

/-- The right-hand side of the Ein representation of `R_h`. -/
noncomputable def einRep (h u : ℝ) : ℝ :=
  (ein (h * u) + exp (-2 * h) * (ein (-2 * h) - ein (-h * (2 - u)))) / (1 - exp (-2 * h))

/-- The derivative of `einRep h` in `u`. -/
noncomputable def einRepDeriv (h u : ℝ) : ℝ :=
  (h * einIntegrand (h * u) - exp (-2 * h) * (h * einIntegrand (-h * (2 - u)))) / (1 - exp (-2 * h))

theorem hasDerivAt_einRep (h u : ℝ) : HasDerivAt (einRep h) (einRepDeriv h u) u := by
  have h1 : HasDerivAt (fun u : ℝ => h * u) h u := by simpa using (hasDerivAt_id u).const_mul h
  have h2 : HasDerivAt (fun u : ℝ => -h * (2 - u)) h u := by
    have := ((hasDerivAt_const u (2:ℝ)).sub (hasDerivAt_id u)).const_mul (-h)
    simpa using this
  have h3 := ((hasDerivAt_ein (h * u)).comp u h1)
  have h4 := ((hasDerivAt_ein (-h * (2 - u))).comp u h2)
  have h5 := ((h3.add (((hasDerivAt_const u (ein (-2 * h))).sub h4).const_mul (exp (-2 * h)))).div_const
    (1 - exp (-2 * h)))
  refine h5.congr_deriv ?_
  unfold einRepDeriv
  ring

theorem einRep_zero (h : ℝ) : einRep h 0 = 0 := by
  have : -h * (2 - 0) = -2 * h := by ring
  unfold einRep; rw [mul_zero, ein_zero, this]; simp

theorem continuous_einRepDeriv (h : ℝ) : Continuous (einRepDeriv h) := by
  have := continuous_einIntegrand
  unfold einRepDeriv
  fun_prop

theorem einRepDeriv_eq_integrand (h : ℝ) (hh : 0 < h) (u : ℝ) : einRepDeriv h u = integrand h u := by
  have hd : Dense (({0, 2} : Set ℝ)ᶜ) := by
    rw [Set.compl_eq_univ_sdiff]; exact dense_univ.sdiff_finite (Set.toFinite _)
  have := Continuous.ext_on hd (continuous_einRepDeriv h) ((contDiff_integrand h hh).continuous) ?_
  · exact congrFun this u
  intro v hv
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hv
  obtain ⟨h0, h2⟩ := hv
  have h1 : 0 < 1 - exp (-2 * h) := by
    have : exp (-2 * h) < 1 := by rw [exp_lt_one_iff]; linarith
    linarith
  have hF : exp (-2 * h) * exp (-(-h * (2 - v))) = exp (-h * v) := by
    rw [← exp_add]; congr 1; ring
  have ha : h * v ≠ 0 := mul_ne_zero hh.ne' h0
  have hb : -h * (2 - v) ≠ 0 := mul_ne_zero (neg_ne_zero.2 hh.ne') (sub_ne_zero.2 (Ne.symm h2))
  have h2' : 2 - v ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
  unfold einRepDeriv
  rw [einIntegrand_of_ne ha, einIntegrand_of_ne hb, integrand_of_ne h h0 h2]
  unfold numer
  rw [aH_eq h hh]
  simp only [neg_mul, neg_neg] at hF ⊢
  have h1' : 1 - exp (-(2 * h)) ≠ 0 := by rw [neg_mul] at h1; exact h1.ne'
  generalize exp (-(2 * h)) = e2 at *
  generalize exp (h * (2 - v)) = F at *
  generalize exp (-(h * v)) = E at *
  field_simp
  linear_combination (-v) * hF


theorem corr_eq_einRep (h : ℝ) (hh : 0 < h) (u : ℝ) : corr h u = einRep h u := by
  have hd : Differentiable ℝ (fun x => corr h x - einRep h x) := fun x =>
    ((contDiff_corr h hh).differentiable (by simp) x).sub (hasDerivAt_einRep h x).differentiableAt
  have h0 : ∀ x, deriv (fun x => corr h x - einRep h x) x = 0 := by
    intro x
    have : HasDerivAt (fun x => corr h x - einRep h x) (deriv (corr h) x - einRepDeriv h x) x :=
      ((contDiff_corr h hh).differentiable (by simp) x).hasDerivAt.sub (hasDerivAt_einRep h x)
    rw [this.deriv, deriv_corr h hh, einRepDeriv_eq_integrand h hh]; ring
  have := is_const_of_deriv_eq_zero hd h0 u 0
  simp only [einRep_zero] at this
  have c0 : corr h 0 = 0 := by simp [corr]
  rw [c0] at this
  linarith

theorem einIntegrand_le_two_div {s : ℝ} (hs : 0 ≤ s) : einIntegrand s ≤ 2 / (1 + s) := by
  rcases le_total s 1 with h1 | h1
  · refine (einIntegrand_le_one hs).trans ?_
    rw [le_div_iff₀ (by linarith)]; linarith
  · have hp : 0 < s := by linarith
    refine (einIntegrand_le_inv hp).trans ?_
    rw [div_le_div_iff₀ hp (by linarith)]; linarith

theorem ein_neg_ge {s : ℝ} (hs : 0 ≤ s) : -(8 * exp s / (2 + s)) ≤ ein (-s) := by
  have hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt (fun x => 8 * exp x / (2 + x) + ein (-x))
      ((8 * exp x * (2 + x) - 8 * exp x * 1) / (2 + x) ^ 2 + einIntegrand (-x) * (-1)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 8 * exp x / (2 + x))
        ((8 * exp x * (2 + x) - 8 * exp x * 1) / (2 + x) ^ 2) x := by
      have := ((hasDerivAt_exp x).const_mul 8).div ((hasDerivAt_id x).const_add 2) (by simp; linarith)
      exact this
    have h2 : HasDerivAt (fun x : ℝ => ein (-x)) (einIntegrand (-x) * (-1)) x :=
      (hasDerivAt_ein (-x)).comp x (hasDerivAt_neg x)
    exact h1.add h2
  have hm : MonotoneOn (fun x => 8 * exp x / (2 + x) + ein (-x)) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (le_of_lt (by simpa using hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := hx
      rw [(hd x hx0.le).deriv, einIntegrand_neg]
      have hg := einIntegrand_le_two_div hx0.le
      have key : 2 / (1 + x) ≤ 8 * (1 + x) / (2 + x) ^ 2 := by
        rw [div_le_div_iff₀ (by linarith) (by positivity)]; nlinarith
      have e1 : (8 * exp x * (2 + x) - 8 * exp x * 1) / (2 + x) ^ 2
          = exp x * (8 * (1 + x) / (2 + x) ^ 2) := by
        field_simp; ring
      rw [e1]
      have := exp_pos x
      nlinarith [mul_le_mul_of_nonneg_left (hg.trans key) this.le]
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs
  simp only [neg_zero, ein_zero, exp_zero] at this
  have h3 : (0:ℝ) ≤ 8 * 1 / (2 + 0) + 0 := by norm_num
  linarith


theorem ein_one_le : ein 1 ≤ 1 := by simpa using ein_le_self (z := 1) zero_le_one

theorem ein_sub_log_le {z : ℝ} (hz : 1 ≤ z) : ein z - log z ≤ ein 1 := by
  have hd : ∀ x : ℝ, 1 ≤ x → HasDerivAt (fun x => ein x - log x) (einIntegrand x - x⁻¹) x :=
    fun x hx => (hasDerivAt_ein x).sub (Real.hasDerivAt_log (by linarith))
  have hm : AntitoneOn (fun x => ein x - log x) (Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1) ?_ ?_ ?_
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (le_of_lt (by simpa using hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 1 < x := hx
      rw [(hd x hx0.le).deriv]
      have := einIntegrand_le_inv (show 0 < x by linarith)
      rw [one_div] at this
      linarith
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
  simpa using this

theorem ein_sub_log_ge {z : ℝ} (hz : 1 ≤ z) : ein 1 - exp (-1) ≤ ein z - log z := by
  have hd : ∀ x : ℝ, 1 ≤ x → HasDerivAt (fun x => ein x - log x - exp (-x))
      (einIntegrand x - x⁻¹ - exp (-x) * (-1)) x := by
    intro x hx
    exact ((hasDerivAt_ein x).sub (Real.hasDerivAt_log (by linarith))).sub
      ((hasDerivAt_neg x).exp)
  have hm : MonotoneOn (fun x => ein x - log x - exp (-x)) (Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (le_of_lt (by simpa using hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 1 < x := hx
      have hxp : 0 < x := by linarith
      rw [(hd x hx0.le).deriv, einIntegrand_of_ne hxp.ne']
      have : (1 - exp (-x)) / x - x⁻¹ - exp (-x) * (-1) = exp (-x) * ((x - 1) / x) := by
        field_simp; ring
      rw [this]
      have := exp_pos (-x)
      positivity
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hz) hz
  simp only [log_one, sub_zero] at this
  have h2 := exp_pos (-z)
  linarith

theorem log_one_add_le_log_add {z : ℝ} (hz : 1 ≤ z) : log (1 + z) ≤ log z + 1 := by
  have hp : 0 < z := by linarith
  have : log (1 + z) ≤ log (2 * z) := log_le_log (by linarith) (by linarith)
  rw [log_mul (by norm_num) hp.ne'] at this
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
  linarith

theorem ein_le_log {z : ℝ} (hz : 0 ≤ z) : ein z ≤ log (1 + z) + 1 := by
  rcases le_total z 1 with h1 | h1
  · have := ein_le_self hz
    have h0 : 0 ≤ log (1 + z) := log_nonneg (by linarith)
    linarith
  · have := ein_sub_log_le h1
    have := ein_one_le
    have : log z ≤ log (1 + z) := log_le_log (by linarith) (by linarith)
    linarith

theorem log_le_ein {z : ℝ} (hz : 0 ≤ z) : log (1 + z) - 2 ≤ ein z := by
  rcases le_total z 1 with h1 | h1
  · have := ein_nonneg hz
    have h0 : log (1 + z) ≤ z := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + z by linarith)
      linarith
    linarith
  · have h3 := ein_sub_log_ge h1
    have h4 := ein_nonneg (show (0:ℝ) ≤ 1 by norm_num)
    have h5 := log_one_add_le_log_add h1
    have h6 : exp (-1) ≤ 1 := by rw [exp_le_one_iff]; norm_num
    linarith


theorem einRep_sub_ein {h : ℝ} (hh : 0 < h) (u : ℝ) :
    einRep h u - ein (h * u) =
      exp (-2 * h) * (ein (h * u) + (ein (-2 * h) - ein (-h * (2 - u)))) / (1 - exp (-2 * h)) := by
  have h1 : 1 - exp (-2 * h) ≠ 0 := by
    have : exp (-2 * h) < 1 := by rw [exp_lt_one_iff]; linarith
    linarith
  unfold einRep
  generalize exp (-2 * h) = e2 at *
  field_simp
  ring

theorem exp_neg_two_mul_mul_exp {h : ℝ} : exp (-2 * h) * exp (2 * h) = 1 := by
  rw [← exp_add, show -2 * h + 2 * h = 0 by ring, exp_zero]

theorem exp_mix {h u : ℝ} : exp (-2 * h) * exp (h * (2 - u)) = exp (-(h * u)) := by
  rw [← exp_add]; congr 1; ring

theorem abs_einRep_sub_ein_le {h : ℝ} (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    |einRep h u - ein (h * u)| ≤ 26 / h := by
  obtain ⟨hu0, hu2⟩ := hu
  have hp : 0 < h := by linarith
  have hE := @exp_neg_two_mul_mul_exp h
  have hF := @exp_mix h u
  have he2pos : 0 < exp (-2 * h) := exp_pos _
  have hexp_pos := exp_pos (2 * h)
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * h by linarith)
  have h5 : exp (-2 * h) ≤ 1 / 5 := by
    have h6 : (5:ℝ) ≤ exp (2 * h) := by
      have := Real.add_one_le_exp (2 * h); linarith
    nlinarith [mul_le_mul_of_nonneg_left h6 he2pos.le]
  have hs1 : exp (-2 * h) * (2 * h) ≤ 1 / h := by
    rw [le_div_iff₀ hp]
    nlinarith [mul_le_mul_of_nonneg_left hq he2pos.le]
  -- the three pieces
  have ha0 : 0 ≤ ein (h * u) := ein_nonneg (by positivity)
  have ha1 : ein (h * u) ≤ 2 * h := by
    have := ein_le_self (z := h * u) (by positivity)
    nlinarith
  have hb := ein_neg_ge (s := 2 * h) (by linarith)
  have hb0 : ein (-2 * h) ≤ 0 := ein_nonpos (by linarith)
  have hs2 : 0 ≤ h * (2 - u) := mul_nonneg hp.le (by linarith)
  have hc := ein_neg_ge (s := h * (2 - u)) hs2
  have hc0 : ein (-h * (2 - u)) ≤ 0 := ein_nonpos (by nlinarith)
  rw [← neg_mul] at hb hc
  set a := ein (h * u)
  set b := ein (-2 * h)
  set c := ein (-h * (2 - u))
  set B1 := 8 * exp (2 * h) / (2 + 2 * h) with hB1
  set B2 := 8 * exp (h * (2 - u)) / (2 + h * (2 - u)) with hB2
  have hB1p : 0 ≤ B1 := by positivity
  have hB2p : 0 ≤ B2 := by positivity
  have hT : |a + (b - c)| ≤ 2 * h + B1 + B2 := by
    rw [abs_le]; constructor <;> linarith
  have hD : 2 + h * (2 - u) ≥ 2 := by nlinarith
  have e1 : exp (-2 * h) * B1 = 8 / (2 + 2 * h) := by
    rw [hB1, show exp (-2 * h) * (8 * exp (2 * h) / (2 + 2 * h))
      = 8 * (exp (-2 * h) * exp (2 * h)) / (2 + 2 * h) by ring, hE]; ring
  have e2' : exp (-2 * h) * B2 = 8 * exp (-(h * u)) / (2 + h * (2 - u)) := by
    rw [hB2, show exp (-2 * h) * (8 * exp (h * (2 - u)) / (2 + h * (2 - u)))
      = 8 * (exp (-2 * h) * exp (h * (2 - u))) / (2 + h * (2 - u)) by ring, hF]
  have hb1 : 8 / (2 + 2 * h) ≤ 4 / h := by
    rw [div_le_div_iff₀ (by linarith) hp]; nlinarith
  have hb2 : 8 * exp (-(h * u)) / (2 + h * (2 - u)) ≤ 8 / h := by
    have hEp := exp_pos (-(h * u))
    rw [div_le_div_iff₀ (by linarith) hp]
    rcases le_total u 1 with h1 | h1
    · have : exp (-(h * u)) ≤ 1 := by rw [exp_le_one_iff]; nlinarith
      nlinarith
    · have h7 : exp (-(h * u)) * (1 + h) ≤ 1 := by
        have h8 := Real.add_one_le_exp (h * u)
        have h9 : exp (-(h * u)) * exp (h * u) = 1 := by rw [← exp_add]; simp
        have : 1 + h ≤ exp (h * u) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this hEp.le]
      nlinarith
  have hsum : exp (-2 * h) * |a + (b - c)| ≤ 13 / h := by
    calc exp (-2 * h) * |a + (b - c)| ≤ exp (-2 * h) * (2 * h + B1 + B2) :=
          mul_le_mul_of_nonneg_left hT he2pos.le
      _ = exp (-2 * h) * (2 * h) + exp (-2 * h) * B1 + exp (-2 * h) * B2 := by ring
      _ ≤ 1 / h + 4 / h + 8 / h := by
          rw [e1, e2']; exact add_le_add (add_le_add hs1 hb1) hb2
      _ = 13 / h := by ring
  rw [einRep_sub_ein hp, abs_div, abs_mul, abs_of_pos he2pos]
  have h1p : 0 < 1 - exp (-2 * h) := by linarith
  rw [abs_of_pos h1p, div_le_iff₀ h1p]
  have h26 : 26 / h * (4 / 5) ≤ 26 / h * (1 - exp (-2 * h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h27 : 26 / h * (4 / 5) = 104 / 5 / h := by ring
  have h28 : (13:ℝ) / h ≤ 104 / 5 / h := by
    apply div_le_div_of_nonneg_right (by norm_num) hp.le
  linarith


theorem exp_corr_bounds {h : ℝ} (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    exp (-15) * (1 + h * u) ≤ exp (corr h u) ∧ exp (corr h u) ≤ exp 14 * (1 + h * u) := by
  have hp : 0 < h := by linarith
  have hz : 0 ≤ h * u := mul_nonneg hp.le hu.1
  have hd := abs_einRep_sub_ein_le hh hu
  rw [← corr_eq_einRep h hp u] at hd
  have h13 : 26 / h ≤ 13 := by rw [div_le_iff₀ hp]; linarith
  rw [abs_le] at hd
  have h1 := ein_le_log hz
  have h2 := log_le_ein hz
  have hpos : (0:ℝ) < 1 + h * u := by linarith
  have e : exp (log (1 + h * u)) = 1 + h * u := exp_log hpos
  constructor
  · calc exp (-15) * (1 + h * u) = exp (-15 + log (1 + h * u)) := by rw [exp_add, e]
      _ ≤ exp (corr h u) := exp_le_exp.2 (by linarith [hd.1])
  · calc exp (corr h u) ≤ exp (14 + log (1 + h * u)) := exp_le_exp.2 (by linarith [hd.2])
      _ = exp 14 * (1 + h * u) := by rw [exp_add, e]

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne

/-- EX035: the `Ein` representation of the engineered correction.  With
`Ein z = ∫₀^z (1 - e^{-t}) / t dt` (`DGPS.Examples.EngineeredRankOne.ein`, the integrand being
continuously extended by `1` at the origin), for every `h ≥ 2` and `u ∈ [0,2]`
`R_h(u) = [Ein(h u) + e^{-2h}(Ein(-2h) - Ein(-h(2-u)))] / (1 - e^{-2h})`; uniformly in
`h ≥ 2`, `u ∈ [0,2]`, `R_h(u) = Ein(h u) + O(1/h)`, and `exp R_h(u)` is bounded above and below by
fixed positive multiples of `1 + h u`.  Here `R_h = corr h` (EX030/EX031). -/
theorem engineered_ein_representation :
    (Continuous einIntegrand ∧ einIntegrand 0 = 1 ∧
      ∀ t : ℝ, t ≠ 0 → einIntegrand t = (1 - exp (-t)) / t) ∧
    (∀ h : ℝ, 2 ≤ h → ∀ u ∈ Icc (0:ℝ) 2,
      corr h u = (ein (h * u) + exp (-2 * h) * (ein (-2 * h) - ein (-h * (2 - u)))) /
        (1 - exp (-2 * h))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ u ∈ Icc (0:ℝ) 2, |corr h u - ein (h * u)| ≤ C / h) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ u ∈ Icc (0:ℝ) 2,
      c * (1 + h * u) ≤ exp (corr h u) ∧ exp (corr h u) ≤ C * (1 + h * u)) := by
  refine ⟨⟨continuous_einIntegrand, einIntegrand_zero, fun t ht => einIntegrand_of_ne ht⟩,
    fun h hh u _ => corr_eq_einRep h (by linarith) u, ⟨26, by norm_num, fun h hh u hu => ?_⟩,
    ⟨exp (-15), exp 14, exp_pos _, exp_pos _, fun h hh u hu => exp_corr_bounds hh hu⟩⟩
  have := abs_einRep_sub_ein_le hh hu
  rwa [← corr_eq_einRep h (by linarith) u] at this

end DGPS.Examples
