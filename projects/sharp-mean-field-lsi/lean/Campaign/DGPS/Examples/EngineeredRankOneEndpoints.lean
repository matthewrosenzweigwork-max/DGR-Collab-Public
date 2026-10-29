import DGPS.Examples.EngineeredRankOne

open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open DGPS.Circle.AngularNormalization

/-!
# Removable endpoints and monotone correction (EX031)

For `h ≥ 2`, `N_h(u) = A_h (1 - exp (-h u)) - u` vanishes at `0` and `2`, is concave and
nonnegative on `[0,2]`, and the endpoint-extended integrand `N_h(u) / (u (2 - u))`
(`DGPS.Examples.EngineeredRankOne.integrand`) is smooth (indeed real analytic) on all of `ℝ`.
Hence `R_h` (`corr`) is smooth on `ℝ` and nondecreasing on `[0,2]`, and its composition with
`U = 1 - cos θ` is smooth and `2π`-periodic. Main output:
`DGPS.Examples.removable_endpoints_and_monotone_correction`.
-/

namespace DGPS.Examples.EngineeredRankOne

theorem aH_pos (h : ℝ) (hh : 0 < h) : 0 < aH h := by
  unfold aH
  have h1 := Real.cosh_pos h
  have h2 := Real.sinh_pos_iff.2 hh
  have := div_pos h1 h2
  linarith

theorem analyticAt_dslope {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x) (a : ℝ) (x : ℝ) :
    AnalyticAt ℝ (dslope f a) x := by
  by_cases hx : x = a
  · subst hx
    obtain ⟨p, hp⟩ := hf x
    exact (HasFPowerSeriesAt.has_fpower_series_dslope_fslope hp).analyticAt
  · have h1 : AnalyticAt ℝ (fun z => (f z - f a) / (z - a)) x :=
      ((hf x).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hx)
    refine h1.congr ?_
    have : ∀ᶠ z in 𝓝 x, z ≠ a := isOpen_ne.mem_nhds hx
    filter_upwards [this] with z hz
    rw [dslope_of_ne _ hz, slope_def_field]

theorem analyticAt_numer (h x : ℝ) : AnalyticAt ℝ (numer h) x := by
  unfold numer
  have h1 : AnalyticAt ℝ (fun y : ℝ => exp (-h * y)) x :=
    (analyticAt_rexp).comp (analyticAt_const.mul analyticAt_id)
  exact (analyticAt_const.mul (analyticAt_const.sub h1)).sub analyticAt_id

/-- First quotient `N_h(v) / v`, extended analytically at `0`. -/
noncomputable def quot1 (h : ℝ) : ℝ → ℝ := dslope (numer h) 0
/-- Second quotient `N_h(v) / (v (v - 2))`, extended analytically at `0` and `2`. -/
noncomputable def quot2 (h : ℝ) : ℝ → ℝ := dslope (quot1 h) 2

theorem analyticAt_quot1 (h x : ℝ) : AnalyticAt ℝ (quot1 h) x :=
  analyticAt_dslope (analyticAt_numer h) 0 x

theorem analyticAt_quot2 (h x : ℝ) : AnalyticAt ℝ (quot2 h) x :=
  analyticAt_dslope (analyticAt_quot1 h) 2 x

theorem numer_eq_quot1 (h v : ℝ) : numer h v = v * quot1 h v := by
  have := sub_smul_dslope (numer h) 0 v
  simp only [smul_eq_mul, sub_zero, numer_zero] at this
  unfold quot1; linarith

theorem quot1_two (h : ℝ) (hh : 0 < h) : quot1 h 2 = 0 := by
  have := numer_eq_quot1 h 2
  rw [numer_two h hh] at this
  linarith

theorem quot1_eq_quot2 (h : ℝ) (hh : 0 < h) (v : ℝ) : quot1 h v = (v - 2) * quot2 h v := by
  have := sub_smul_dslope (quot1 h) 2 v
  simp only [smul_eq_mul, quot1_two h hh, sub_zero] at this
  unfold quot2; linarith

theorem numer_eq_quot2 (h : ℝ) (hh : 0 < h) (v : ℝ) :
    numer h v = v * ((v - 2) * quot2 h v) := by
  rw [numer_eq_quot1, quot1_eq_quot2 h hh]

theorem integrand_eq_neg_quot2 (h : ℝ) (hh : 0 < h) (v : ℝ) :
    integrand h v = - quot2 h v := by
  by_cases h0 : v = 0
  · subst h0
    have e1 : quot1 h 0 = aH h * h - 1 := by
      unfold quot1
      rw [dslope_same]
      have := (hasDerivAt_numer h 0).deriv
      rw [this]; simp
    have e2 := quot1_eq_quot2 h hh 0
    simp only [integrand, ite_true]
    linarith
  by_cases h2 : v = 2
  · subst h2
    have hg : DifferentiableAt ℝ (quot1 h) 2 := (analyticAt_quot1 h 2).differentiableAt
    have hd : HasDerivAt (numer h) (1 * quot1 h 2 + 2 * deriv (quot1 h) 2) 2 := by
      have := (hasDerivAt_id (2:ℝ)).mul hg.hasDerivAt
      have e : numer h = fun v => id v * quot1 h v := funext (numer_eq_quot1 h)
      rw [e]; exact this
    have e3 := hd.unique (hasDerivAt_numer h 2)
    rw [quot1_two h hh] at e3
    have e4 : quot2 h 2 = deriv (quot1 h) 2 := by unfold quot2; rw [dslope_same]
    have : (2:ℝ) ≠ 0 := by norm_num
    simp only [integrand, this, ite_false, ite_true]
    rw [e4]; linarith
  · rw [integrand_of_ne h h0 h2, numer_eq_quot2 h hh]
    have : (2 - v) ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
    field_simp
    ring

theorem contDiff_integrand (h : ℝ) (hh : 0 < h) : ContDiff ℝ ∞ (integrand h) := by
  have e : integrand h = fun v => - quot2 h v := funext (integrand_eq_neg_quot2 h hh)
  rw [e]
  refine ContDiff.neg ?_
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (analyticAt_quot2 h x).contDiffAt

theorem contDiff_corr (h : ℝ) (hh : 0 < h) : ContDiff ℝ ∞ (corr h) := by
  have hc : Continuous (integrand h) := (contDiff_integrand h hh).continuous
  have hd : ∀ u, HasDerivAt (corr h) (integrand h u) u := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hder : deriv (corr h) = integrand h := funext fun u => (hd u).deriv
  rw [contDiff_infty_iff_deriv, hder]
  exact ⟨fun u => (hd u).differentiableAt, contDiff_integrand h hh⟩

theorem deriv_corr (h : ℝ) (hh : 0 < h) (u : ℝ) : deriv (corr h) u = integrand h u :=
  ((((contDiff_integrand h hh).continuous).integral_hasStrictDerivAt 0 u).hasDerivAt).deriv

theorem concaveOn_numer (h : ℝ) (hh : 0 < h) : ConcaveOn ℝ univ (numer h) := by
  have hd : deriv (numer h) = fun v => aH h * h * exp (-h * v) - 1 :=
    funext fun v => (hasDerivAt_numer h v).deriv
  have hd2 : ∀ v, HasDerivAt (deriv (numer h)) (aH h * h * (exp (-h * v) * -h)) v := by
    intro v
    rw [hd]
    have h1 : HasDerivAt (fun v : ℝ => -h * v) (-h) v := by
      simpa using (hasDerivAt_id v).const_mul (-h)
    have := ((h1.exp).const_mul (aH h * h)).sub_const 1
    exact this
  refine concaveOn_of_deriv2_nonpos convex_univ (continuous_iff_continuousAt.2
      fun x => (hasDerivAt_numer h x).continuousAt).continuousOn
    (fun x _ => (hasDerivAt_numer h x).differentiableAt.differentiableWithinAt)
    (fun x _ => (hd2 x).differentiableAt.differentiableWithinAt) ?_
  intro x _
  have : deriv^[2] (numer h) x = aH h * h * (exp (-h * x) * -h) := by
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
    exact (hd2 x).deriv
  rw [this]
  have h1 := aH_pos h hh
  have h2 := exp_pos (-h * x)
  have : 0 < aH h * h * (exp (-h * x) * h) := by positivity
  nlinarith

theorem numer_nonneg (h : ℝ) (hh : 0 < h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) : 0 ≤ numer h u := by
  have hc := concaveOn_numer h hh
  have ha : 0 ≤ 1 - u / 2 := by linarith [hu.2]
  have hb : 0 ≤ u / 2 := by linarith [hu.1]
  have key := hc.2 (mem_univ (0:ℝ)) (mem_univ (2:ℝ)) ha hb (by ring)
  simp only [smul_eq_mul, numer_zero, numer_two h hh, mul_zero, add_zero] at key
  have e : (0:ℝ) + u / 2 * 2 = u := by ring
  rw [e] at key
  exact key

theorem integrand_nonneg (h : ℝ) (hh : 0 < h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    0 ≤ integrand h u := by
  have hcl : IsClosed {v : ℝ | 0 ≤ integrand h v} :=
    isClosed_le continuous_const (contDiff_integrand h hh).continuous
  have hsub : Ioo (0:ℝ) 2 ⊆ {v : ℝ | 0 ≤ integrand h v} := by
    intro v hv
    have h0 : v ≠ 0 := hv.1.ne'
    have h2 : v ≠ 2 := hv.2.ne
    show 0 ≤ integrand h v
    rw [integrand_of_ne h h0 h2]
    exact div_nonneg (numer_nonneg h hh ⟨hv.1.le, hv.2.le⟩)
      (mul_nonneg hv.1.le (by linarith [hv.2]))
  have := hcl.closure_subset_iff.2 hsub
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 2)] at this
  exact this hu

theorem monotoneOn_corr (h : ℝ) (hh : 0 < h) : MonotoneOn (corr h) (Icc 0 2) := by
  have hd : Differentiable ℝ (corr h) :=
    (contDiff_corr h hh).differentiable (by simp)
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 2) hd.continuous.continuousOn
    hd.differentiableOn ?_
  intro u hu
  rw [interior_Icc] at hu
  rw [deriv_corr h hh]
  exact integrand_nonneg h hh ⟨hu.1.le, hu.2.le⟩

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne

/-- EX031: removable endpoints of the correction integrand and monotonicity of `R_h`.
`N_h = numer h` vanishes at `0` and `2`, is concave on `[0,2]` (indeed on `ℝ`) and nonnegative there;
the endpoint-extended integrand `integrand h` is smooth on `ℝ`; `R_h = corr h` is smooth on `ℝ` and
nondecreasing on `[0,2]`; and the compositions with `U = 1 - cos θ` (as functions of the lifted
angle `t : ℝ`, equivalently on `AngCircle` through `Uang`) are smooth and `2π`-periodic, as are
`E_h`, `log q_h` and `q_h`. -/
theorem removable_endpoints_and_monotone_correction (h : ℝ) (hh : 2 ≤ h) :
    (∀ u, numer h u = aH h * (1 - exp (-h * u)) - u) ∧
    numer h 0 = 0 ∧ numer h 2 = 0 ∧
    ConcaveOn ℝ (Icc 0 2) (numer h) ∧
    (∀ u ∈ Icc (0:ℝ) 2, 0 ≤ numer h u) ∧
    (∀ u, deriv (deriv (numer h)) u = -(aH h * h ^ 2 * exp (-h * u))) ∧
    ContDiff ℝ ∞ (integrand h) ∧
    (∀ u ∈ Icc (0:ℝ) 2, 0 ≤ integrand h u) ∧
    ContDiff ℝ ∞ (corr h) ∧
    (∀ u, deriv (corr h) u = integrand h u) ∧
    MonotoneOn (corr h) (Icc 0 2) ∧
    ContDiff ℝ ∞ (fun t : ℝ => corr h (Uang (t : Real.Angle))) ∧
    (∀ t : ℝ, corr h (Uang ((t + 2 * π : ℝ) : Real.Angle)) = corr h (Uang (t : Real.Angle))) ∧
    ContDiff ℝ ∞ (fun t : ℝ => Eang h (t : Real.Angle)) ∧
    ContDiff ℝ ∞ (fun t : ℝ => logq h (t : Real.Angle)) ∧
    ContDiff ℝ ∞ (fun t : ℝ => qAng h (t : Real.Angle)) := by
  have hp : 0 < h := by linarith
  have hU : ∀ t : ℝ, Uang (t : Real.Angle) = 1 - Real.cos t := fun t => by
    unfold Uang; rw [Real.Angle.cos_coe]
  have hUs : ContDiff ℝ ∞ (fun t : ℝ => Uang (t : Real.Angle)) := by
    have : (fun t : ℝ => Uang (t : Real.Angle)) = fun t => 1 - Real.cos t := funext hU
    rw [this]; exact contDiff_const.sub Real.contDiff_cos
  have hC : ContDiff ℝ ∞ (fun t : ℝ => corr h (Uang (t : Real.Angle))) :=
    (contDiff_corr h hp).comp hUs
  have hd : deriv (numer h) = fun v => aH h * h * exp (-h * v) - 1 :=
    funext fun v => (hasDerivAt_numer h v).deriv
  have hd2 : ∀ v, deriv (deriv (numer h)) v = -(aH h * h ^ 2 * exp (-h * v)) := by
    intro v
    rw [hd]
    have h1 : HasDerivAt (fun v : ℝ => -h * v) (-h) v := by
      simpa using (hasDerivAt_id v).const_mul (-h)
    have := (((h1.exp).const_mul (aH h * h)).sub_const 1).deriv
    rw [this]; ring
  have hE : ContDiff ℝ ∞ (fun t : ℝ => Eang h (t : Real.Angle)) := by
    unfold Eang
    exact ((Real.contDiff_exp.comp (contDiff_const.mul hUs)).sub contDiff_const).div_const _
  have hL : ContDiff ℝ ∞ (fun t : ℝ => logq h (t : Real.Angle)) := by
    unfold logq
    exact (contDiff_const.mul hUs).neg.sub hC
  refine ⟨fun u => rfl, numer_zero h, numer_two h hp,
    (concaveOn_numer h hp).subset (subset_univ _) (convex_Icc 0 2),
    fun u hu => numer_nonneg h hp hu, hd2, contDiff_integrand h hp,
    fun u hu => integrand_nonneg h hp hu, contDiff_corr h hp, deriv_corr h hp,
    monotoneOn_corr h hp, hC, ?_, hE, hL, ?_⟩
  · intro t
    have : ((t + 2 * π : ℝ) : Real.Angle) = (t : Real.Angle) := by
      rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
    rw [this]
  · unfold qAng
    exact contDiff_const.mul (Real.contDiff_exp.comp hL)

end DGPS.Examples
