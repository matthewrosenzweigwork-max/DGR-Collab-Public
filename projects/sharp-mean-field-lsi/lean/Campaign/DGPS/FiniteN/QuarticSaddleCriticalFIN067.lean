import DGPS.FiniteN.QuarticSaddleGlobalFIN066
import DGPS.Examples.AttractiveXYCollapse

/-!
# Quartic saddle: complete critical point exclusion (FIN067)

For the auxiliary function `ψ(x,y) = (x-1)²/(2κ) + y²/(2κη) - log I₀(√(x²+y²))` of the
anisotropic quartic saddle (`quarticPsi_FIN066`), every critical point lies on the `x` axis;
the negative-axis critical points `x = -s` are exactly the roots `s > 0` of `κ g(s) - s = 1`,
satisfy `s ≤ 4` and form a finite set; the transverse curvature there is `(s-4)/(4κs)`, which is
negative for `s < 4`, while at `s = 4` the `x` curvature is `A > 0` and the `y` curvature is `0`.
Main result: `DGPS.FiniteN.quartic_complete_critical_point_exclusion`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DGPS.FiniteN.QuarticSaddleCriticalFIN067

open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Circle.BesselMoments DGPS.FiniteN.AttractiveLandscape
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselConcavity
open DGPS.Circle.BesselMonotonicity DGPS.Examples.AttractiveXYCollapseEX026
open DGPS.FiniteN.QuarticSaddleGlobalFIN066

theorem featureMean_amap_FIN067 (w : EuclideanSpace ℝ (Fin 2)) :
    featureMean featU_FIN066 featPhi_FIN066 (amap_FIN066 w) =
      !₂[Real.sqrt quarticKappa * (w 0 * besselRatio (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) /
            Real.sqrt (w 0 ^ 2 + w 1 ^ 2)),
        Real.sqrt (quarticKappa * quarticEta) * (w 1 * besselRatio (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) /
            Real.sqrt (w 0 ^ 2 + w 1 ^ 2))] := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  rw [featureMean_eq_measureMean, gibbs_eq_FIN066]
  have e0 : 1 + Real.sqrt quarticKappa * (amap_FIN066 w) 0 = w 0 := by
    simp [amap_FIN066]; field_simp; ring
  have e1 : Real.sqrt (quarticKappa * quarticEta) * (amap_FIN066 w) 1 = w 1 := by
    simp [amap_FIN066]; field_simp
  rw [e0, e1]
  obtain ⟨m1, m2⟩ := mean_closed_EX026 (w 0) (w 1)
  have hint : Integrable featPhi_FIN066
      (xyBivariateLaw_EX023 (w 0) (w 1) : Measure (Torus 1)) :=
    integrable_feature _ continuous_Phi_FIN066
  have h0 := (EuclideanSpace.proj (0 : Fin 2)).integral_comp_comm hint
  have h1 := (EuclideanSpace.proj (1 : Fin 2)).integral_comp_comm hint
  unfold measureMean
  ext i
  fin_cases i
  · have : ∫ x, (featPhi_FIN066 x) 0 ∂(xyBivariateLaw_EX023 (w 0) (w 1) : Measure (Torus 1)) =
        Real.sqrt quarticKappa * xyZ1 (xyBivariateLaw_EX023 (w 0) (w 1) : Measure (Torus 1)) := by
      simp only [featPhi_FIN066]
      simp
      rw [integral_const_mul]
      rfl
    simpa [this, m1] using h0.symm
  · have : ∫ x, (featPhi_FIN066 x) 1 ∂(xyBivariateLaw_EX023 (w 0) (w 1) : Measure (Torus 1)) =
        Real.sqrt (quarticKappa * quarticEta) *
          xyZ2 (xyBivariateLaw_EX023 (w 0) (w 1) : Measure (Torus 1)) := by
      simp only [featPhi_FIN066]
      simp
      rw [integral_const_mul]
      rfl
    simpa [this, m2] using h1.symm

theorem comp_Alin_eq_zero_FIN067 (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :
    L.comp Alin_FIN066 = 0 ↔ L = 0 := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  constructor
  · intro h
    ext u
    have hu : Alin_FIN066 !₂[Real.sqrt quarticKappa * u 0,
        Real.sqrt (quarticKappa * quarticEta) * u 1] = u := by
      rw [Alin_apply_FIN066]
      ext i
      fin_cases i
      · simp; field_simp
      · simp; field_simp
    have := congrArg (fun M => M !₂[Real.sqrt quarticKappa * u 0,
        Real.sqrt (quarticKappa * quarticEta) * u 1]) h
    simpa [hu] using this
  · intro h
    simp [h]


theorem crit_iff_FIN067 (w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ quarticPsi_FIN066 w = 0 ↔
      (w 0 - 1 = quarticKappa * (w 0 * besselRatio (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) /
            Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) ∧
       w 1 = quarticKappa * quarticEta * (w 1 * besselRatio (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) /
            Real.sqrt (w 0 ^ 2 + w 1 ^ 2))) := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  have sp := Real.sqrt_pos.2 hk
  have sp' := Real.sqrt_pos.2 hke
  have a := Real.mul_self_sqrt hk.le
  have a' := Real.mul_self_sqrt hke.le
  rw [fderiv_quarticPsi_FIN066, comp_Alin_eq_zero_FIN067,
    fderiv_psi_eq_zero_iff continuous_U_FIN066 continuous_Phi_FIN066, featureMean_amap_FIN067]
  generalize w 0 * besselRatio (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) /
    Real.sqrt (w 0 ^ 2 + w 1 ^ 2) = X
  generalize w 1 * besselRatio (Real.sqrt (w 0 ^ 2 + w 1 ^ 2)) /
    Real.sqrt (w 0 ^ 2 + w 1 ^ 2) = Y
  constructor
  · intro h
    have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
    have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h
    simp [amap_FIN066] at h0 h1
    rw [eq_div_iff sp.ne'] at h0
    rw [eq_div_iff sp'.ne'] at h1
    constructor
    · have e : quarticKappa * X = Real.sqrt quarticKappa * X * Real.sqrt quarticKappa := by
        rw [mul_right_comm, a]
      linarith
    · have e : quarticKappa * quarticEta * Y =
          Real.sqrt (quarticKappa * quarticEta) * Y * Real.sqrt (quarticKappa * quarticEta) := by
        rw [mul_right_comm (Real.sqrt (quarticKappa * quarticEta)) Y, a']
      linarith
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · simp [amap_FIN066]
      rw [eq_div_iff sp.ne', h0, mul_right_comm, a]
    · simp [amap_FIN066]
      rw [eq_div_iff sp'.ne', h1, mul_right_comm (Real.sqrt (quarticKappa * quarticEta)) Y, a']

theorem kappa_mul_b_FIN067 : quarticKappa * quarticB = 5 := by
  have hb : 0 < quarticB := besselRatio_pos 4 (by norm_num)
  show 5 / quarticB * quarticB = 5
  field_simp

theorem quarticB_eq_FIN067 : quarticB = besselRatio 4 := rfl

theorem axis_of_crit_FIN067 {w : EuclideanSpace ℝ (Fin 2)}
    (h : fderiv ℝ quarticPsi_FIN066 w = 0) : w 1 = 0 := by
  by_contra hy
  have hk := quarticKappa_pos_FIN066
  have hb : 0 < quarticB := besselRatio_pos 4 (by norm_num)
  have hkb := kappa_mul_b_FIN067
  obtain ⟨E1, E2⟩ := (crit_iff_FIN067 w).1 h
  have hpos : 0 < w 0 ^ 2 + w 1 ^ 2 := by
    have := sq_pos_of_ne_zero hy
    positivity
  have hRpos : 0 < Real.sqrt (w 0 ^ 2 + w 1 ^ 2) := Real.sqrt_pos.2 hpos
  have hR2 : Real.sqrt (w 0 ^ 2 + w 1 ^ 2) ^ 2 = w 0 ^ 2 + w 1 ^ 2 := Real.sq_sqrt hpos.le
  generalize Real.sqrt (w 0 ^ 2 + w 1 ^ 2) = R at hRpos hR2 E1 E2
  have hη : quarticEta = 4 / 5 := quarticEta_FIN066
  -- G = g(R)/R = b/4
  have hG : besselRatio R / R = besselRatio 4 / 4 := by
    have e : w 1 * (quarticKappa * quarticEta * (besselRatio R / R) - 1) = 0 := by
      have : w 1 * besselRatio R / R = w 1 * (besselRatio R / R) := mul_div_assoc _ _ _
      rw [this] at E2
      linarith
    have e2 := (mul_eq_zero.1 e).resolve_left hy
    have hkη : quarticKappa * quarticEta = 4 / quarticB := by
      rw [hη]; show 5 / quarticB * (4 / 5) = 4 / quarticB
      field_simp
    rw [hkη] at e2
    have : besselRatio R / R = quarticB / 4 := by
      field_simp at e2 ⊢
      linarith
    rw [this]; rfl
  have hR4 : R = 4 := by
    have := strictAntiOn_ratio.injOn (Set.mem_Ioi.2 hRpos) (Set.mem_Ioi.2 (by norm_num : (0:ℝ) < 4))
      (by simpa using hG)
    exact this
  subst hR4
  have hx : w 0 = -4 := by
    have : w 0 * besselRatio 4 / 4 = w 0 * (besselRatio 4 / 4) := mul_div_assoc _ _ _
    rw [this] at E1
    have h4 : quarticKappa * (besselRatio 4 / 4) = 5 / 4 := by
      rw [← quarticB_eq_FIN067]
      field_simp
      linarith
    have : w 0 - 1 = 5 / 4 * w 0 := by
      calc w 0 - 1 = quarticKappa * (w 0 * (besselRatio 4 / 4)) := E1
        _ = (quarticKappa * (besselRatio 4 / 4)) * w 0 := by ring
        _ = 5 / 4 * w 0 := by rw [h4]
    linarith
  have : w 1 ^ 2 = 0 := by nlinarith
  exact hy (pow_eq_zero_iff (two_ne_zero) |>.1 this)

theorem vec_zero_FIN067 (a b : ℝ) : (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) 0 = a := rfl

theorem vec_one_FIN067 (a b : ℝ) : (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) 1 = b := rfl

theorem crit_axis_iff_FIN067 {s : ℝ} (hs : 0 < s) :
    fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 ↔ quarticKappa * besselRatio s - s = 1 := by
  rw [crit_iff_FIN067, vec_zero_FIN067, vec_one_FIN067]
  have hR : Real.sqrt ((-s) ^ 2 + (0 : ℝ) ^ 2) = s := by
    rw [show (-s) ^ 2 + (0 : ℝ) ^ 2 = s ^ 2 by ring]
    exact Real.sqrt_sq hs.le
  rw [hR]
  have e : -s * besselRatio s / s = -besselRatio s := by field_simp
  rw [e]
  constructor
  · rintro ⟨h, -⟩
    linarith
  · intro h
    refine ⟨by linarith, by simp⟩


theorem fin065_FIN067 :
    0 < 1 / quarticKappa - deriv besselRatio 4 ∧ quarticKappa * deriv besselRatio 4 < 1 / 2 := by
  obtain ⟨-, -, -, -, -, -, -, ⟨hA, -, -⟩, -, ⟨-, hv⟩⟩ :=
    DGPS.FiniteN.quartic_explicit_model_rational_certificate
  exact ⟨hA, by linarith⟩

theorem lt_one_of_gt_four_FIN067 {s : ℝ} (hs : 4 < s) :
    quarticKappa * besselRatio s - s < 1 := by
  have hk := quarticKappa_pos_FIN066
  obtain ⟨-, hv⟩ := fin065_FIN067
  have hkb : quarticKappa * besselRatio 4 = 5 := kappa_mul_b_FIN067
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope besselRatio hs
    continuous_besselRatio.continuousOn
    (fun x _ => (hasDerivAt_ratio x).differentiableAt.differentiableWithinAt)
  rw [deriv_ratio] at hcd
  have h1 : ratioDeriv c < ratioDeriv 4 :=
    strictAntiOn_ratioDeriv (Set.mem_Ici.2 (by norm_num)) (Set.mem_Ici.2 (by linarith [hc.1])) hc.1
  have h2 : ratioDeriv 4 = deriv besselRatio 4 := (deriv_ratio 4).symm
  have hs4 : 0 < s - 4 := by linarith
  have h3 := (eq_div_iff hs4.ne').1 hcd
  have h4 := mul_lt_mul_of_pos_right h1 hs4
  have h5 : besselRatio s - besselRatio 4 < deriv besselRatio 4 * (s - 4) := by
    rw [← h2]; linarith
  have h6 := mul_lt_mul_of_pos_left h5 hk
  have h7 := mul_lt_mul_of_pos_right hv hs4
  nlinarith

noncomputable def hfun_FIN067 (t : ℝ) : ℝ := quarticKappa * besselRatio t - t - 1

theorem hasDerivAt_hfun_FIN067 (t : ℝ) :
    HasDerivAt hfun_FIN067 (quarticKappa * ratioDeriv t - 1) t := by
  have h := (((hasDerivAt_ratio t).const_mul quarticKappa).sub (hasDerivAt_id t)).sub_const 1
  exact h

theorem strictConcaveOn_hfun_FIN067 : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) hfun_FIN067 := by
  have hk := quarticKappa_pos_FIN066
  have hd : ∀ t, deriv hfun_FIN067 t = quarticKappa * ratioDeriv t - 1 :=
    fun t => (hasDerivAt_hfun_FIN067 t).deriv
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_hfun_FIN067 t).continuousAt).continuousOn ?_
  rw [interior_Ici]
  intro a ha b hb hab
  rw [hd, hd]
  have := strictAntiOn_ratioDeriv (Set.mem_Ici.2 (Set.mem_Ioi.1 ha).le)
    (Set.mem_Ici.2 (Set.mem_Ioi.1 hb).le) hab
  nlinarith [mul_lt_mul_of_pos_left this hk]

theorem no_three_FIN067 {x y z : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z)
    (h1 : hfun_FIN067 x = 0) (h2 : hfun_FIN067 y = 0) (h3 : hfun_FIN067 z = 0) : False := by
  have hz : 0 ≤ z := by linarith
  have hxz : 0 < z - x := by linarith
  have hα : 0 < (z - y) / (z - x) := div_pos (by linarith) hxz
  have hβ : 0 < (y - x) / (z - x) := div_pos (by linarith) hxz
  have hne : z - x ≠ 0 := hxz.ne'
  have hsum : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hne]; ring
  have key := strictConcaveOn_hfun_FIN067.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hz)
    (by linarith : x ≠ z) hα hβ hsum
  simp only [smul_eq_mul] at key
  have hmix : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    field_simp
    ring
  rw [hmix, h1, h3, h2] at key
  simp at key

theorem hfun_four_FIN067 : hfun_FIN067 4 = 0 := by
  have hkb : quarticKappa * besselRatio 4 = 5 := kappa_mul_b_FIN067
  unfold hfun_FIN067
  linarith

theorem finite_roots_FIN067 :
    {s : ℝ | 0 < s ∧ quarticKappa * besselRatio s - s = 1}.Finite := by
  have no3 : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → hfun_FIN067 x = 0 → hfun_FIN067 y = 0 →
      hfun_FIN067 z = 0 → x ≠ y → x ≠ z → y ≠ z → False := by
    intro x y z hx hy hz hx0 hy0 hz0 hxy hxz hyz
    rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
      rcases lt_or_gt_of_ne hyz with h3 | h3 <;>
      first
      | (exfalso; linarith)
      | exact no_three_FIN067 hx.le (by linarith) (by linarith) hx0 hy0 hz0
      | exact no_three_FIN067 hx.le (by linarith) (by linarith) hx0 hz0 hy0
      | exact no_three_FIN067 hy.le (by linarith) (by linarith) hy0 hx0 hz0
      | exact no_three_FIN067 hy.le (by linarith) (by linarith) hy0 hz0 hx0
      | exact no_three_FIN067 hz.le (by linarith) (by linarith) hz0 hx0 hy0
      | exact no_three_FIN067 hz.le (by linarith) (by linarith) hz0 hy0 hx0
  have hroot : ∀ s : ℝ, quarticKappa * besselRatio s - s = 1 ↔ hfun_FIN067 s = 0 := by
    intro s; unfold hfun_FIN067; constructor <;> intro h <;> linarith
  by_cases hex : ∃ s0, 0 < s0 ∧ hfun_FIN067 s0 = 0 ∧ s0 ≠ 4
  · obtain ⟨s0, hs0, hz0, hne⟩ := hex
    refine ((Set.finite_singleton s0).insert 4).subset ?_
    rintro s ⟨hs, hr⟩
    by_contra hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    exact no3 s s0 4 hs hs0 (by norm_num) ((hroot s).1 hr) hz0 hfun_four_FIN067 hmem.2 hmem.1 hne
  · refine (Set.finite_singleton 4).subset ?_
    rintro s ⟨hs, hr⟩
    by_contra hne
    exact hex ⟨s, hs, (hroot s).1 hr, hne⟩

theorem le_four_of_crit_FIN067 {s : ℝ} (hs : 0 < s)
    (h : fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0) : s ≤ 4 := by
  by_contra hlt
  have := lt_one_of_gt_four_FIN067 (not_le.1 hlt)
  have h' := (crit_axis_iff_FIN067 hs).1 h
  linarith

theorem hessian_axis_FIN067 {s : ℝ} (hs : 0 < s) (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-s, 0] v v =
      (1 / quarticKappa - deriv besselRatio s) * v 0 ^ 2 +
        (1 / (quarticKappa * quarticEta) - besselRatio s / s) * v 1 ^ 2 := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  have hs0 : -s ≠ 0 := neg_ne_zero.2 hs.ne'
  have hk0 : quarticKappa ≠ 0 := hk.ne'
  have hη0 : quarticEta ≠ 0 := by rw [quarticEta_FIN066]; norm_num
  rw [hessian_quarticPsi_FIN066, amapRoot_FIN066,
    hessian_psi continuous_U_FIN066 continuous_Phi_FIN066, featureCov_zOf_FIN066 hs0,
    besselRatio_neg, deriv_ratio]
  have hrd : ratioDeriv s = 1 - besselRatio s / s - besselRatio s ^ 2 := by
    unfold ratioDeriv; rw [ratio_div_eq s hs.ne']
  rw [hrd, neg_div_neg_eq]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Alin_apply_FIN066]
  simp [div_pow, Real.sq_sqrt hk.le, Real.sq_sqrt hke.le]
  field_simp
  ring

theorem transverse_FIN067 {s : ℝ} (hs : 0 < s) (hr : quarticKappa * besselRatio s - s = 1) :
    1 / (quarticKappa * quarticEta) - besselRatio s / s = (s - 4) / (4 * quarticKappa * s) := by
  have hk := quarticKappa_pos_FIN066
  have hg : besselRatio s = (1 + s) / quarticKappa := by
    field_simp; linarith
  rw [hg, quarticEta_FIN066]
  field_simp
  ring

end DGPS.FiniteN.QuarticSaddleCriticalFIN067

namespace DGPS.FiniteN

open DGPS.Models DGPS.Circle.BesselMoments DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.QuarticSaddleCriticalFIN067

/-- **FIN067 (complete critical point exclusion).**  For the auxiliary function
`ψ = quarticPsi_FIN066` of the anisotropic quartic saddle:
1. every critical point lies on the `x` axis;
2. for `s > 0`, `(-s, 0)` is critical iff `κ g(s) - s = 1`, and then `s ≤ 4`;
3. there are only finitely many negative-axis critical points;
4. at a negative-axis critical point `(-s,0)` the Hessian quadratic form is
   `(1/κ - g'(s)) v₀² + ((s-4)/(4κs)) v₁²`, so the transverse curvature is `< 0` for `s < 4`;
5. at `s = 4` the point is critical, the `x` curvature `A = 1/κ - g'(4)` is positive and the
   `y` curvature vanishes, so the Hessian has no negative direction. -/
theorem quartic_complete_critical_point_exclusion :
    (∀ w : EuclideanSpace ℝ (Fin 2), fderiv ℝ quarticPsi_FIN066 w = 0 → w 1 = 0) ∧
    (∀ s : ℝ, 0 < s → (fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 ↔
      quarticKappa * besselRatio s - s = 1)) ∧
    (∀ s : ℝ, 0 < s → fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 → s ≤ 4) ∧
    {s : ℝ | 0 < s ∧ fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0}.Finite ∧
    (∀ s : ℝ, 0 < s → fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 →
      ∀ v : EuclideanSpace ℝ (Fin 2),
        fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-s, 0] v v =
          (1 / quarticKappa - deriv besselRatio s) * v 0 ^ 2 +
            (s - 4) / (4 * quarticKappa * s) * v 1 ^ 2) ∧
    (∀ s : ℝ, 0 < s → s < 4 → fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 →
      fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-s, 0] !₂[0, 1] !₂[0, 1] =
          (s - 4) / (4 * quarticKappa * s) ∧
        (s - 4) / (4 * quarticKappa * s) < 0 ∧
        fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-s, 0] !₂[0, 1] !₂[0, 1] < 0) ∧
    (fderiv ℝ quarticPsi_FIN066 !₂[-4, 0] = 0 ∧
      0 < 1 / quarticKappa - deriv besselRatio 4 ∧
      fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-4, 0] !₂[1, 0] !₂[1, 0] =
        1 / quarticKappa - deriv besselRatio 4 ∧
      fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-4, 0] !₂[0, 1] !₂[0, 1] = 0 ∧
      (∀ v : EuclideanSpace ℝ (Fin 2),
        fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-4, 0] v v =
          (1 / quarticKappa - deriv besselRatio 4) * v 0 ^ 2) ∧
      (∀ v : EuclideanSpace ℝ (Fin 2),
        0 ≤ fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-4, 0] v v)) := by
  have hk := quarticKappa_pos_FIN066
  have hA := (fin065_FIN067).1
  have hform : ∀ s : ℝ, 0 < s → fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0 →
      ∀ v : EuclideanSpace ℝ (Fin 2),
        fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-s, 0] v v =
          (1 / quarticKappa - deriv besselRatio s) * v 0 ^ 2 +
            (s - 4) / (4 * quarticKappa * s) * v 1 ^ 2 := by
    intro s hs h v
    rw [hessian_axis_FIN067 hs, transverse_FIN067 hs ((crit_axis_iff_FIN067 hs).1 h)]
  have hcrit4 : fderiv ℝ quarticPsi_FIN066 !₂[-4, 0] = 0 := by
    rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num, crit_axis_iff_FIN067 (by norm_num)]
    have := kappa_mul_b_FIN067
    have e : quarticKappa * besselRatio 4 = 5 := this
    linarith
  have hform4 : ∀ v : EuclideanSpace ℝ (Fin 2),
      fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-4, 0] v v =
        (1 / quarticKappa - deriv besselRatio 4) * v 0 ^ 2 := by
    intro v
    have := hform 4 (by norm_num) (by simpa using hcrit4) v
    simpa using this
  refine ⟨fun w h => axis_of_crit_FIN067 h, fun s hs => crit_axis_iff_FIN067 hs,
    fun s hs h => le_four_of_crit_FIN067 hs h, ?_, hform, ?_, ?_⟩
  · refine finite_roots_FIN067.subset ?_
    rintro s ⟨hs, h⟩
    exact ⟨hs, (crit_axis_iff_FIN067 hs).1 h⟩
  · intro s hs hs4 h
    have hneg : (s - 4) / (4 * quarticKappa * s) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    have e : fderiv ℝ (fderiv ℝ quarticPsi_FIN066) !₂[-s, 0] !₂[0, 1] !₂[0, 1] =
        (s - 4) / (4 * quarticKappa * s) := by rw [hform s hs h]; simp
    exact ⟨e, hneg, e ▸ hneg⟩
  · refine ⟨hcrit4, hA, ?_, ?_, hform4, ?_⟩
    · rw [hform4]; simp
    · rw [hform4]; simp
    · intro v
      rw [hform4]
      exact mul_nonneg hA.le (sq_nonneg _)

end DGPS.FiniteN
