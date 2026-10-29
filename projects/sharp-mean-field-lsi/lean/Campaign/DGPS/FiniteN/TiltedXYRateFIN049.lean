import DGPS.FiniteN.TiltedXYCriticalFIN048
import DGPS.FiniteN.CriticalXYMoment
import DGPS.FiniteN.Tools.PoincareGlobal
import DGPS.FiniteN.Tools.NegativeDirection
import DGPS.FiniteN.Tools.Exterior
import DGPS.FiniteN.Tools.QuadraticLaplace
import DGPS.FiniteN.Tools.IMS

/-!
# FIN049: the tilted auxiliary rate is at least `N`

For the fixed tilted XY auxiliary law `η_N ∝ exp (-N ψ)`, `ψ = tiltPsi 4 (1/2)` on the plane,
we assemble the complete critical geometry (FIN048), the negative-direction local Dirichlet rate
(FIN022), the exterior rate (FIN023) and the centered IMS globalization (FIN024) to prove
`tilted_auxiliary_rate_at_least_n`: a Poincare inequality with rate `c N` for all large `N`, on
smooth compactly supported mean-zero test functions.
-/

open scoped ContDiff RealInnerProductSpace
open MeasureTheory Metric Set

namespace DGPS.FiniteN.TiltedXY.Fin049

/-- Conversion of `imsEta` integrals into unnormalized integrals. -/
theorem imsEta_integral_FIN049 {k : ℕ} (N : ℝ) (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (g : EuclideanSpace ℝ (Fin k) → ℝ) :
    ∫ x, g x ∂(DGPS.FiniteN.imsEta N ψ) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * ψ x))))⁻¹.toReal *
        ∫ x, g x * Real.exp (-(N * ψ x)) := by
  have hdens : Measurable fun x => ENNReal.ofReal (Real.exp (-(N * ψ x))) :=
    (Real.continuous_exp.comp (continuous_const.mul hψ.continuous).neg).measurable.ennreal_ofReal
  unfold DGPS.FiniteN.imsEta
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hdens
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  ring

/-- Mass of a measurable set under `imsEta`, as a ratio of Laplace integrals. -/
theorem imsEta_real_FIN049 {k : ℕ} (N : ℝ) (ψ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hZ : 0 < ∫ x, Real.exp (-(N * ψ x)))
    (S : Set (EuclideanSpace ℝ (Fin k))) (hS : MeasurableSet S) :
    (DGPS.FiniteN.imsEta N ψ S).toReal =
      (∫ x in S, Real.exp (-(N * ψ x))) / ∫ x, Real.exp (-(N * ψ x)) := by
  have hint : Integrable (fun x => Real.exp (-(N * ψ x))) := by
    by_contra h
    rw [integral_undef h] at hZ
    exact lt_irrefl _ hZ
  have hnn : 0 ≤ᵐ[volume] fun x => Real.exp (-(N * ψ x)) :=
    Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  have hZe : (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * ψ x)))) =
      ENNReal.ofReal (∫ x, Real.exp (-(N * ψ x))) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  have hSe : (∫⁻ x in S, ENNReal.ofReal (Real.exp (-(N * ψ x)))) =
      ENNReal.ofReal (∫ x in S, Real.exp (-(N * ψ x))) :=
    (ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_restrict_of_ae hnn)).symm
  unfold DGPS.FiniteN.imsEta
  rw [Measure.smul_apply, withDensity_apply _ hS, smul_eq_mul, hZe, hSe, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le,
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun x _ => (Real.exp_pos _).le)]
  ring

open DGPS.FiniteN.TiltedXY.Fin048 DGPS.Circle.BesselMoments

/-- The auxiliary potential. -/
noncomputable abbrev psi : Plane → ℝ := tiltPsi 4 (1 / 2)

theorem contDiff_psi_FIN049 : ContDiff ℝ ∞ psi := contDiff_tiltPsi 4 (1 / 2)

theorem cfun_abs_le_FIN049 (w : Plane) : |cfun 4 w| ≤ 1 / 4 := by
  unfold cfun
  have h1 := DGPS.FiniteN.critR_nonneg (‖w‖ ^ 2 / 4) (by positivity)
  have h2 := DGPS.FiniteN.critR_le_one (‖w‖ ^ 2 / 4) (by positivity)
  rw [abs_le]
  constructor <;> linarith

theorem hess_term_FIN049 (w v u : Plane) :
    |deriv DGPS.FiniteN.critR (‖w‖ ^ 2 / 4) / 4 * (⟪w, v⟫ * ⟪w, u⟫)| ≤ 1 / 2 * (‖v‖ * ‖u‖) := by
  by_cases hw : w = 0
  · subst hw
    simp
    positivity
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  set r := ‖w‖ with hrdef
  set D := deriv DGPS.FiniteN.critR (r ^ 2 / 4) with hD
  have hD0 : D ≤ 0 := DGPS.FiniteN.critR_deriv_nonpos _ (by positivity)
  have hax := critR_deriv_axis_FIN048 hr
  have hg1 := DGPS.Circle.BesselConcavity.ratioDeriv_pos r hr
  have hg2 := DGPS.Circle.BesselConcavity.ratioDeriv_lt_half r hr
  have hg3 := DGPS.Circle.BesselMonotonicity.ratio_lt_half r hr
  have hg4 := DGPS.Circle.BesselMonotonicity.besselRatio_pos r hr
  rw [DGPS.Circle.BesselConcavity.deriv_ratio] at hax
  have hq : -(D * r ^ 2 / 4) ≤ 1 / 2 := by
    have : 0 < besselRatio r / r := div_pos hg4 hr
    linarith
  have hv : |⟪w, v⟫| ≤ r * ‖v‖ := abs_real_inner_le_norm w v
  have hu : |⟪w, u⟫| ≤ r * ‖u‖ := abs_real_inner_le_norm w u
  have hvu : |⟪w, v⟫ * ⟪w, u⟫| ≤ r ^ 2 * (‖v‖ * ‖u‖) := by
    rw [abs_mul]
    calc |⟪w, v⟫| * |⟪w, u⟫| ≤ (r * ‖v‖) * (r * ‖u‖) :=
          mul_le_mul hv hu (abs_nonneg _) (by positivity)
      _ = r ^ 2 * (‖v‖ * ‖u‖) := by ring
  rw [abs_mul, abs_of_nonpos (by linarith : D / 4 ≤ 0)]
  have hnn : 0 ≤ -(D / 4) := by linarith
  calc -(D / 4) * |⟪w, v⟫ * ⟪w, u⟫| ≤ -(D / 4) * (r ^ 2 * (‖v‖ * ‖u‖)) :=
        mul_le_mul_of_nonneg_left hvu hnn
    _ = -(D * r ^ 2 / 4) * (‖v‖ * ‖u‖) := by ring
    _ ≤ 1 / 2 * (‖v‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_right hq (by positivity)

theorem hess_bound_FIN049 (w : Plane) : ‖fderiv ℝ (fderiv ℝ psi) w‖ ≤ 3 / 4 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have h := tiltPsi_hessian_apply 4 (1 / 2) (by norm_num) w v u
  have h1 := cfun_abs_le_FIN049 w
  have h2 := hess_term_FIN049 w v u
  have h3 : |⟪v, u⟫| ≤ ‖v‖ * ‖u‖ := abs_real_inner_le_norm v u
  show ‖(fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) w v) u‖ ≤ _
  rw [h, Real.norm_eq_abs]
  calc |cfun 4 w * ⟪v, u⟫ - deriv DGPS.FiniteN.critR (‖w‖ ^ 2 / 4) / 4 * (⟪w, v⟫ * ⟪w, u⟫)|
      ≤ |cfun 4 w * ⟪v, u⟫| + |deriv DGPS.FiniteN.critR (‖w‖ ^ 2 / 4) / 4 * (⟪w, v⟫ * ⟪w, u⟫)| :=
        abs_sub _ _
    _ ≤ 1 / 4 * (‖v‖ * ‖u‖) + 1 / 2 * (‖v‖ * ‖u‖) := by
        gcongr
        rw [abs_mul]
        exact mul_le_mul h1 h3 (abs_nonneg _) (by norm_num)
    _ = 3 / 4 * ‖v‖ * ‖u‖ := by ring

theorem far_gradient_FIN049 (w : Plane) (hw : 8 ≤ ‖w‖) :
    1 / 16 * ‖w‖ ≤ ‖fderiv ℝ psi w‖ := by
  have hr : 0 < ‖w‖ := by linarith
  set r := ‖w‖ with hrdef
  set v : Plane := r⁻¹ • w with hv
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hwv : ⟪w, v⟫ = r := by
    rw [hv, inner_smul_right, real_inner_self_eq_norm_sq, ← hrdef]
    field_simp
  have hcf : 1 / 8 ≤ cfun 4 w := by
    unfold cfun
    rw [rho_eq_FIN048 hr]
    have h1 := DGPS.Circle.BesselMonotonicity.besselRatio_lt_one r
    have h2 : besselRatio r / r ≤ 1 / 8 := by
      rw [div_le_iff₀ hr]; nlinarith
    linarith
  have h := fderiv_tiltPsi_apply 4 (1 / 2) (by norm_num) w v
  have h3 : |⟪e1, v⟫| ≤ 1 := by
    have := abs_real_inner_le_norm e1 v
    rwa [norm_e1, hvn, mul_one] at this
  have h4 : 1 / 16 * r ≤ |fderiv ℝ psi w v| := by
    have h5 : fderiv ℝ psi w v = cfun 4 w * r - 1 / 2 / 4 * ⟪e1, v⟫ := by
      rw [← hwv]; exact h
    rw [h5]
    have := (abs_le.1 h3).2
    refine le_trans ?_ (le_abs_self _)
    nlinarith
  calc 1 / 16 * r ≤ |fderiv ℝ psi w v| := h4
    _ = ‖fderiv ℝ psi w v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ psi w‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ psi w‖ := by rw [hvn, mul_one]

open Filter Topology Function

theorem fderiv_psi_contDiff_FIN049 : ContDiff ℝ ∞ (fderiv ℝ psi) :=
  contDiff_psi_FIN049.fderiv_right (by simp)

theorem hess_continuous_FIN049 : Continuous (fderiv ℝ (fderiv ℝ psi)) :=
  fderiv_psi_contDiff_FIN049.continuous_fderiv (by simp)

theorem neg_dir_nbhd_FIN049 (p : Plane) (hp : fderiv ℝ (fderiv ℝ psi) p e2 e2 < 0) :
    ∃ r > 0, ∃ c > 0, ∀ x ∈ ball p r, fderiv ℝ (fun y => fderiv ℝ psi y e2) x e2 ≤ -c := by
  have hid : ∀ x, fderiv ℝ (fun y => fderiv ℝ psi y e2) x e2 =
      fderiv ℝ (fderiv ℝ psi) x e2 e2 := by
    intro x
    rw [fderiv_clm_apply (fderiv_psi_contDiff_FIN049.differentiable (by simp) x)
      (differentiableAt_const e2)]
    simp
  have hcont : Continuous fun x => fderiv ℝ (fderiv ℝ psi) x e2 e2 :=
    (hess_continuous_FIN049.clm_apply continuous_const).clm_apply continuous_const
  have hev : ∀ᶠ x in 𝓝 p, fderiv ℝ (fderiv ℝ psi) x e2 e2 <
      fderiv ℝ (fderiv ℝ psi) p e2 e2 / 2 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by linarith)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨r, hr, -(fderiv ℝ (fderiv ℝ psi) p e2 e2 / 2), by linarith, fun x hx => ?_⟩
  rw [hid]
  linarith [hb x hx]

theorem hess_ball_FIN049 (p : Plane) (m : ℝ) (hm : 0 < m)
    (hp : ∀ v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ psi) p v v) :
    ∃ r > 0, ∀ x ∈ ball p r, ∀ v, m / 2 * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ psi) x v v := by
  obtain ⟨r, hr, hb⟩ := (Metric.continuousAt_iff (α := Plane) (β := Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (f := fderiv ℝ (fderiv ℝ psi)) (a := p)).1
    (hess_continuous_FIN049.continuousAt) (m / 2)
    (by linarith)
  refine ⟨r, hr, fun x hx v => ?_⟩
  have h1 : ‖fderiv ℝ (fderiv ℝ psi) x - fderiv ℝ (fderiv ℝ psi) p‖ < m / 2 := by
    exact (dist_eq_norm (fderiv ℝ (fderiv ℝ psi) x) (fderiv ℝ (fderiv ℝ psi) p)).symm.trans_lt
      (hb hx)
  have h2 : |(fderiv ℝ (fderiv ℝ psi) x - fderiv ℝ (fderiv ℝ psi) p) v v| ≤
      ‖fderiv ℝ (fderiv ℝ psi) x - fderiv ℝ (fderiv ℝ psi) p‖ * ‖v‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc ‖(fderiv ℝ (fderiv ℝ psi) x - fderiv ℝ (fderiv ℝ psi) p) v v‖
        ≤ ‖(fderiv ℝ (fderiv ℝ psi) x - fderiv ℝ (fderiv ℝ psi) p) v‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ psi) x - fderiv ℝ (fderiv ℝ psi) p‖ * ‖v‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  have h3 : ‖fderiv ℝ (fderiv ℝ psi) x - fderiv ℝ (fderiv ℝ psi) p‖ * ‖v‖ ^ 2 ≤ m / 2 * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h1.le (by positivity)
  have h4 := (abs_le.1 (h2.trans h3)).1
  simp only [sub_apply] at h4
  have := hp v
  linarith

theorem coercive_of_pos_FIN049 (B : Plane →L[ℝ] Plane →L[ℝ] ℝ) (hB : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ B v v := by
  have hcont : Continuous fun v : Plane => B v v := (B.continuous.clm_apply continuous_id)
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : Plane) 1).exists_isMinOn
    ⟨e1, by simp [norm_e1]⟩ hcont.continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu1; simp at hu1
  refine ⟨B u u, hB u hu0, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
  have h1 := hmin (show ‖v‖⁻¹ • v ∈ sphere (0 : Plane) 1 by simpa using hw)
  have h2 : B v v = ‖v‖ ^ 2 * B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  rw [h2]
  have : B u u ≤ B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) := h1
  nlinarith [sq_nonneg ‖v‖]

theorem gradient_gap_FIN049 (U : Set Plane) (hU : IsOpen U)
    (hcrit : ∀ x, fderiv ℝ psi x = 0 → x ∈ U) :
    ∃ c₀ > 0, ∀ x, x ∉ U → c₀ < ‖fderiv ℝ psi x‖ := by
  have hgc : Continuous fun x => ‖fderiv ℝ psi x‖ :=
    (contDiff_psi_FIN049.continuous_fderiv (by simp)).norm
  set S : Set Plane := closedBall 0 8 \ U with hS
  have hSc : IsCompact S := (isCompact_closedBall _ _).diff hU
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨1 / 4, by norm_num, fun x hx => ?_⟩
    have hx8 : 8 < ‖x‖ := by
      by_contra hle
      push Not at hle
      have : x ∈ S := ⟨by simpa using hle, hx⟩
      rw [hS0] at this
      exact this
    have := far_gradient_FIN049 x hx8.le
    linarith
  · obtain ⟨y, hy, hmin⟩ := hSc.exists_isMinOn hSne hgc.continuousOn
    have hypos : 0 < ‖fderiv ℝ psi y‖ := by
      rcases (norm_nonneg (fderiv ℝ psi y)).eq_or_lt with h | h
      · exact absurd (hcrit y (norm_eq_zero.1 h.symm)) hy.2
      · exact h
    refine ⟨min (1 / 4) (‖fderiv ℝ psi y‖ / 2), by positivity, fun x hx => ?_⟩
    by_cases hx8 : 8 ≤ ‖x‖
    · have := far_gradient_FIN049 x hx8
      have h2 := min_le_left (1 / 4 : ℝ) (‖fderiv ℝ psi y‖ / 2)
      linarith
    · push Not at hx8
      have hxS : x ∈ S := ⟨by simpa using hx8.le, hx⟩
      have h1 : ‖fderiv ℝ psi y‖ ≤ ‖fderiv ℝ psi x‖ := hmin hxS
      have h2 := min_le_right (1 / 4 : ℝ) (‖fderiv ℝ psi y‖ / 2)
      linarith

theorem geometry_FIN049 :
    ∃ (w0 p₁ p₂ : Plane) (r₀ r₁ r₂ c₁ n₁ n₂ c₀ : ℝ),
      0 < r₀ ∧ 0 < r₁ ∧ 0 < r₂ ∧ 0 < c₁ ∧ 0 < n₁ ∧ 0 < n₂ ∧ 0 < c₀ ∧
      (∀ u, psi w0 ≤ psi u) ∧ (∀ w, (∀ u, psi w ≤ psi u) → w = w0) ∧
      (∀ x ∈ ball w0 r₀, ∀ v, c₁ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ psi) x v v) ∧
      (∀ x ∈ ball p₁ r₁, fderiv ℝ (fun y => fderiv ℝ psi y e2) x e2 ≤ -n₁) ∧
      (∀ x ∈ ball p₂ r₂, fderiv ℝ (fun y => fderiv ℝ psi y e2) x e2 ≤ -n₂) ∧
      (∀ x, x ∉ ball w0 r₀ ∪ ball p₁ r₁ ∪ ball p₂ r₂ → c₀ < ‖fderiv ℝ psi x‖) := by
  obtain ⟨t₀, s₁, s₂, ht₀, hs₁0, hs₁1, hs₂1, hs₂4, -, -, -, hcrit, hmin, huniq, hpos, hrem⟩ :=
    tilted_xy_complete_critical_geometry
  have hs₂0 : 0 < s₂ := by linarith
  obtain ⟨m, hm, hmv⟩ := coercive_of_pos_FIN049 (fderiv ℝ (fderiv ℝ psi) (t₀ • e1)) hpos
  obtain ⟨r₀, hr₀, hball⟩ := hess_ball_FIN049 (t₀ • e1) m hm hmv
  obtain ⟨-, -, h1a, h1b, -⟩ := hrem s₁ (Or.inl rfl)
  obtain ⟨-, -, h2a, h2b, -⟩ := hrem s₂ (Or.inr rfl)
  have n1 : fderiv ℝ (fderiv ℝ psi) ((-s₁) • e1) e2 e2 < 0 := by
    rw [h1a]; exact h1b
  have n2 : fderiv ℝ (fderiv ℝ psi) ((-s₂) • e1) e2 e2 < 0 := by
    rw [h2a]; exact h2b
  obtain ⟨r₁, hr₁, c1, hc1, hn1⟩ := neg_dir_nbhd_FIN049 _ n1
  obtain ⟨r₂, hr₂, c2, hc2, hn2⟩ := neg_dir_nbhd_FIN049 _ n2
  have hU : IsOpen (ball (t₀ • e1) r₀ ∪ ball ((-s₁) • e1) r₁ ∪ ball ((-s₂) • e1) r₂) :=
    ((isOpen_ball.union isOpen_ball).union isOpen_ball)
  have hcr : ∀ x, fderiv ℝ psi x = 0 →
      x ∈ ball (t₀ • e1) r₀ ∪ ball ((-s₁) • e1) r₁ ∪ ball ((-s₂) • e1) r₂ := by
    intro x hx
    have : x ∈ ({t₀ • e1, (-s₁) • e1, (-s₂) • e1} : Set Plane) := by
      rw [← hcrit]; exact hx
    rcases this with h | h | h
    · rw [h]; exact Or.inl (Or.inl (mem_ball_self hr₀))
    · rw [h]; exact Or.inl (Or.inr (mem_ball_self hr₁))
    · rw [h]; exact Or.inr (mem_ball_self hr₂)
  obtain ⟨c₀, hc₀, hgap⟩ := gradient_gap_FIN049 _ hU hcr
  refine ⟨t₀ • e1, (-s₁) • e1, (-s₂) • e1, r₀, r₁, r₂, m / 2, c1, c2, c₀, hr₀, hr₁, hr₂,
    by positivity, hc1, hc2, hc₀, hmin, ?_, hball, hn1, hn2, hgap⟩
  intro w hw
  exact huniq w hw

theorem growth_FIN049 (w0 : Plane) :
    ∃ b > 0, ∃ C : ℝ, ∀ w, b * dist w w0 ^ 2 - C ≤ psi w - psi w0 := by
  set d0 : ℝ := ‖(1 / 2 : ℝ) • e1 - w0‖ with hd0
  refine ⟨1 / 32, by norm_num, d0 ^ 2 / 16 + 9 / 2 + psi w0, fun w => ?_⟩
  set a : ℝ := ‖w - (1 / 2 : ℝ) • e1‖ with ha
  have h1 : ‖w‖ ≤ a + 1 / 2 := by
    have := norm_le_norm_add_norm_sub' w ((1 / 2 : ℝ) • e1)
    have h2 : ‖(1 / 2 : ℝ) • e1‖ = 1 / 2 := by
      rw [norm_smul, norm_e1]; norm_num
    linarith
  have h2 := log_besselI_zero_le_FIN048 ‖w‖
  rw [abs_of_nonneg (norm_nonneg w)] at h2
  have h3 : dist w w0 ≤ a + d0 := by
    rw [dist_eq_norm]
    calc ‖w - w0‖ = ‖(w - (1 / 2 : ℝ) • e1) + ((1 / 2 : ℝ) • e1 - w0)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h4 : dist w w0 ^ 2 ≤ 2 * a ^ 2 + 2 * d0 ^ 2 := by
    have := dist_nonneg (x := w) (y := w0)
    have h5 : dist w w0 ^ 2 ≤ (a + d0) ^ 2 := pow_le_pow_left₀ this h3 2
    nlinarith [sq_nonneg (a - d0)]
  have h6 : psi w ≥ a ^ 2 / 8 - ‖w‖ := by
    show tiltPsi 4 (1 / 2) w ≥ _
    unfold tiltPsi
    rw [← ha]
    linarith
  have h7 : 0 ≤ (a / 4 - 2) ^ 2 := sq_nonneg _
  nlinarith

theorem ims_normalize_nonneg_FIN049 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (hp0 : ∀ i x, 0 ≤ p i x) (hp1 : ∀ x, ∑ i, p i x = 1) :
    ∃ χ : ι → E → ℝ, (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧ (∀ x, ∑ i, χ i x ^ 2 = 1) ∧
      (∀ i, support (χ i) = support (p i)) ∧
      (∀ x i₁, (∀ i, i ≠ i₁ → p i x = 0) → χ i₁ x = 1) := by
  classical
  have hs : ∀ x, 0 < ∑ k, p k x ^ 2 := by
    intro x
    have : ∃ i, 0 < p i x := by
      by_contra h
      push Not at h
      have h0 : ∀ i, p i x = 0 := fun i => le_antisymm (h i) (hp0 i x)
      have := hp1 x
      simp [h0] at this
    obtain ⟨i, hi⟩ := this
    exact Finset.sum_pos' (fun k _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hsm : ContDiff ℝ ∞ (fun x => ∑ k, p k x ^ 2) :=
    ContDiff.sum fun k _ => (hp k).pow 2
  have hsq : ContDiff ℝ ∞ (fun x => Real.sqrt (∑ k, p k x ^ 2)) :=
    hsm.sqrt (fun x => (hs x).ne')
  have hpos : ∀ x, 0 < Real.sqrt (∑ k, p k x ^ 2) := fun x => Real.sqrt_pos.mpr (hs x)
  refine ⟨fun i x => p i x / Real.sqrt (∑ k, p k x ^ 2), fun i => (hp i).div hsq
    (fun x => (hpos x).ne'), fun i x => div_nonneg (hp0 i x) (hpos x).le, fun x => ?_, fun i => ?_, fun x i₁ h => ?_⟩
  · simp only [div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt (hs x).le, div_self (hs x).ne']
  · ext x
    simp [Function.mem_support, (hpos x).ne']
  · have h1 : p i₁ x = 1 := by
      have := hp1 x
      rw [Finset.sum_eq_single i₁ (fun i _ hi => h i hi) (by simp)] at this
      exact this
    have h2 : ∑ k, p k x ^ 2 = 1 := by
      rw [Finset.sum_eq_single i₁ (fun i _ hi => by simp [h i hi]) (by simp), h1]; norm_num
    simp [h1, h2]

theorem ims_cutoffs_nonneg_FIN049 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (U : Fin m → Set E) (hU : ∀ j, IsOpen (U j)) (hUc : ∀ j, IsCompact (closure (U j)))
    (W : Set E) (hW : IsOpen W) (hcov : Wᶜ ⊆ ⋃ j, U j) (j₀ : Fin m) (V : Set E)
    (hV : closure V ⊆ U j₀) :
    ∃ χ : Option (Fin m) → E → ℝ, (∀ i, ContDiff ℝ ∞ (χ i)) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ x, ∑ i, χ i x ^ 2 = 1) ∧
      (∀ j, tsupport (χ (some j)) ⊆ U j) ∧ tsupport (χ none) ⊆ W ∧
      (∀ x ∈ V, χ (some j₀) x = 1) ∧ ∃ C : ℝ, ∀ x, ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 ≤ C := by
  classical
  let U' : Option (Fin m) → Set E := fun i =>
    match i with
    | none => W \ closure V
    | some j => if j = j₀ then U j else U j \ closure V
  have hU' : ∀ i, IsOpen (U' i) := by
    intro i
    cases i with
    | none => exact hW.sdiff isClosed_closure
    | some j =>
      by_cases h : j = j₀
      · subst h; simpa [U'] using hU j
      · simpa [U', h] using (hU j).sdiff isClosed_closure
  have hcov' : ⋃ i, U' i = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ closure V
    · exact mem_iUnion.mpr ⟨some j₀, by simpa [U'] using hV hx⟩
    · by_cases hxW : x ∈ W
      · exact mem_iUnion.mpr ⟨none, hxW, hx⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hxW)
        refine mem_iUnion.mpr ⟨some j, ?_⟩
        by_cases h : j = j₀
        · subst h; simpa [U'] using hj
        · simp [U', h, hj, hx]
  obtain ⟨p, hp, hp0, hp1, hpU⟩ := DGPS.FiniteN.ims_exists_partition U' hU' hcov'
  obtain ⟨χ, hχ, hχ0, hχ1, hsupp, hone⟩ := ims_normalize_nonneg_FIN049 p hp hp0 hp1
  have htsupp : ∀ i, tsupport (χ i) = tsupport (p i) := fun i => by
    simp only [tsupport, hsupp i]
  have hUsub : ∀ j, U' (some j) ⊆ U j := by
    intro j; by_cases h : j = j₀ <;> simp [U', h]
  -- the compact set
  let Q : Set E := ⋃ j, closure (U j)
  have hQ : IsCompact Q := isCompact_iUnion hUc
  have hpQ : ∀ x, x ∉ Q → ∀ j, p (some j) x = 0 := by
    intro x hx j
    by_contra h
    exact hx (mem_iUnion.mpr ⟨j, subset_closure (hUsub j (hpU _ (subset_tsupport _ h)))⟩)
  have hQo : IsOpen Qᶜ := hQ.isClosed.isOpen_compl
  have hχQ : ∀ x, x ∉ Q → ∀ i, fderiv ℝ (χ i) x = 0 := by
    intro x hx i
    have hev : χ i =ᶠ[nhds x] fun _ => (if i = none then (1 : ℝ) else 0) := by
      filter_upwards [hQo.mem_nhds hx] with y hy
      have hy' : ∀ j, p (some j) y = 0 := hpQ y hy
      cases i with
      | none =>
        simpa using hone y none (fun i hi => by
          cases i with
          | none => exact absurd rfl hi
          | some j => exact hy' j)
      | some j =>
        have : support (χ (some j)) = support (p (some j)) := hsupp _
        by_contra hne
        have : y ∈ support (χ (some j)) := by simpa using hne
        rw [hsupp] at this
        exact this (hy' j)
    rw [hev.fderiv_eq]; simp
  refine ⟨χ, hχ, hχ0, hχ1, fun j => ?_, ?_, fun x hx => ?_, ?_⟩
  · rw [htsupp]; exact (hpU _).trans (hUsub j)
  · rw [htsupp]; exact (hpU none).trans sdiff_subset
  · refine hone x (some j₀) fun i hi => ?_
    cases i with
    | none =>
      by_contra h
      exact (hpU none (subset_tsupport _ h)).2 (subset_closure hx)
    | some j =>
      by_contra h
      have := hpU _ (subset_tsupport _ h)
      have hj : j ≠ j₀ := fun e => hi (by rw [e])
      simp [U', hj] at this
      exact this.2 (subset_closure hx)
  · have hc : Continuous fun x => ∑ i, ‖fderiv ℝ (χ i) x‖ ^ 2 :=
      continuous_finsetSum _ fun i _ =>
        ((hχ i).continuous_fderiv (by simp)).norm.pow 2
    obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ Q
    · exact (le_abs_self _).trans ((hC x hx).trans (le_max_left _ _))
    · simp [hχQ x hx]




theorem laplace_masses_FIN049 (w0 : Plane) (hmin : ∀ u, psi w0 ≤ psi u)
    (huniq : ∀ w, psi w = psi w0 → w = w0)
    (hH : ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ psi) w0 v v) :
    ∃ Nz : ℝ, 1 ≤ Nz ∧ (∀ N, Nz ≤ N → 0 < ∫ x, Real.exp (-(N * psi x))) ∧
      ∀ r > 0, ∃ c > 0, ∃ C > 0, ∃ N1 : ℝ, Nz ≤ N1 ∧ ∀ N, N1 ≤ N →
        (DGPS.FiniteN.imsEta N psi {x | r ≤ dist x w0}).toReal ≤ C * Real.exp (-(c * N)) := by
  have hψ2 : ContDiff ℝ 2 psi := contDiff_psi_FIN049.of_le (by simp)
  obtain ⟨b, hb, C, hgrow⟩ := growth_FIN049 w0
  obtain ⟨⟨L0, hL0, A0, hA0, Nz, hNz, hlb⟩, htail⟩ :=
    DGPS.FiniteN.quadratic_minimum_laplace_bounds_and_gap_tails (E := Plane) hψ2 hmin huniq hH
      ⟨b, hb, C, hgrow⟩
  have hZ : ∀ N, Nz ≤ N → 0 < ∫ x, Real.exp (-(N * psi x)) := by
    intro N hN
    have hN0 : 0 < N := by linarith
    have := (hlb N hN).1
    refine lt_of_lt_of_le ?_ this
    positivity
  refine ⟨Nz, hNz, hZ, fun r hr => ?_⟩
  obtain ⟨c, hc, C', hC', N0, hN0, ht⟩ := htail r hr
  refine ⟨c, hc, C', hC', max N0 Nz, le_max_right _ _, fun N hN => ?_⟩
  have hNz' : Nz ≤ N := (le_max_right _ _).trans hN
  have hN0' : N0 ≤ N := (le_max_left _ _).trans hN
  have hmeas : MeasurableSet {x : Plane | r ≤ dist x w0} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  rw [DGPS.FiniteN.TiltedXY.Fin049.imsEta_real_FIN049 N psi (hZ N hNz') _ hmeas]
  rw [div_le_iff₀ (hZ N hNz')]
  exact ht N hN0'

/-- A negative-direction patch gives the rate `c N` for the normalized Dirichlet form. -/
theorem patch_rate_FIN049 (p : Plane) (r n c : ℝ) (hn : 0 < n) (hc : c ≤ n / 2)
    (hneg : ∀ x ∈ ball p r, fderiv ℝ (fun y => fderiv ℝ psi y e2) x e2 ≤ -n)
    (N : ℝ) (hN : 0 ≤ N) (G : Plane → ℝ) (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (hGU : tsupport G ⊆ ball p r) :
    c * N ^ (1 : ℝ) * ∫ x, G x ^ 2 ∂(DGPS.FiniteN.imsEta N psi) ≤
      ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(DGPS.FiniteN.imsEta N psi) := by
  have h := DGPS.FiniteN.negative_direction_local_dirichlet_rate psi contDiff_psi_FIN049 e2
    norm_e2 (ball p r) n hn hneg N hN G hG hGc hGU
  rw [imsEta_integral_FIN049 N psi contDiff_psi_FIN049,
    imsEta_integral_FIN049 N psi contDiff_psi_FIN049 (fun x => ‖fderiv ℝ G x‖ ^ 2), Real.rpow_one]
  have hZ : 0 ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * psi x))))⁻¹.toReal := ENNReal.toReal_nonneg
  have hI : 0 ≤ ∫ x, G x ^ 2 * Real.exp (-(N * psi x)) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have h1 : c * N ≤ n * N / 2 := by nlinarith
  have h2 : c * N * ∫ x, G x ^ 2 * Real.exp (-(N * psi x)) ≤
      ∫ x, ‖fderiv ℝ G x‖ ^ 2 * Real.exp (-(N * psi x)) :=
    (mul_le_mul_of_nonneg_right h1 hI).trans (by linarith)
  calc c * N * ((∫⁻ x, ENNReal.ofReal (Real.exp (-(N * psi x))))⁻¹.toReal *
        ∫ x, G x ^ 2 * Real.exp (-(N * psi x)))
      = (∫⁻ x, ENNReal.ofReal (Real.exp (-(N * psi x))))⁻¹.toReal *
        (c * N * ∫ x, G x ^ 2 * Real.exp (-(N * psi x))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hZ

theorem assembly_FIN049 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ F : Plane → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        ∫ x, F x ∂(DGPS.FiniteN.imsEta N psi) = 0 →
        c * N ^ (1 : ℝ) * ∫ x, F x ^ 2 ∂(DGPS.FiniteN.imsEta N psi) ≤
          ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(DGPS.FiniteN.imsEta N psi) := by
  obtain ⟨w0, p₁, p₂, r₀, r₁, r₂, c₁, n₁, n₂, c₀, hr₀, hr₁, hr₂, hc₁, hn₁, hn₂, hc₀, hmin,
    huniq, hhess, hneg1, hneg2, hgap⟩ := geometry_FIN049
  have hH : ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ psi) w0 v v :=
    ⟨c₁, hc₁, hhess w0 (mem_ball_self hr₀)⟩
  obtain ⟨Nz, hNz1, hZ, hmasses⟩ := laplace_masses_FIN049 w0 hmin (fun w hw => huniq w (fun u => by rw [hw]; exact hmin u)) hH
  have hgc : Continuous fun x => ‖fderiv ℝ psi x‖ := fderiv_psi_contDiff_FIN049.continuous.norm
  -- the three patches
  let U : Fin 3 → Set Plane := ![ball w0 r₀, ball p₁ r₁, ball p₂ r₂]
  have hU0 : U 0 = ball w0 r₀ := rfl
  have hU1 : U 1 = ball p₁ r₁ := rfl
  have hU2 : U 2 = ball p₂ r₂ := rfl
  have hUj : ∀ j, ∃ p r, U j = ball p r := by
    intro j
    fin_cases j
    · exact ⟨_, _, hU0⟩
    · exact ⟨_, _, hU1⟩
    · exact ⟨_, _, hU2⟩
  have hUo : ∀ j, IsOpen (U j) := fun j => by
    obtain ⟨p, r, h⟩ := hUj j
    rw [h]; exact isOpen_ball
  have hUc : ∀ j, IsCompact (closure (U j)) := fun j => by
    obtain ⟨p, r, h⟩ := hUj j
    rw [h]; exact isBounded_ball.isCompact_closure
  let W : Set Plane := {x | c₀ < ‖fderiv ℝ psi x‖}
  have hWo : IsOpen W := isOpen_lt continuous_const hgc
  have hcov : Wᶜ ⊆ ⋃ j, U j := by
    intro x hx
    by_contra hxU
    have hx' : x ∉ ball w0 r₀ ∪ ball p₁ r₁ ∪ ball p₂ r₂ := by
      intro h
      apply hxU
      rcases h with (h | h) | h
      · exact mem_iUnion.2 ⟨0, h⟩
      · exact mem_iUnion.2 ⟨1, h⟩
      · exact mem_iUnion.2 ⟨2, h⟩
    exact hx (hgap x hx')
  have hV : closure (ball w0 (r₀ / 2)) ⊆ U 0 := by
    rw [hU0]
    exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  obtain ⟨χ, hχ, hχ0, hsum, hχU, hχW, hχV, C, hC⟩ :=
    ims_cutoffs_nonneg_FIN049 U hUo hUc W hWo hcov 0 (ball w0 (r₀ / 2)) hV
  -- exterior
  let K : Set Plane := closedBall 0 8 ∩ {x | c₀ ≤ ‖fderiv ℝ psi x‖}
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 8).inter_right (isClosed_le continuous_const hgc)
  have hWX : W ⊆ K ∪ {x | 8 ≤ ‖x‖} := by
    intro x hx
    by_cases h8 : ‖x‖ ≤ 8
    · exact Or.inl ⟨by simpa using h8, le_of_lt (show c₀ < ‖fderiv ℝ psi x‖ from hx)⟩
    · exact Or.inr (by simpa using (not_le.1 h8).le)
  obtain ⟨c', hc', N₂, hext0⟩ := DGPS.FiniteN.noncritical_and_far_exterior_dirichlet_rate psi
    contDiff_psi_FIN049 (3 / 4) hess_bound_FIN049 K hKc (min c₀ (1 / 16))
    (lt_min hc₀ (by norm_num)) (fun x hx => (min_le_left _ _).trans hx.2) 8 (by norm_num)
    (fun x hx => (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg x)).trans
      (far_gradient_FIN049 x hx))
  -- Laplace tails
  obtain ⟨cA, hcA, AA, hAA, NA, hNzA, htA⟩ := hmasses (r₀ / 2) (by linarith)
  obtain ⟨cB, hcB, AB, hAB, NB, hNzB, htB⟩ := hmasses r₀ hr₀
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℝ, ∀ N, N₁ ≤ N →
      Nz ≤ N ∧ NA ≤ N ∧ NB ≤ N ∧ 2 * AB / cB ≤ N ∧ N₂ ≤ N :=
    ⟨max Nz (max NA (max NB (max (2 * AB / cB) N₂))), fun N hN => by
      simpa [max_le_iff] using hN⟩
  have hfin : ∀ N : ℝ, IsFiniteMeasure (DGPS.FiniteN.imsEta N psi) := fun N =>
    DGPS.FiniteN.Tools.ConditionalPoincareMain.imsEta_finite N psi
  -- the common rate
  have hcc : 0 < min (min (n₁ / 2) (n₂ / 2)) c' := lt_min (lt_min (by positivity) (by positivity)) hc'
  refine DGPS.FiniteN.auxiliary_poincare_globalization_with_the_mean psi contDiff_psi_FIN049 U
    (K ∪ {x | 8 ≤ ‖x‖}) 0 χ C hχ hsum hC hχU (hχW.trans hWX) w0 r₀ c₁ hc₁ hU0 hhess
    (hχ0 _) N₁ AA cA (1 / 2) hcA (by norm_num) ?_ ?_ 1 (min (min (n₁ / 2) (n₂ / 2)) c')
    (by norm_num) le_rfl hcc ?_ ?_
  · -- mass of the minimum ball
    intro N hN
    obtain ⟨hNz, hNA, hNB, hNm, hN2⟩ := hN₁ N hN
    have hZN := hZ N hNz
    have hint : Integrable (fun x : Plane => Real.exp (-(N * psi x))) := by
      by_contra h
      rw [integral_undef h] at hZN
      exact lt_irrefl _ hZN
    have hmeas : MeasurableSet {x : Plane | r₀ ≤ dist x w0} :=
      (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
    have hcompl : {x : Plane | r₀ ≤ dist x w0} = (ball w0 r₀)ᶜ := by
      ext x; simp [mem_ball, not_lt]
    have hsum1 : (DGPS.FiniteN.imsEta N psi (ball w0 r₀)).toReal +
        (DGPS.FiniteN.imsEta N psi {x | r₀ ≤ dist x w0}).toReal = 1 := by
      rw [imsEta_real_FIN049 N psi hZN _ hmeas, imsEta_real_FIN049 N psi hZN _ measurableSet_ball,
        ← add_div, div_eq_one_iff_eq hZN.ne', hcompl]
      exact integral_add_compl measurableSet_ball hint
    have htail := htB N hNB
    have hAe : AB * Real.exp (-(cB * N)) ≤ 1 / 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have h1 := Real.add_one_le_exp (cB * N)
      have h2 : 2 * AB ≤ N * cB := (div_le_iff₀ hcB).1 hNm
      nlinarith
    linarith
  · -- the minimum patch cutoff is exponentially close to one
    intro N hN
    obtain ⟨hNz, hNA, hNB, hNm, hN2⟩ := hN₁ N hN
    have := hfin N
    refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)).trans (htA N hNA)
    intro x (hx : χ (some 0) x ≠ 1)
    show r₀ / 2 ≤ dist x w0
    by_contra h
    exact hx (hχV x (mem_ball.2 (not_le.1 h)))
  · -- the other patches
    intro j hj N hN G hG hGc hGU
    obtain ⟨hNz, hNA, hNB, hNm, hN2⟩ := hN₁ N hN
    have hN0 : 0 ≤ N := by linarith
    match j, hj with
    | 0, h => exact absurd rfl h
    | 1, _ =>
      exact patch_rate_FIN049 p₁ r₁ n₁ _ hn₁
        (((min_le_left _ _).trans (min_le_left _ _)))
        hneg1 N hN0 G hG hGc hGU
    | 2, _ =>
      exact patch_rate_FIN049 p₂ r₂ n₂ _ hn₂
        (((min_le_left _ _).trans (min_le_right _ _)))
        hneg2 N hN0 G hG hGc hGU
  · -- the exterior
    intro N hN G hG hGc hGX
    obtain ⟨hNz, hNA, hNB, hNm, hN2⟩ := hN₁ N hN
    have h := hext0 N hN2 G hG hGc hGX
    have hI : 0 ≤ ∫ x, G x ^ 2 ∂(DGPS.FiniteN.imsEta N psi) :=
      integral_nonneg fun x => sq_nonneg _
    refine le_trans ?_ h
    have : min (min (n₁ / 2) (n₂ / 2)) c' ≤ c' := min_le_right _ _
    have hN2' : 0 ≤ N ^ 2 := sq_nonneg N
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hN2') hI

end DGPS.FiniteN.TiltedXY.Fin049

namespace DGPS.FiniteN

open DGPS.FiniteN.TiltedXY.Fin048 in
/-- **FIN049.** For the fixed tilted XY auxiliary law `η_N ∝ exp (-N ψ)` with
`ψ = tiltPsi 4 (1/2)`, the Poincare (spectral gap) inequality holds with a rate at least `c N`
for all sufficiently large `N`, on smooth compactly supported mean-zero test functions. -/
theorem tilted_auxiliary_rate_at_least_n :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        ∫ x, F x ∂(imsEta N (tiltPsi 4 (1 / 2))) = 0 →
        c * N * ∫ x, F x ^ 2 ∂(imsEta N (tiltPsi 4 (1 / 2))) ≤
          ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(imsEta N (tiltPsi 4 (1 / 2))) := by
  obtain ⟨c, hc, N₀, h⟩ := DGPS.FiniteN.TiltedXY.Fin049.assembly_FIN049
  refine ⟨c, hc, N₀, fun N hN F hF hFc hF0 => ?_⟩
  have := h N hN F hF hFc hF0
  rwa [Real.rpow_one] at this

end DGPS.FiniteN
