import DGPS.FiniteN.ScalarFoldFIN059
import DGPS.FiniteN.TiltedXYRateFIN049

/-!
# FIN060 (part A): one-dimensional geometry of the fold auxiliary potential

Real-line estimates for `ψ = scalarPsi κ h_c`: bounded second derivative, linear growth of the
gradient, quadratic growth of `ψ`, and the gradient gap away from the two stationary points.
-/

open MeasureTheory Set Metric
open scoped ContDiff

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity
  DGPS.Circle.BesselMonotonicity DGPS.FiniteN.ScalarFoldFIN056 DGPS.Circle.AngularNormalization

theorem abs_ratio_lt_one_FIN060 (t : ℝ) : |besselRatio t| < 1 := by
  rw [abs_lt]
  refine ⟨?_, besselRatio_lt_one t⟩
  have := besselRatio_lt_one (-t)
  rw [besselRatio_neg] at this
  linarith

theorem ratioDeriv_mem_FIN060 (t : ℝ) : 0 ≤ ratioDeriv t ∧ ratioDeriv t ≤ 1 / 2 := by
  rcases lt_trichotomy t 0 with h | h | h
  · have h' : 0 < -t := by linarith
    rw [← ratioDeriv_neg_FIN056 t]
    exact ⟨(ratioDeriv_pos _ h').le, (ratioDeriv_lt_half _ h').le⟩
  · subst h; rw [ratioDeriv_zero]; norm_num
  · exact ⟨(ratioDeriv_pos _ h).le, (ratioDeriv_lt_half _ h).le⟩

theorem abs_psiSecond_le_FIN060 {κ : ℝ} (hκ : 2 < κ) (t : ℝ) : |1 / κ - ratioDeriv t| ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := ratioDeriv_mem_FIN060 t
  have hk : 1 / κ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hκ.le
  have hk0 : 0 < 1 / κ := by positivity
  rw [abs_le]; constructor <;> linarith

theorem lower_gradient_FIN060 {κ : ℝ} (hκ : 0 < κ) (h t : ℝ) :
    |t| / κ - |h| / κ - 1 ≤ |psiDerivFIN056 κ h t| := by
  unfold psiDerivFIN056
  have h1 : |(t - h) / κ| ≥ |t| / κ - |h| / κ := by
    rw [abs_div, abs_of_pos hκ, ← sub_div]
    exact div_le_div_of_nonneg_right (by have := abs_sub_abs_le_abs_sub t h; linarith) hκ.le
  have h2 := abs_ratio_lt_one_FIN060 t
  have h3 : |(t - h) / κ| - |besselRatio t| ≤ |(t - h) / κ - besselRatio t| := abs_sub_abs_le_abs_sub _ _
  linarith

theorem far_gradient_scalar_FIN060 {κ : ℝ} (hκ : 0 < κ) (h t : ℝ) (ht : 2 * |h| + 2 * κ ≤ |t|) :
    |t| / (2 * κ) ≤ |psiDerivFIN056 κ h t| := by
  have := lower_gradient_FIN060 hκ h t
  have e : |t| / κ - |h| / κ - 1 - |t| / (2 * κ) = (|t| - 2 * |h| - 2 * κ) / (2 * κ) := by
    field_simp; ring
  have : 0 ≤ (|t| - 2 * |h| - 2 * κ) / (2 * κ) := div_nonneg (by linarith) (by positivity)
  linarith

theorem besselI_zero_le_FIN060 (t : ℝ) : besselI 0 t ≤ Real.exp |t| := by
  unfold besselI
  calc ∫ θ, Real.exp (t * angCos θ) * angMode 0 θ ∂angHaar ≤ ∫ _θ, Real.exp |t| ∂angHaar := by
        refine integral_mono (integrable_exp_mul t (angMode 0) (continuous_angMode 0)
          (abs_angMode_le 0)) (integrable_const _) fun θ => ?_
        rw [angMode_zero]
        simp only [mul_one]
        exact Real.exp_le_exp.2 (mul_angCos_le t θ)
    _ = Real.exp |t| := by simp

theorem log_besselI_zero_le_FIN060 (t : ℝ) : Real.log (besselI 0 t) ≤ |t| := by
  rw [Real.log_le_iff_le_exp (besselI_zero_pos t)]
  exact besselI_zero_le_FIN060 t

theorem scalarPsi_growth_FIN060 {κ : ℝ} (hκ : 0 < κ) (h t0 : ℝ) :
    ∃ b > 0, ∃ C : ℝ, ∀ t, b * (t - t0) ^ 2 - C ≤ scalarPsi κ h t - scalarPsi κ h t0 := by
  refine ⟨1 / (8 * κ), by positivity, (t0 - h) ^ 2 / (2 * κ) + 2 * κ + |t0| + scalarPsi κ h t0 + 0, fun t => ?_⟩
  have h1 := log_besselI_zero_le_FIN060 t
  have h2 : scalarPsi κ h t ≥ (t - h) ^ 2 / (2 * κ) - |t| := by
    unfold scalarPsi; linarith
  have h3 : (t - h) ^ 2 ≥ (t - t0) ^ 2 / 2 - (t0 - h) ^ 2 := by
    nlinarith [sq_nonneg (t - t0 + 2 * (t0 - h))]
  have h4 : |t| ≤ |t - t0| + |t0| := by
    have := abs_add_le (t - t0) t0
    simpa using this
  have h5 : |t - t0| ≤ (t - t0) ^ 2 / (8 * κ) + 2 * κ := by
    have : (|t - t0| - 4 * κ) ^ 2 ≥ 0 := sq_nonneg _
    have e : (t - t0) ^ 2 = |t - t0| ^ 2 := (sq_abs _).symm
    rw [e]
    have : |t - t0| ^ 2 / (8 * κ) + 2 * κ - |t - t0| = (|t - t0| - 4 * κ) ^ 2 / (8 * κ) := by
      field_simp; ring
    have h6 : 0 ≤ (|t - t0| - 4 * κ) ^ 2 / (8 * κ) := by positivity
    linarith
  have h7 : (t - h) ^ 2 / (2 * κ) ≥ (t - t0) ^ 2 / (4 * κ) - (t0 - h) ^ 2 / (2 * κ) := by
    have : (t - h) ^ 2 / (2 * κ) ≥ ((t - t0) ^ 2 / 2 - (t0 - h) ^ 2) / (2 * κ) :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have e : ((t - t0) ^ 2 / 2 - (t0 - h) ^ 2) / (2 * κ) =
        (t - t0) ^ 2 / (4 * κ) - (t0 - h) ^ 2 / (2 * κ) := by field_simp; ring
    linarith
  have e2 : (t - t0) ^ 2 / (4 * κ) - (t - t0) ^ 2 / (8 * κ) = 1 / (8 * κ) * (t - t0) ^ 2 := by
    field_simp; ring
  linarith

/-! ### The one-dimensional Euclidean space -/

/-- The line `ℝ^1` as a Euclidean space. -/
abbrev E1 : Type := EuclideanSpace ℝ (Fin 1)

/-- The coordinate functional on `E1`. -/
noncomputable def prFIN060 : E1 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 1)

theorem prFIN060_apply (x : E1) : prFIN060 x = x 0 := rfl

theorem norm_E1_FIN060 (x : E1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

theorem dist_E1_FIN060 (x y : E1) : dist x y = |x 0 - y 0| := by
  rw [dist_eq_norm, norm_E1_FIN060]; rfl

theorem norm_smul_pr_FIN060 (a : ℝ) : ‖a • prFIN060‖ = |a| := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a) fun v => ?_
    have hv : |v 0| ≤ ‖v‖ := (norm_E1_FIN060 v).ge
    have h2 : ‖(a • prFIN060) v‖ = |a| * |v 0| := by
      rw [smul_apply, prFIN060_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
    rw [h2]
    exact mul_le_mul_of_nonneg_left hv (abs_nonneg a)
  · have h := (a • prFIN060).le_opNorm (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    have h3 : ‖(a • prFIN060) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))‖ = |a| := by
      rw [smul_apply, prFIN060_apply, smul_eq_mul, Real.norm_eq_abs, PiLp.single_apply]
      simp
    rw [h3, PiLp.norm_single, norm_one, mul_one] at h
    exact h

/-- A function of one real variable viewed on `E1`. -/
noncomputable def psiE (g : ℝ → ℝ) : E1 → ℝ := fun x => g (x 0)

theorem hasFDerivAt_psiE {g : ℝ → ℝ} (hg : Differentiable ℝ g) (x : E1) :
    HasFDerivAt (psiE g) (deriv g (x 0) • prFIN060) x := by
  have h1 : HasFDerivAt (prFIN060 : E1 → ℝ) prFIN060 x := prFIN060.hasFDerivAt
  exact (hg.differentiableAt.hasDerivAt.comp_hasFDerivAt x h1 : _)

theorem fderiv_psiE {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    fderiv ℝ (psiE g) = fun x => deriv g (x 0) • prFIN060 :=
  funext fun x => (hasFDerivAt_psiE hg x).fderiv

theorem norm_fderiv_psiE {g : ℝ → ℝ} (hg : Differentiable ℝ g) (x : E1) :
    ‖fderiv ℝ (psiE g) x‖ = |deriv g (x 0)| := by
  rw [fderiv_psiE hg, norm_smul_pr_FIN060]

theorem contDiff_psiE {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (psiE g) :=
  hg.comp prFIN060.contDiff

theorem fderiv_fderiv_psiE {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (x v w : E1) :
    fderiv ℝ (fderiv ℝ (psiE g)) x v w = deriv (deriv g) (x 0) * v 0 * w 0 := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
  have hg2 : Differentiable ℝ (deriv g) :=
    (contDiff_infty_iff_deriv.1 hg).2.differentiable (by simp)
  have h1 : HasFDerivAt (fun y : E1 => deriv g (y 0))
      (deriv (deriv g) (x 0) • prFIN060) x :=
    hg2.differentiableAt.hasDerivAt.comp_hasFDerivAt x prFIN060.hasFDerivAt
  have h2 := h1.smul_const prFIN060
  rw [fderiv_psiE hg1, h2.fderiv]
  simp [prFIN060_apply, mul_assoc]

theorem norm_fderiv_fderiv_psiE_le {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {M : ℝ}
    (hM : ∀ t, |deriv (deriv g) t| ≤ M) (x : E1) :
    ‖fderiv ℝ (fderiv ℝ (psiE g)) x‖ ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [fderiv_fderiv_psiE hg, Real.norm_eq_abs, abs_mul, abs_mul]
  have hv : |v 0| ≤ ‖v‖ := (norm_E1_FIN060 v).ge
  have hw : |w 0| ≤ ‖w‖ := (norm_E1_FIN060 w).ge
  have := hM (x 0)
  calc |deriv (deriv g) (x 0)| * |v 0| * |w 0| ≤ M * ‖v‖ * ‖w‖ := by gcongr
    _ = _ := by ring

end DGPS.FiniteN.ScalarFoldFIN060
