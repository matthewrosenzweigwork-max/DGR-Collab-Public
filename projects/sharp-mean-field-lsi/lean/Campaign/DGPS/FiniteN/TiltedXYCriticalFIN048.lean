import DGPS.FiniteN.CriticalXY
import DGPS.Circle.BesselConcavity
import DGPS.Examples.AttractiveXYTilt
import DGPS.Examples.AttractiveXYTiltRemoteEX025

/-!
# Tilted XY complete critical geometry (FIN048)

For the tilted attractive XY model `V = -h cos 2πx`, `W = κ (1 - cos 2π(x - y))` the auxiliary
potential on the plane `ℝ²` (after the affine change of variable `w = √κ z + h e₁`) is
`ψ(w) = ‖w - h e₁‖²/(2κ) - log I₀(‖w‖)` (`tiltPsi κ h`).  Its gradient is
`(w - h e₁)/κ - (g(‖w‖)/‖w‖) w` with `g = I₁/I₀`; a critical point is therefore aligned with the
field, `w = t e₁`, with `t` a nonzero root of `t = κ g(t) + h` (the EX023 scalar equation).  The
unique positive root is the nondegenerate global minimiser; a negative root `t = -s` satisfies
`κ g(s) - s = h`, and the transverse (`e₂`) Hessian eigenvalue is `1/κ - g(s)/s = -h/(κ s) < 0`,
so the remote critical point is not a local minimum.  The radial eigenvalue is `1/κ - g'(s)`
(which may vanish at a fold of the more general positive-field family).
-/

open scoped ContDiff RealInnerProductSpace
open MeasureTheory Filter Topology DGPS.Circle.BesselMoments DGPS.Circle.AngularNormalization

namespace DGPS.FiniteN.TiltedXY.Fin048

/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The field direction `e₁`. -/
noncomputable def e1 : Plane := EuclideanSpace.single 0 1

/-- The transverse direction `e₂`. -/
noncomputable def e2 : Plane := EuclideanSpace.single 1 1

/-- The tilted auxiliary potential `ψ(w) = ‖w - h e₁‖²/(2κ) - log I₀(‖w‖)`. -/
noncomputable def tiltPsi (κ h : ℝ) (w : Plane) : ℝ :=
  ‖w - h • e1‖ ^ 2 / (2 * κ) - Real.log (besselI 0 ‖w‖)

theorem e1_apply_zero : e1 0 = 1 := by simp [e1]
theorem e1_apply_one : e1 1 = 0 := by simp [e1]
theorem e2_apply_zero : e2 0 = 0 := by simp [e2]
theorem e2_apply_one : e2 1 = 1 := by simp [e2]

theorem norm_e1 : ‖e1‖ = 1 := by simp [e1]
theorem norm_e2 : ‖e2‖ = 1 := by simp [e2]

theorem norm_sq_plane (v : Plane) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [sq_abs]

theorem inner_plane (v w : Plane) : ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem plane_ext {v w : Plane} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  ext i; fin_cases i <;> simp [h0, h1]

theorem smul_e1_apply_zero (t : ℝ) : (t • e1) 0 = t := by simp [e1]
theorem smul_e1_apply_one (t : ℝ) : (t • e1) 1 = 0 := by simp [e1]

theorem tiltPsi_eq (κ h : ℝ) (w : Plane) :
    tiltPsi κ h w = ‖w - h • e1‖ ^ 2 / (2 * κ) - ‖w‖ ^ 2 / 4 + critPot w := by
  unfold tiltPsi critPot critH
  rw [besselI_zero_eq_critQ]
  ring

theorem contDiff_tiltPsi (κ h : ℝ) : ContDiff ℝ ∞ (tiltPsi κ h) := by
  have : tiltPsi κ h = fun w => ‖w - h • e1‖ ^ 2 / (2 * κ) - ‖w‖ ^ 2 / 4 + critPot w :=
    funext (tiltPsi_eq κ h)
  rw [this]
  have h1 : ContDiff ℝ ∞ (fun w : Plane => ‖w - h • e1‖ ^ 2 / (2 * κ)) :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _
  have h2 : ContDiff ℝ ∞ (fun w : Plane => ‖w‖ ^ 2 / 4) := (contDiff_norm_sq ℝ).div_const _
  exact (h1.sub h2).add critPot_contDiff

/-- The radial coefficient `1/κ - R(‖w‖²/4)/2` of the gradient (`R = A/Q`). -/
noncomputable def cfun (κ : ℝ) (w : Plane) : ℝ := 1 / κ - critR (‖w‖ ^ 2 / 4) / 2

theorem tiltPsi_hasFDerivAt (κ h : ℝ) (hκ : κ ≠ 0) (w : Plane) :
    HasFDerivAt (tiltPsi κ h)
      (cfun κ w • innerSL ℝ w - (h / κ) • innerSL ℝ e1) w := by
  have hfun : tiltPsi κ h = fun w => ‖w - h • e1‖ ^ 2 / (2 * κ) - ‖w‖ ^ 2 / 4 + critPot w :=
    funext (tiltPsi_eq κ h)
  rw [hfun]
  have h1 : HasFDerivAt (fun x : Plane => ‖x - h • e1‖ ^ 2 / (2 * κ))
      ((1 / κ) • innerSL ℝ (w - h • e1)) w := by
    have c := ((hasFDerivAt_id w).sub_const (h • e1)).norm_sq
    have e : (fun x : Plane => ‖x - h • e1‖ ^ 2 / (2 * κ)) =
        fun x : Plane => (1 / (2 * κ)) * ‖id x - h • e1‖ ^ 2 := by
      funext x; simp [div_eq_inv_mul]
    rw [e]
    refine (c.const_mul (1 / (2 * κ))).congr_fderiv ?_
    ext v
    simp
    field_simp
  have h2 : HasFDerivAt (fun x : Plane => ‖x‖ ^ 2 / 4) ((1 / 2 : ℝ) • innerSL ℝ w) w := by
    have := hasFDerivAt_comp_normSq (F := fun s : ℝ => s) (F' := 1) w (hasDerivAt_id _)
    simpa using this
  have h3 := critPot_hasFDerivAt w
  refine ((h1.sub h2).add h3).congr_fderiv ?_
  ext v
  simp [cfun, innerSL_apply_apply]
  ring

theorem fderiv_tiltPsi_apply (κ h : ℝ) (hκ : κ ≠ 0) (w v : Plane) :
    fderiv ℝ (tiltPsi κ h) w v = cfun κ w * ⟪w, v⟫ - (h / κ) * ⟪e1, v⟫ := by
  rw [(tiltPsi_hasFDerivAt κ h hκ w).fderiv]
  simp [innerSL_apply_apply]

theorem tiltPsi_hessian_apply (κ h : ℝ) (hκ : κ ≠ 0) (w v u : Plane) :
    fderiv ℝ (fderiv ℝ (tiltPsi κ h)) w v u =
      cfun κ w * ⟪v, u⟫ - (deriv critR (‖w‖ ^ 2 / 4) / 4) * (⟪w, v⟫ * ⟪w, u⟫) := by
  have hf : fderiv ℝ (tiltPsi κ h) =
      fun x => cfun κ x • innerSL ℝ x - (h / κ) • innerSL ℝ e1 :=
    funext fun x => (tiltPsi_hasFDerivAt κ h hκ x).fderiv
  rw [hf]
  have hd : HasDerivAt critR (deriv critR (‖w‖ ^ 2 / 4)) (‖w‖ ^ 2 / 4) :=
    (critR_differentiableAt _ (by positivity)).hasDerivAt
  have hc : HasFDerivAt (cfun κ)
      (((-(deriv critR (‖w‖ ^ 2 / 4)) / 2) / 2) • innerSL ℝ w) w := by
    refine hasFDerivAt_comp_normSq (F := fun s => 1 / κ - critR s / 2) w ?_
    exact ((hasDerivAt_const _ (1 / κ)).sub (hd.div_const 2)).congr_deriv (by ring)
  have hg := (innerSL ℝ (E := Plane)).hasFDerivAt (x := w)
  have h2 := (hc.smul hg).sub_const ((h / κ) • innerSL ℝ e1)
  have h3 : HasFDerivAt (fun x : Plane => cfun κ x • innerSL ℝ x - (h / κ) • innerSL ℝ e1) _ w :=
    h2
  rw [h3.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have e1' : (innerSL ℝ v) u = ⟪v, u⟫ := by simp
  have e2' : (innerSL ℝ w) v = ⟪w, v⟫ := by simp
  have e3' : (innerSL ℝ w) u = ⟪w, u⟫ := by simp
  rw [e1', e2', e3']
  ring

theorem tiltPsi_hessian (κ h : ℝ) (hκ : κ ≠ 0) (w v : Plane) :
    fderiv ℝ (fderiv ℝ (tiltPsi κ h)) w v v =
      cfun κ w * ‖v‖ ^ 2 - (deriv critR (‖w‖ ^ 2 / 4) / 4) * ⟪w, v⟫ ^ 2 := by
  rw [tiltPsi_hessian_apply κ h hκ, real_inner_self_eq_norm_sq]
  ring

/-! ### Axis values -/

theorem rho_eq_FIN048 {r : ℝ} (hr : 0 < r) : critR (r ^ 2 / 4) / 2 = besselRatio r / r := by
  have h := critR_ratio (r ^ 2 / 4) (by positivity)
  have e : 2 * Real.sqrt (r ^ 2 / 4) = r := by
    rw [show r ^ 2 / 4 = (r / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    ring
  rw [e] at h
  exact h.symm

theorem norm_smul_e1_sq (t : ℝ) : ‖t • e1‖ ^ 2 = t ^ 2 := by
  rw [norm_smul, norm_e1, mul_one, Real.norm_eq_abs, sq_abs]

theorem cfun_smul_e1 (κ t : ℝ) (ht : t ≠ 0) :
    cfun κ (t • e1) = 1 / κ - besselRatio t / t := by
  unfold cfun
  rw [norm_smul_e1_sq]
  rcases lt_or_gt_of_ne ht with h | h
  · have := rho_eq_FIN048 (neg_pos.2 h)
    rw [neg_sq] at this
    rw [this, besselRatio_neg, neg_div_neg_eq]
  · rw [rho_eq_FIN048 h]

theorem inner_smul_e1_e1 (t : ℝ) : ⟪t • e1, e1⟫ = t := by
  rw [inner_plane]; simp [e1_apply_zero, e1_apply_one]

theorem inner_smul_e1_e2 (t : ℝ) : ⟪t • e1, e2⟫ = 0 := by
  rw [inner_plane]; simp [e1_apply_one, e2_apply_zero, e2_apply_one]

theorem inner_e1_e1 : ⟪e1, e1⟫ = 1 := by
  rw [inner_plane]; simp [e1_apply_zero, e1_apply_one]

theorem inner_e1_e2 : ⟪e1, e2⟫ = 0 := by
  rw [inner_plane]; simp [e1_apply_zero, e1_apply_one, e2_apply_zero, e2_apply_one]

theorem inner_e2_e2 : ⟪e2, e2⟫ = 1 := by
  rw [inner_plane]; simp [e2_apply_zero, e2_apply_one]

/-! ### Critical points -/

theorem fderiv_tiltPsi_eq_zero_iff (κ h : ℝ) (hκ : κ ≠ 0) (hh : h ≠ 0) (w : Plane) :
    fderiv ℝ (tiltPsi κ h) w = 0 ↔ ∃ t : ℝ, t = κ * besselRatio t + h ∧ w = t • e1 := by
  constructor
  · intro h0
    have a := fderiv_tiltPsi_apply κ h hκ w e1
    have b := fderiv_tiltPsi_apply κ h hκ w e2
    rw [h0] at a b
    simp only [zero_apply] at a b
    rw [inner_plane, inner_plane] at a b
    simp only [e1_apply_zero, e1_apply_one, e2_apply_zero, e2_apply_one] at a b
    have a' : cfun κ w * w 0 = h / κ := by linarith
    have hc : cfun κ w ≠ 0 := by
      intro hc0
      rw [hc0] at a'
      have : h / κ = 0 := by linarith
      exact hh (by simpa [hκ] using this)
    have hw1 : w 1 = 0 := by
      have : cfun κ w * w 1 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hc
    have hw : w = w 0 • e1 :=
      plane_ext (by simp [e1_apply_zero]) (by simp [e1_apply_one, hw1])
    have ht0 : w 0 ≠ 0 := by
      intro h00
      rw [h00] at a'
      have : h / κ = 0 := by linarith
      exact hh (by simpa [hκ] using this)
    refine ⟨w 0, ?_, hw⟩
    have hcf := cfun_smul_e1 κ (w 0) ht0
    rw [← hw] at hcf
    rw [hcf] at a'
    field_simp at a'
    linarith
  · rintro ⟨t, ht, rfl⟩
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [DGPS.Circle.BesselConcavity.ratio_zero] at ht
      exact hh (by linarith)
    ext v
    rw [fderiv_tiltPsi_apply κ h hκ, cfun_smul_e1 κ t ht0, inner_plane, inner_plane]
    simp only [smul_e1_apply_zero, smul_e1_apply_one, e1_apply_zero, e1_apply_one,
      zero_apply]
    have hg : besselRatio t = (t - h) / κ := by field_simp; linarith
    rw [hg]
    field_simp
    ring

/-! ### Coercivity and global minimisers -/

theorem besselI_zero_le_FIN048 (t : ℝ) : besselI 0 t ≤ Real.exp |t| := by
  have h0 : besselI 0 t = ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar := by
    simp [besselI, angMode_zero]
  rw [h0]
  have hI := integrable_exp_mul t (fun _ => 1) continuous_const (fun _ => by simp)
  calc ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar ≤ ∫ _θ, Real.exp |t| ∂angHaar :=
        integral_mono hI (integrable_const _) fun θ => by
          rw [mul_one]; exact Real.exp_le_exp.2 (mul_angCos_le t θ)
    _ = Real.exp |t| := by simp

theorem log_besselI_zero_le_FIN048 (t : ℝ) : Real.log (besselI 0 t) ≤ |t| :=
  (Real.log_le_iff_le_exp (besselI_zero_pos t)).2 (besselI_zero_le_FIN048 t)

theorem tiltPsi_coercive (κ h : ℝ) (hκ : 0 < κ) (b : ℝ) :
    ∃ X : ℝ, ∀ w : Plane, X ≤ ‖w‖ → b ≤ tiltPsi κ h w := by
  refine ⟨|h| + 2 * κ + 1 + 2 * κ * (|h| + |b|), fun w hw => ?_⟩
  have h1 : ‖w‖ - |h| ≤ ‖w - h • e1‖ := by
    have := norm_sub_norm_le w (h • e1)
    rwa [norm_smul, norm_e1, mul_one, Real.norm_eq_abs] at this
  have h2 := log_besselI_zero_le_FIN048 ‖w‖
  rw [abs_of_nonneg (norm_nonneg w)] at h2
  have hx0 : 0 ≤ ‖w‖ - |h| := by
    have := abs_nonneg h; have := abs_nonneg b; have := mul_nonneg hκ.le (add_nonneg (abs_nonneg h) (abs_nonneg b))
    linarith
  have h3 : (‖w‖ - |h|) ^ 2 ≤ ‖w - h • e1‖ ^ 2 := pow_le_pow_left₀ hx0 h1 2
  have h4 : ‖w‖ + b ≤ (‖w‖ - |h|) ^ 2 / (2 * κ) := by
    rw [le_div_iff₀ (by positivity)]
    have := le_abs_self b
    have := abs_nonneg h
    have := abs_nonneg b
    nlinarith [mul_nonneg hκ.le (add_nonneg (abs_nonneg h) (abs_nonneg b))]
  have h5 : (‖w‖ - |h|) ^ 2 / (2 * κ) ≤ ‖w - h • e1‖ ^ 2 / (2 * κ) :=
    div_le_div_of_nonneg_right h3 (by positivity)
  unfold tiltPsi
  linarith

theorem exists_min_tiltPsi (κ h : ℝ) (hκ : 0 < κ) :
    ∃ w : Plane, ∀ u : Plane, tiltPsi κ h w ≤ tiltPsi κ h u := by
  refine (contDiff_tiltPsi κ h).continuous.exists_forall_le ?_
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨X, hX⟩ := tiltPsi_coercive κ h hκ b
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop X] with w hw using hX w hw

theorem tiltPsi_neg_axis (κ h s : ℝ) :
    tiltPsi κ h ((-s) • e1) = tiltPsi κ h (s • e1) + 2 * s * h / κ := by
  have e1' : (-s) • e1 - h • e1 = (-(s + h)) • e1 := by module
  have e2' : s • e1 - h • e1 = (s - h) • e1 := by module
  have n : ‖(-s) • e1‖ = ‖s • e1‖ := by simp [norm_smul, norm_e1]
  unfold tiltPsi
  rw [e1', e2', n, norm_smul_e1_sq, norm_smul_e1_sq]
  field_simp
  ring

theorem cfun_root (κ h t : ℝ) (hκ : κ ≠ 0) (ht : t ≠ 0) (hr : t = κ * besselRatio t + h) :
    cfun κ (t • e1) = h / (κ * t) := by
  rw [cfun_smul_e1 κ t ht]
  have hg : besselRatio t = (t - h) / κ := by field_simp; linarith
  rw [hg]
  field_simp
  ring

theorem root_ne_zero (κ h t : ℝ) (hh : h ≠ 0) (hr : t = κ * besselRatio t + h) : t ≠ 0 := by
  rintro rfl
  rw [DGPS.Circle.BesselConcavity.ratio_zero] at hr
  exact hh (by linarith)

theorem root_pos_of_isMin (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hr : t = κ * besselRatio t + h)
    (hm : ∀ u : Plane, tiltPsi κ h (t • e1) ≤ tiltPsi κ h u) : 0 < t := by
  have ht0 := root_ne_zero κ h t hh.ne' hr
  by_contra hneg
  have ht : t < 0 := lt_of_le_of_ne (not_lt.1 hneg) ht0
  obtain ⟨s, rfl⟩ : ∃ s, t = -s := ⟨-t, by ring⟩
  have h1 := hm (s • e1)
  rw [tiltPsi_neg_axis] at h1
  have : 0 < 2 * s * h / κ := by
    have : 0 < s := by linarith
    positivity
  linarith

theorem global_min_FIN048 (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    ∃ t : ℝ, 0 < t ∧ t = κ * besselRatio t + h ∧
      (∀ u : Plane, tiltPsi κ h (t • e1) ≤ tiltPsi κ h u) ∧
      (∀ w : Plane, (∀ u : Plane, tiltPsi κ h w ≤ tiltPsi κ h u) → w = t • e1) := by
  have key : ∀ w : Plane, (∀ u : Plane, tiltPsi κ h w ≤ tiltPsi κ h u) →
      ∃ t : ℝ, 0 < t ∧ t = κ * besselRatio t + h ∧ w = t • e1 := by
    intro w hw
    have hloc : IsLocalMin (tiltPsi κ h) w := Filter.Eventually.of_forall hw
    have hf := hloc.fderiv_eq_zero
    obtain ⟨t, hr, rfl⟩ := (fderiv_tiltPsi_eq_zero_iff κ h hκ.ne' hh.ne' w).1 hf
    exact ⟨t, root_pos_of_isMin κ h t hκ hh hr hw, hr, rfl⟩
  obtain ⟨w, hw⟩ := exists_min_tiltPsi κ h hκ
  obtain ⟨t, ht, hr, rfl⟩ := key w hw
  refine ⟨t, ht, hr, hw, fun w' hw' => ?_⟩
  obtain ⟨t', ht', hr', rfl⟩ := key w' hw'
  rw [DGPS.Examples.AttractiveXYTilt.positive_root_atMostOne_EX023 hκ.le hh ht' ht hr' hr]

/-! ### Hessian at axis critical points -/

theorem cfun_hasFDerivAt (κ : ℝ) (w : Plane) :
    HasFDerivAt (cfun κ) (((-(deriv critR (‖w‖ ^ 2 / 4)) / 2) / 2) • innerSL ℝ w) w := by
  have hd : HasDerivAt critR (deriv critR (‖w‖ ^ 2 / 4)) (‖w‖ ^ 2 / 4) :=
    (critR_differentiableAt _ (by positivity)).hasDerivAt
  refine hasFDerivAt_comp_normSq (F := fun s => 1 / κ - critR s / 2) w ?_
  exact ((hasDerivAt_const _ (1 / κ)).sub (hd.div_const 2)).congr_deriv (by ring)

theorem cfun_continuous (κ : ℝ) : Continuous (cfun κ) :=
  continuous_iff_continuousAt.2 fun w => (cfun_hasFDerivAt κ w).continuousAt

theorem hessian_pos_root (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) (ht : 0 < t)
    (hr : t = κ * besselRatio t + h) (v : Plane) (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (tiltPsi κ h)) (t • e1) v v := by
  rw [tiltPsi_hessian κ h hκ.ne', cfun_root κ h t hκ.ne' ht.ne' hr]
  have hd : deriv critR (‖t • e1‖ ^ 2 / 4) ≤ 0 := by
    apply critR_deriv_nonpos
    rw [norm_smul_e1_sq]; positivity
  have h1 : 0 < h / (κ * t) * ‖v‖ ^ 2 := by
    have : 0 < ‖v‖ := norm_pos_iff.2 hv
    positivity
  have h2 : 0 ≤ -(deriv critR (‖t • e1‖ ^ 2 / 4) / 4) * ⟪t • e1, v⟫ ^ 2 := by
    have : 0 ≤ -(deriv critR (‖t • e1‖ ^ 2 / 4) / 4) := by linarith
    positivity
  nlinarith

theorem hessian_e2_root (κ h t : ℝ) (hκ : κ ≠ 0) (ht : t ≠ 0)
    (hr : t = κ * besselRatio t + h) (u : Plane) :
    fderiv ℝ (fderiv ℝ (tiltPsi κ h)) (t • e1) e2 u = h / (κ * t) * ⟪e2, u⟫ := by
  rw [tiltPsi_hessian_apply κ h hκ, inner_smul_e1_e2, cfun_root κ h t hκ ht hr]
  ring

theorem hessian_e1_e2_axis (κ h t : ℝ) (hκ : κ ≠ 0) :
    fderiv ℝ (fderiv ℝ (tiltPsi κ h)) (t • e1) e1 e2 = 0 := by
  rw [tiltPsi_hessian_apply κ h hκ, inner_e1_e2, inner_smul_e1_e2]
  ring

theorem cfun_neg_axis_FIN048 (κ : ℝ) {s : ℝ} (hs : 0 < s) :
    cfun κ ((-s) • e1) = 1 / κ - besselRatio s / s := by
  rw [cfun_smul_e1 κ (-s) (neg_ne_zero.2 hs.ne'), besselRatio_neg, neg_div_neg_eq]

theorem critR_deriv_axis_FIN048 {r : ℝ} (hr : 0 < r) :
    deriv critR (r ^ 2 / 4) * r ^ 2 / 4 = deriv besselRatio r - besselRatio r / r := by
  have hc : HasDerivAt critR (deriv critR (r ^ 2 / 4)) (r ^ 2 / 4) :=
    (critR_differentiableAt _ (by positivity)).hasDerivAt
  have hq : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (r / 2) r := by
    have := ((hasDerivAt_id r).pow 2).div_const 4
    refine this.congr_deriv ?_
    simp; ring
  have hd1 : HasDerivAt (fun x : ℝ => critR (x ^ 2 / 4) / 2)
      (deriv critR (r ^ 2 / 4) * (r / 2) / 2) r := by
    have hcomp : HasDerivAt (fun x : ℝ => critR (x ^ 2 / 4))
        (deriv critR (r ^ 2 / 4) * (r / 2)) r := HasDerivAt.comp (h₂ := critR) r hc hq
    exact hcomp.div_const 2
  have hg : HasDerivAt besselRatio (deriv besselRatio r) r := by
    rw [DGPS.Circle.BesselConcavity.deriv_ratio]
    exact DGPS.Circle.BesselConcavity.hasDerivAt_ratio r
  have hd2 : HasDerivAt (fun x : ℝ => besselRatio x / x)
      ((deriv besselRatio r * r - besselRatio r * 1) / r ^ 2) r :=
    hg.div (hasDerivAt_id r) hr.ne'
  have heq : (fun x : ℝ => critR (x ^ 2 / 4) / 2) =ᶠ[𝓝 r] fun x => besselRatio x / x := by
    filter_upwards [Ioi_mem_nhds hr] with x hx using rho_eq_FIN048 hx
  have E := hd1.unique (hd2.congr_of_eventuallyEq heq)
  have : deriv critR (r ^ 2 / 4) * r ^ 2 / 4 = r * (deriv critR (r ^ 2 / 4) * (r / 2) / 2) := by
    ring
  rw [this, E]
  field_simp

theorem hessian_radial_neg_FIN048 (κ h s : ℝ) (hκ : κ ≠ 0) (hs : 0 < s) :
    fderiv ℝ (fderiv ℝ (tiltPsi κ h)) ((-s) • e1) e1 e1 = 1 / κ - deriv besselRatio s := by
  rw [tiltPsi_hessian_apply κ h hκ, cfun_neg_axis_FIN048 κ hs, inner_smul_e1_e1, norm_smul_e1_sq,
    neg_sq]
  have := critR_deriv_axis_FIN048 hs
  have e : deriv critR (s ^ 2 / 4) / 4 * (-s * -s) = deriv critR (s ^ 2 / 4) * s ^ 2 / 4 := by
    ring
  rw [inner_e1_e1, e, this]
  ring

/-! ### Remote critical points are not local minima -/

theorem not_isLocalMin_neg_root (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) (ht : t < 0)
    (hr : t = κ * besselRatio t + h) : ¬ IsLocalMin (tiltPsi κ h) (t • e1) := by
  intro hmin
  set L : ℝ → Plane := fun τ => t • e1 + τ • e2 with hL
  have hLc : Continuous L := by fun_prop
  have hL0 : L 0 = t • e1 := by simp [hL]
  have hneg : cfun κ (L 0) < 0 := by
    rw [hL0, cfun_root κ h t hκ.ne' ht.ne hr]
    exact div_neg_of_pos_of_neg hh (mul_neg_of_pos_of_neg hκ ht)
  have ev1 : ∀ᶠ τ in 𝓝 (0 : ℝ), cfun κ (L τ) < 0 :=
    ((cfun_continuous κ).comp hLc).continuousAt.eventually_mem (isOpen_Iio.mem_nhds hneg)
  have ev2 : ∀ᶠ τ in 𝓝 (0 : ℝ), tiltPsi κ h (t • e1) ≤ tiltPsi κ h (L τ) := by
    have := hLc.tendsto 0
    rw [hL0] at this
    exact this.eventually hmin
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (ev1.and ev2)
  have hb : 0 < ε / 2 := by positivity
  have hLd : ∀ x, HasDerivAt L e2 x := fun x => by
    have := ((hasDerivAt_id x).smul_const e2).const_add (t • e1)
    simpa [hL] using this
  have hφ : ∀ x, HasDerivAt (fun τ => tiltPsi κ h (L τ)) (cfun κ (L x) * x) x := fun x => by
    have := (tiltPsi_hasFDerivAt κ h hκ.ne' (L x)).comp_hasDerivAt x (hLd x)
    refine this.congr_deriv ?_
    simp only [sub_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [inner_plane, inner_plane]
    simp [hL, e1_apply_zero, e1_apply_one, e2_apply_zero, e2_apply_one]
  have hanti : StrictAntiOn (fun τ => tiltPsi κ h (L τ)) (Set.Icc 0 (ε / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 (ε / 2))
      ((contDiff_tiltPsi κ h).continuous.comp hLc).continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hφ x).deriv]
    have hx' := hball (y := x) (by rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2])
    exact mul_neg_of_neg_of_pos hx'.1 hx.1
  have hlt := hanti (Set.left_mem_Icc.2 hb.le) (Set.right_mem_Icc.2 hb.le) hb
  have hb' := (hball (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos hb]; linarith)).2
  have : L 0 = t • e1 := hL0
  simp only [hL] at hb' hlt
  simp only [zero_smul, add_zero] at hlt
  linarith

/-! ### At most two remote roots -/

theorem no_three_roots_FIN048 (κ h : ℝ) (hκ : 0 < κ) {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hbc : b < c) (ra : κ * besselRatio a - a = h) (rb : κ * besselRatio b - b = h)
    (rc : κ * besselRatio c - c = h) : False := by
  have hF : ∀ x, HasDerivAt (fun s => κ * besselRatio s - s)
      (κ * DGPS.Circle.BesselConcavity.ratioDeriv x - 1) x := fun x =>
    ((DGPS.Circle.BesselConcavity.hasDerivAt_ratio x).const_mul κ).sub (hasDerivAt_id x)
      |>.congr_deriv (by simp)
  have hcont : Continuous (fun s => κ * besselRatio s - s) :=
    (DGPS.Circle.BesselConcavity.continuous_besselRatio.const_mul κ).sub continuous_id
  obtain ⟨ξ₁, hξ₁, d₁⟩ := exists_deriv_eq_zero hab hcont.continuousOn (by simp only [ra, rb])
  obtain ⟨ξ₂, hξ₂, d₂⟩ := exists_deriv_eq_zero hbc hcont.continuousOn (by simp only [rb, rc])
  rw [(hF ξ₁).deriv] at d₁
  rw [(hF ξ₂).deriv] at d₂
  have hlt := DGPS.Circle.BesselConcavity.strictAntiOn_ratioDeriv
    (Set.mem_Ici.2 (by linarith [hξ₁.1] : (0 : ℝ) ≤ ξ₁))
    (Set.mem_Ici.2 (by linarith [hξ₂.1, hab, hbc] : (0 : ℝ) ≤ ξ₂))
    (by linarith [hξ₁.2, hξ₂.1] : ξ₁ < ξ₂)
  nlinarith

theorem root_dichotomy_FIN048 (κ h : ℝ) (hκ : 0 < κ) {p q s : ℝ} (hp : 0 ≤ p) (hpq : p < q)
    (hs : 0 ≤ s) (rp : κ * besselRatio p - p = h) (rq : κ * besselRatio q - q = h)
    (rs : κ * besselRatio s - s = h) : s = p ∨ s = q := by
  by_contra hne0
  have hne := not_or.1 hne0
  rcases lt_trichotomy s p with h1 | h1 | h1
  · exact no_three_roots_FIN048 κ h hκ hs h1 hpq rs rp rq
  · exact hne.1 h1
  · rcases lt_trichotomy s q with h2 | h2 | h2
    · exact no_three_roots_FIN048 κ h hκ hp h1 h2 rp rs rq
    · exact hne.2 h2
    · exact no_three_roots_FIN048 κ h hκ hp hpq h2 rp rq rs

end DGPS.FiniteN.TiltedXY.Fin048

namespace DGPS.FiniteN

open DGPS.FiniteN.TiltedXY.Fin048

/-- **FIN048: complete critical geometry of the tilted attractive XY auxiliary potential.**
For `κ = 4`, `h = 1/2`, `ψ(w) = ‖w - h e₁‖²/(2κ) - log I₀(‖w‖)` has exactly three critical points,
all on the field axis `ℝ e₁`:
* `t₀ e₁` with `t₀ > 0` the unique positive root of `t = 4 g(t) + 1/2` (`g = I₁/I₀`); it is the
  unique global minimiser and its Hessian is positive definite (nondegenerate);
* two remote points `-s₁ e₁`, `-s₂ e₁` with `0 < s₁ < 1 < s₂ < 4` and `4 g(s) - s = 1/2`; at each
  of them `e₂` is a Hessian eigenvector with the strictly negative eigenvalue
  `1/κ - g(s)/s = -h/(κ s) = -(1/2)/(4 s)`, the radial entry is `1/κ - g'(s)`, the mixed entry
  vanishes, and the point is not a local minimum. -/
theorem tilted_xy_complete_critical_geometry :
    ∃ t₀ s₁ s₂ : ℝ, 0 < t₀ ∧ 0 < s₁ ∧ s₁ < 1 ∧ 1 < s₂ ∧ s₂ < 4 ∧
      t₀ = 4 * DGPS.Circle.BesselMoments.besselRatio t₀ + 1 / 2 ∧
      4 * DGPS.Circle.BesselMoments.besselRatio s₁ - s₁ = 1 / 2 ∧
      4 * DGPS.Circle.BesselMoments.besselRatio s₂ - s₂ = 1 / 2 ∧
      {w : Plane | fderiv ℝ (tiltPsi 4 (1 / 2)) w = 0} =
        {t₀ • e1, (-s₁) • e1, (-s₂) • e1} ∧
      (∀ u : Plane, tiltPsi 4 (1 / 2) (t₀ • e1) ≤ tiltPsi 4 (1 / 2) u) ∧
      (∀ w : Plane, (∀ u : Plane, tiltPsi 4 (1 / 2) w ≤ tiltPsi 4 (1 / 2) u) → w = t₀ • e1) ∧
      (∀ v : Plane, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) (t₀ • e1) v v) ∧
      (∀ s : ℝ, (s = s₁ ∨ s = s₂) →
        ¬ IsLocalMin (tiltPsi 4 (1 / 2)) ((-s) • e1) ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e2 e2 =
          1 / 4 - DGPS.Circle.BesselMoments.besselRatio s / s ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e2 e2 = -(1 / 2) / (4 * s) ∧
        -(1 / 2) / (4 * s) < 0 ∧
        (∀ u : Plane, fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e2 u =
          -(1 / 2) / (4 * s) * ⟪e2, u⟫) ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e1 e2 = 0 ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e1 e1 =
          1 / 4 - deriv DGPS.Circle.BesselMoments.besselRatio s) := by
  obtain ⟨t₀, ht₀, hr₀, hmin, huniq⟩ :=
    global_min_FIN048 4 (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨s₁, s₂, h0, h1, h2, h3, r1, r2⟩ :=
    DGPS.Examples.AttractiveXYTiltRemoteEX025.remote_roots_exist_EX025
  have hrem : ∀ {s : ℝ}, 4 * DGPS.Circle.BesselMoments.besselRatio s - s = 1 / 2 →
      -s = 4 * DGPS.Circle.BesselMoments.besselRatio (-s) + 1 / 2 := fun {s} h =>
    DGPS.Examples.AttractiveXYTiltRemoteEX025.remote_root_iff_EX025.2 h
  refine ⟨t₀, s₁, s₂, ht₀, h0, h1, h2, h3, hr₀, r1, r2, ?_, hmin, huniq,
    fun v hv => hessian_pos_root 4 (1 / 2) t₀ (by norm_num) (by norm_num) ht₀ hr₀ v hv, ?_⟩
  · ext w
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hw
      obtain ⟨t, ht, rfl⟩ :=
        (fderiv_tiltPsi_eq_zero_iff 4 (1 / 2) (by norm_num) (by norm_num) w).1 hw
      have ht0 := root_ne_zero 4 (1 / 2) t (by norm_num) ht
      rcases lt_or_gt_of_ne ht0 with hlt | hgt
      · obtain ⟨s, rfl⟩ : ∃ s, t = -s := ⟨-t, by ring⟩
        have hs : 0 < s := by linarith
        have hrs : 4 * DGPS.Circle.BesselMoments.besselRatio s - s = 1 / 2 :=
          DGPS.Examples.AttractiveXYTiltRemoteEX025.remote_root_iff_EX025.1 ht
        rcases root_dichotomy_FIN048 4 (1 / 2) (by norm_num) h0.le (by linarith) hs.le r1 r2 hrs
          with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · left
        rw [DGPS.Examples.AttractiveXYTilt.positive_root_atMostOne_EX023 (by norm_num : (0:ℝ) ≤ 4)
          (by norm_num : (0:ℝ) < 1 / 2) hgt ht₀ ht hr₀]
    · rintro (rfl | rfl | rfl)
      · exact (fderiv_tiltPsi_eq_zero_iff 4 (1 / 2) (by norm_num) (by norm_num) _).2
          ⟨_, hr₀, rfl⟩
      · exact (fderiv_tiltPsi_eq_zero_iff 4 (1 / 2) (by norm_num) (by norm_num) _).2
          ⟨_, hrem r1, rfl⟩
      · exact (fderiv_tiltPsi_eq_zero_iff 4 (1 / 2) (by norm_num) (by norm_num) _).2
          ⟨_, hrem r2, rfl⟩
  · have key : ∀ s : ℝ, 0 < s → 4 * DGPS.Circle.BesselMoments.besselRatio s - s = 1 / 2 →
        (¬ IsLocalMin (tiltPsi 4 (1 / 2)) ((-s) • e1) ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e2 e2 =
          1 / 4 - DGPS.Circle.BesselMoments.besselRatio s / s ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e2 e2 = -(1 / 2) / (4 * s) ∧
        -(1 / 2) / (4 * s) < 0 ∧
        (∀ u : Plane, fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e2 u =
          -(1 / 2) / (4 * s) * ⟪e2, u⟫) ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e1 e2 = 0 ∧
        fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e1 e1 =
          1 / 4 - deriv DGPS.Circle.BesselMoments.besselRatio s) := by
      intro s hs hrs
      have hr := hrem hrs
      have hg : DGPS.Circle.BesselMoments.besselRatio s = (s + 1 / 2) / 4 := by linarith
      have hval : (1 / 2 : ℝ) / (4 * -s) = -(1 / 2) / (4 * s) := by
        field_simp
      have heig : ∀ u : Plane,
          fderiv ℝ (fderiv ℝ (tiltPsi 4 (1 / 2))) ((-s) • e1) e2 u =
            -(1 / 2) / (4 * s) * ⟪e2, u⟫ := by
        intro u
        rw [hessian_e2_root 4 (1 / 2) (-s) (by norm_num) (neg_ne_zero.2 hs.ne') hr u, hval]
      have h22 := heig e2
      rw [inner_e2_e2, mul_one] at h22
      refine ⟨not_isLocalMin_neg_root 4 (1 / 2) (-s) (by norm_num) (by norm_num)
        (neg_neg_of_pos hs) hr, ?_, h22, ?_, heig, ?_,
        hessian_radial_neg_FIN048 4 (1 / 2) s (by norm_num) hs⟩
      · rw [h22, hg]
        field_simp
        ring
      · have : 0 < (1 / 2 : ℝ) / (4 * s) := by positivity
        rw [neg_div]
        linarith
      · exact hessian_e1_e2_axis 4 (1 / 2) (-s) (by norm_num)
    rintro s (rfl | rfl)
    · exact key _ h0 r1
    · exact key _ (by linarith) r2

end DGPS.FiniteN
