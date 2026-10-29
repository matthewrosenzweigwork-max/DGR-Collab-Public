import DGPS.Examples.AttractiveXYCollapse
import DGPS.Structural.PositivityFromResidual
import DGPS.Structural.SmallRateCircle
/-!
# EX027: all-species fold lower bound

For the attractive XY model on the circle (`κ = 4`, `h = h_c + ε`, `0 < ε ≤ 1`) this file proves:
the explicit free-energy function `Ψ_h(z) = 2|z|² - log I_0(|h e₁ + 4 z|)` has gradient `4 R_h`
and Hessian of operator norm at most `20`; for every finite positive-weight species family the gap
satisfies `G = E + Ψ_h(z) - Ψ_h(z_*)` with `E = ∑ θ_s H(ρ_s | p_{h,z})`; the dissipation satisfies
`E ≤ exp(2 M0) D / (2 a0)`, the residual satisfies `|R_h(z)|² ≤ 2 E`; and the multi-species rate
satisfies `r_ms ≥ a0 exp(-2 M0) ε² / (1 + 20 C_R²)` (`DGPS.Examples.all_species_fold_lower_bound`).
-/

open MeasureTheory
open DGPS DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical
open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity DGPS.Circle.BesselConcavity
open DGPS.Examples.AttractiveXYTilt DGPS.Examples.AttractiveXYCollapseEX026
open DGPS.Models
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DGPS.Examples.AttractiveXYFoldEX027

/-- The vector `(cos 2πx, sin 2πx)`. -/
noncomputable def phi_EX027 : Fin 2 → Torus 1 → ℝ :=
  ![fun x => (xyMode x).re, fun x => (xyMode x).im]

theorem continuous_phi_EX027 (i : Fin 2) : Continuous (phi_EX027 i) := by
  fin_cases i
  · exact Complex.continuous_re.comp continuous_xyMode
  · exact Complex.continuous_im.comp continuous_xyMode

theorem abs_phi_le_EX027 (i : Fin 2) (x : Torus 1) : |phi_EX027 i x| ≤ 1 := by
  fin_cases i
  · exact abs_xyMode_re_le x
  · exact abs_xyMode_im_le x

theorem phi_sq_EX027 (x : Torus 1) : phi_EX027 0 x ^ 2 + phi_EX027 1 x ^ 2 = 1 := by
  have h := xyMode_norm x
  have h2 := Complex.sq_norm (xyMode x)
  rw [h, Complex.normSq_apply] at h2
  simp only [phi_EX027, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

/-- `∑ i, w i φ_i(x)`. -/
noncomputable def lin_EX027 (w : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) : ℝ :=
  ∑ i, w i * phi_EX027 i x

/-- The parametric integral `J_g(w) = ∫ g e^{⟨w, φ⟩} dm`. -/
noncomputable def J_EX027 (g : Torus 1 → ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∫ x, g x * Real.exp (lin_EX027 w x) ∂haar 1

theorem abs_lin_le_EX027 (w : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    |lin_EX027 w x| ≤ 2 * ‖w‖ := by
  unfold lin_EX027
  rw [Fin.sum_univ_two]
  have h0 := PiLp.norm_apply_le w 0
  have h1 := PiLp.norm_apply_le w 1
  have a0 := abs_phi_le_EX027 0 x
  have a1 := abs_phi_le_EX027 1 x
  rw [Real.norm_eq_abs] at h0 h1
  calc |w 0 * phi_EX027 0 x + w 1 * phi_EX027 1 x|
      ≤ |w 0 * phi_EX027 0 x| + |w 1 * phi_EX027 1 x| := abs_add_le _ _
    _ ≤ ‖w‖ + ‖w‖ := by
        rw [abs_mul, abs_mul]
        gcongr
        · calc |w 0| * |phi_EX027 0 x| ≤ |w 0| * 1 := by gcongr
            _ ≤ _ := by linarith
        · calc |w 1| * |phi_EX027 1 x| ≤ |w 1| * 1 := by gcongr
            _ ≤ _ := by linarith
    _ = 2 * ‖w‖ := by ring


theorem continuous_lin_x_EX027 (w : EuclideanSpace ℝ (Fin 2)) : Continuous (lin_EX027 w) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_phi_EX027 i)

/-- The linear form `w ↦ ∑ φ_i(x) w_i` as a continuous linear map. -/
noncomputable def linCLM_EX027 (x : Torus 1) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ∑ i, phi_EX027 i x • EuclideanSpace.proj i

theorem linCLM_apply_EX027 (x : Torus 1) (w : EuclideanSpace ℝ (Fin 2)) :
    linCLM_EX027 x w = lin_EX027 w x := by
  simp [linCLM_EX027, lin_EX027, mul_comm]

theorem norm_linCLM_le_EX027 (x : Torus 1) : ‖linCLM_EX027 x‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
  rw [linCLM_apply_EX027, Real.norm_eq_abs]
  exact abs_lin_le_EX027 w x

theorem continuous_linCLM_EX027 : Continuous linCLM_EX027 :=
  continuous_finsetSum _ fun i _ => (continuous_phi_EX027 i).smul continuous_const

theorem continuous_lin_EX027 : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × Torus 1 =>
    lin_EX027 p.1 p.2) :=
  continuous_finsetSum _ fun i _ =>
    ((EuclideanSpace.proj i).continuous.comp continuous_fst).mul
      ((continuous_phi_EX027 i).comp continuous_snd)

/-- The derivative of `J_g`. -/
noncomputable def dJ_EX027 (g : Torus 1 → ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ∑ i, J_EX027 (fun x => g x * phi_EX027 i x) w • EuclideanSpace.proj i

theorem hasFDerivAt_J_EX027 {g : Torus 1 → ℝ} (hg : Continuous g) (w : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (J_EX027 g) (dJ_EX027 g w) w := by
  obtain ⟨Gb, hGb⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hcont : ∀ (w' : EuclideanSpace ℝ (Fin 2)), Continuous fun x => g x * Real.exp (lin_EX027 w' x) :=
    fun w' => hg.mul (Real.continuous_exp.comp (continuous_lin_x_EX027 w'))
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := haar 1) (s := Metric.ball w 1)
    (F := fun w' x => g x * Real.exp (lin_EX027 w' x))
    (F' := fun w' x => (g x * Real.exp (lin_EX027 w' x)) • linCLM_EX027 x)
    (bound := fun _ => Gb * Real.exp (2 * (‖w‖ + 1)) * 2)
    (Metric.ball_mem_nhds w one_pos)
    (Filter.Eventually.of_forall fun w' => (hcont w').aestronglyMeasurable)
    ((hcont w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((hcont w).smul continuous_linCLM_EX027).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x w' hw' => by
      have hn : ‖w'‖ ≤ ‖w‖ + 1 := by
        have := norm_sub_norm_le w' w
        have h2 : ‖w' - w‖ < 1 := by simpa [dist_eq_norm] using hw'
        linarith
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : |g x| ≤ Gb := by simpa using hGb x (Set.mem_univ x)
      have h2 : Real.exp (lin_EX027 w' x) ≤ Real.exp (2 * (‖w‖ + 1)) :=
        Real.exp_le_exp.2 (le_trans (le_abs_self _) (by linarith [abs_lin_le_EX027 w' x]))
      have h3 := norm_linCLM_le_EX027 x
      have h4 : 0 ≤ Gb := le_trans (abs_nonneg _) h1
      calc |g x| * Real.exp (lin_EX027 w' x) * ‖linCLM_EX027 x‖
          ≤ Gb * Real.exp (2 * (‖w‖ + 1)) * 2 := by gcongr)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x w' _ => by
      have hL := (linCLM_EX027 x).hasFDerivAt (x := w')
      have h1 := ((Real.hasDerivAt_exp (linCLM_EX027 x w')).comp_hasFDerivAt w' hL).const_mul (g x)
      have e : (fun y => g x * Real.exp (lin_EX027 y x)) =
          fun y => g x * (Real.exp ∘ (linCLM_EX027 x)) y := by
        funext y; simp [linCLM_apply_EX027]
      rw [e]
      convert h1 using 1
      rw [smul_smul, linCLM_apply_EX027])
  refine (show HasFDerivAt (J_EX027 g) _ w from key).congr_fderiv ?_
  unfold dJ_EX027
  have e : ∀ x, (g x * Real.exp (lin_EX027 w x)) • linCLM_EX027 x =
      ∑ i, (g x * phi_EX027 i x * Real.exp (lin_EX027 w x)) • EuclideanSpace.proj i := by
    intro x
    unfold linCLM_EX027
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]; congr 1; ring
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const]
    rfl
  · intro i _
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact ((hg.mul (continuous_phi_EX027 i)).mul
      (Real.continuous_exp.comp (continuous_lin_x_EX027 w))).smul continuous_const

theorem cont_integrand_EX027 {g : Torus 1 → ℝ} (hg : Continuous g) (w : EuclideanSpace ℝ (Fin 2)) :
    Continuous fun x => g x * Real.exp (lin_EX027 w x) :=
  hg.mul (Real.continuous_exp.comp (continuous_lin_x_EX027 w))

theorem integrable_J_EX027 {g : Torus 1 → ℝ} (hg : Continuous g) (w : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun x => g x * Real.exp (lin_EX027 w x)) (haar 1) :=
  (cont_integrand_EX027 hg w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem J_add_EX027 {g₁ g₂ : Torus 1 → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (fun x => g₁ x + g₂ x) w = J_EX027 g₁ w + J_EX027 g₂ w := by
  unfold J_EX027
  simp_rw [add_mul]
  exact integral_add (integrable_J_EX027 h₁ w) (integrable_J_EX027 h₂ w)

theorem J_const_mul_EX027 (c : ℝ) (g : Torus 1 → ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (fun x => c * g x) w = c * J_EX027 g w := by
  unfold J_EX027
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

theorem J_sum_EX027 {ι : Type*} (s : Finset ι) (c : ι → ℝ) (g : ι → Torus 1 → ℝ)
    (hg : ∀ i, Continuous (g i)) (w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (fun x => ∑ i ∈ s, c i * g i x) w = ∑ i ∈ s, c i * J_EX027 (g i) w := by
  unfold J_EX027
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro i _
    exact (integrable_J_EX027 (hg i) w).const_mul (c i) |>.congr (Filter.Eventually.of_forall fun x => by simp)

theorem J_nonneg_EX027 {g : Torus 1 → ℝ} (hg : ∀ x, 0 ≤ g x) (w : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ J_EX027 g w :=
  integral_nonneg fun x => mul_nonneg (hg x) (Real.exp_pos _).le

theorem J_mono_EX027 {g₁ g₂ : Torus 1 → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (hle : ∀ x, g₁ x ≤ g₂ x) (w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 g₁ w ≤ J_EX027 g₂ w :=
  integral_mono (integrable_J_EX027 h₁ w) (integrable_J_EX027 h₂ w)
    fun x => mul_le_mul_of_nonneg_right (hle x) (Real.exp_pos _).le

theorem J_one_EX027 (w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (fun _ => 1) w = xyPartition (w 0) (w 1) := by
  simp [J_EX027, xyPartition, lin_EX027, phi_EX027, xyTrig, Fin.sum_univ_two]

theorem Z_pos_EX027 (w : EuclideanSpace ℝ (Fin 2)) : 0 < J_EX027 (fun _ => 1) w := by
  rw [J_one_EX027]; exact xyPartition_pos _ _

theorem Z_eq_bessel_EX027 (w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (fun _ => 1) w = besselI 0 ‖w‖ := by
  rw [J_one_EX027]
  have hn : ‖w‖ = Real.sqrt (w 0 ^ 2 + w 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hn]
  by_cases h : 0 < w 0 ^ 2 + w 1 ^ 2
  · exact DGPS.Examples.AttractiveXYCollapseEX026.partition_pos_EX026 _ _ h
  · have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
    rw [h0, h1]
    have := DGPS.Examples.AttractiveXYTilt.partition_EX023 0
    simpa using this

theorem hasFDerivAt_div_EX027 {a b : EuclideanSpace ℝ (Fin 2) → ℝ}
    {a' b' : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ} {w : EuclideanSpace ℝ (Fin 2)}
    (ha : HasFDerivAt a a' w) (hb : HasFDerivAt b b' w) (h : b w ≠ 0) :
    HasFDerivAt (fun y => a y / b y) ((b w)⁻¹ • a' - (a w / b w ^ 2) • b') w := by
  have hinv : HasFDerivAt (fun y => (b y)⁻¹) ((-(b w ^ 2)⁻¹) • b') w :=
    (hasDerivAt_inv h).comp_hasFDerivAt w hb
  have e : (fun y => a y / b y) = a * fun y => (b y)⁻¹ := by
    funext y; simp [div_eq_mul_inv]
  rw [e]
  refine (ha.mul hinv).congr_fderiv ?_
  ext z
  simp only [add_apply, smul_apply, sub_apply, smul_eq_mul]
  field_simp
  ring

/-- The partition function. -/
noncomputable def Z_EX027 (w : EuclideanSpace ℝ (Fin 2)) : ℝ := J_EX027 (fun _ => 1) w

/-- The cumulant generating function. -/
noncomputable def N_EX027 (w : EuclideanSpace ℝ (Fin 2)) : ℝ := Real.log (Z_EX027 w)

/-- The mean of `φ_i` in the tilted law. -/
noncomputable def M_EX027 (i : Fin 2) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  J_EX027 (phi_EX027 i) w / Z_EX027 w

/-- The gradient of the cumulant generating function. -/
noncomputable def dN_EX027 (w : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ∑ i, M_EX027 i w • EuclideanSpace.proj i

theorem Z_pos'_EX027 (w : EuclideanSpace ℝ (Fin 2)) : 0 < Z_EX027 w := Z_pos_EX027 w

theorem hasFDerivAt_Z_EX027 (w : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt Z_EX027
      (∑ i, J_EX027 (phi_EX027 i) w • EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) w := by
  have := hasFDerivAt_J_EX027 (g := fun _ => 1) continuous_const w
  refine (show HasFDerivAt Z_EX027 _ w from this).congr_fderiv ?_
  simp [dJ_EX027]

theorem hasFDerivAt_N_EX027 (w : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt N_EX027 (dN_EX027 w) w := by
  have h := (hasFDerivAt_Z_EX027 w).log (Z_pos'_EX027 w).ne'
  refine (show HasFDerivAt N_EX027 _ w from h).congr_fderiv ?_
  unfold dN_EX027 M_EX027
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]; congr 1; rw [div_eq_inv_mul]

/-- Derivative of `M_i`. -/
noncomputable def dM_EX027 (i : Fin 2) (w : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (Z_EX027 w)⁻¹ • dJ_EX027 (phi_EX027 i) w -
    (J_EX027 (phi_EX027 i) w / Z_EX027 w ^ 2) • ∑ j, J_EX027 (phi_EX027 j) w • EuclideanSpace.proj j

theorem hasFDerivAt_M_EX027 (i : Fin 2) (w : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (M_EX027 i) (dM_EX027 i w) w :=
  hasFDerivAt_div_EX027 (hasFDerivAt_J_EX027 (continuous_phi_EX027 i) w) (hasFDerivAt_Z_EX027 w)
    (Z_pos'_EX027 w).ne'

/-- The covariance matrix entries. -/
noncomputable def Cov_EX027 (w : EuclideanSpace ℝ (Fin 2)) (i j : Fin 2) : ℝ :=
  J_EX027 (fun x => phi_EX027 i x * phi_EX027 j x) w / Z_EX027 w - M_EX027 i w * M_EX027 j w

theorem dM_apply_EX027 (i : Fin 2) (w v : EuclideanSpace ℝ (Fin 2)) :
    dM_EX027 i w v = ∑ j, Cov_EX027 w i j * v j := by
  unfold dM_EX027 Cov_EX027 M_EX027 dJ_EX027
  simp only [sub_apply, smul_apply, sum_apply, smul_eq_mul, EuclideanSpace.coe_proj, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hZ := (Z_pos'_EX027 w).ne'
  field_simp

/-- The Hessian of the cumulant generating function. -/
noncomputable def d2N_EX027 (w : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ∑ i, (dM_EX027 i w).smulRight (EuclideanSpace.proj i)

theorem hasFDerivAt_dN_EX027 (w : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt dN_EX027 (d2N_EX027 w) w := by
  unfold dN_EX027 d2N_EX027
  refine HasFDerivAt.fun_sum fun i _ => ?_
  exact (hasFDerivAt_M_EX027 i w).smul_const (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

theorem d2N_apply_EX027 (w v u : EuclideanSpace ℝ (Fin 2)) :
    d2N_EX027 w v u = ∑ i, ∑ j, Cov_EX027 w i j * v j * u i := by
  unfold d2N_EX027
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply, EuclideanSpace.coe_proj,
    dM_apply_EX027, smul_eq_mul, Finset.sum_mul]

theorem continuous_lin_v_EX027 (v : EuclideanSpace ℝ (Fin 2)) : Continuous (lin_EX027 v) :=
  continuous_lin_x_EX027 v

theorem J_lin_EX027 (v w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (lin_EX027 v) w = ∑ i, v i * J_EX027 (phi_EX027 i) w :=
  J_sum_EX027 Finset.univ (fun i => v i) phi_EX027 continuous_phi_EX027 w

theorem J_lin_mul_EX027 (v w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (fun x => lin_EX027 v x * lin_EX027 v x) w =
      ∑ i, v i * ∑ j, v j * J_EX027 (fun x => phi_EX027 i x * phi_EX027 j x) w := by
  have e : (fun x => lin_EX027 v x * lin_EX027 v x) =
      fun x => ∑ i, v i * (∑ j, v j * (phi_EX027 i x * phi_EX027 j x)) := by
    funext x
    unfold lin_EX027
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, J_sum_EX027 Finset.univ (fun i => v i)
    (fun i x => ∑ j, v j * (phi_EX027 i x * phi_EX027 j x))
    (fun i => continuous_finsetSum _ fun j _ => continuous_const.mul
      ((continuous_phi_EX027 i).mul (continuous_phi_EX027 j))) w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [J_sum_EX027 Finset.univ (fun j => v j) (fun j x => phi_EX027 i x * phi_EX027 j x)
    (fun j => (continuous_phi_EX027 i).mul (continuous_phi_EX027 j)) w]

theorem d2N_self_EX027 (w v : EuclideanSpace ℝ (Fin 2)) :
    d2N_EX027 w v v = J_EX027 (fun x => lin_EX027 v x * lin_EX027 v x) w / Z_EX027 w -
      (J_EX027 (lin_EX027 v) w / Z_EX027 w) ^ 2 := by
  rw [d2N_apply_EX027, J_lin_mul_EX027, J_lin_EX027]
  simp only [Cov_EX027, M_EX027, Fin.sum_univ_two]
  have hZ := (Z_pos'_EX027 w).ne'
  field_simp
  ring

theorem J_sq_le_EX027 (v w : EuclideanSpace ℝ (Fin 2)) :
    J_EX027 (lin_EX027 v) w ^ 2 ≤ J_EX027 (fun x => lin_EX027 v x * lin_EX027 v x) w * Z_EX027 w := by
  have hZ := Z_pos'_EX027 w
  set m := J_EX027 (lin_EX027 v) w / Z_EX027 w with hm
  have hcont : Continuous (lin_EX027 v) := continuous_lin_v_EX027 v
  have h0 : 0 ≤ J_EX027 (fun x => (lin_EX027 v x - m) * (lin_EX027 v x - m)) w :=
    J_nonneg_EX027 (fun x => mul_self_nonneg _) w
  have e : (fun x => (lin_EX027 v x - m) * (lin_EX027 v x - m)) =
      fun x => (lin_EX027 v x * lin_EX027 v x + (-2 * m) * lin_EX027 v x) + m ^ 2 * 1 := by
    funext x; ring
  have e2 : J_EX027 (fun x => (lin_EX027 v x * lin_EX027 v x + (-2 * m) * lin_EX027 v x) + m ^ 2 * 1) w =
      J_EX027 (fun x => lin_EX027 v x * lin_EX027 v x) w + (-2 * m) * J_EX027 (lin_EX027 v) w +
        m ^ 2 * Z_EX027 w := by
    rw [J_add_EX027 (g₁ := fun x => lin_EX027 v x * lin_EX027 v x + (-2 * m) * lin_EX027 v x)
      (g₂ := fun _ => m ^ 2 * 1) ((hcont.mul hcont).add (continuous_const.mul hcont)) continuous_const,
      J_add_EX027 (g₁ := fun x => lin_EX027 v x * lin_EX027 v x) (g₂ := fun x => (-2 * m) * lin_EX027 v x)
        (hcont.mul hcont) (continuous_const.mul hcont),
      J_const_mul_EX027 (-2 * m) (lin_EX027 v), J_const_mul_EX027 (m ^ 2) (fun _ => 1)]
    rfl
  rw [e, e2] at h0
  have : m * Z_EX027 w = J_EX027 (lin_EX027 v) w := by rw [hm]; field_simp
  nlinarith

theorem d2N_nonneg_EX027 (w v : EuclideanSpace ℝ (Fin 2)) : 0 ≤ d2N_EX027 w v v := by
  rw [d2N_self_EX027]
  have hZ := Z_pos'_EX027 w
  have := J_sq_le_EX027 v w
  rw [div_pow, sub_nonneg, div_le_div_iff₀ (by positivity) hZ]
  nlinarith

theorem norm_sq_EX027 (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

theorem lin_sq_le_EX027 (v : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    lin_EX027 v x * lin_EX027 v x ≤ ‖v‖ ^ 2 := by
  rw [norm_sq_EX027]
  have := phi_sq_EX027 x
  unfold lin_EX027
  rw [Fin.sum_univ_two]
  nlinarith [sq_nonneg (v 0 * phi_EX027 1 x - v 1 * phi_EX027 0 x)]

theorem d2N_le_EX027 (w v : EuclideanSpace ℝ (Fin 2)) : d2N_EX027 w v v ≤ ‖v‖ ^ 2 := by
  rw [d2N_self_EX027]
  have hZ := Z_pos'_EX027 w
  have hcont : Continuous (lin_EX027 v) := continuous_lin_v_EX027 v
  have h1 : J_EX027 (fun x => lin_EX027 v x * lin_EX027 v x) w ≤ J_EX027 (fun _ => ‖v‖ ^ 2) w :=
    J_mono_EX027 (hcont.mul hcont) continuous_const (lin_sq_le_EX027 v) w
  have h2 : J_EX027 (fun _ => ‖v‖ ^ 2) w = ‖v‖ ^ 2 * Z_EX027 w :=
    by simpa only [mul_one, Z_EX027] using J_const_mul_EX027 (‖v‖ ^ 2) (fun _ => 1) w
  have h3 : J_EX027 (fun x => lin_EX027 v x * lin_EX027 v x) w / Z_EX027 w ≤ ‖v‖ ^ 2 := by
    rw [div_le_iff₀ hZ]; linarith
  nlinarith [sq_nonneg (J_EX027 (lin_EX027 v) w / Z_EX027 w)]

theorem Cov_symm_EX027 (w : EuclideanSpace ℝ (Fin 2)) (i j : Fin 2) :
    Cov_EX027 w i j = Cov_EX027 w j i := by
  unfold Cov_EX027
  rw [mul_comm (M_EX027 i w), show (fun x => phi_EX027 i x * phi_EX027 j x) =
    fun x => phi_EX027 j x * phi_EX027 i x from funext fun x => mul_comm _ _]

theorem d2N_symm_EX027 (w v u : EuclideanSpace ℝ (Fin 2)) : d2N_EX027 w v u = d2N_EX027 w u v := by
  simp only [d2N_apply_EX027, Fin.sum_univ_two, Cov_symm_EX027 w 1 0]
  ring

theorem d2N_cs_EX027 (w v u : EuclideanSpace ℝ (Fin 2)) :
    |d2N_EX027 w v u| ≤ ‖v‖ * ‖u‖ := by
  have hq : ∀ t : ℝ, 0 ≤ d2N_EX027 w u u * (t * t) + (2 * d2N_EX027 w v u) * t + d2N_EX027 w v v := by
    intro t
    have h := d2N_nonneg_EX027 w (v + t • u)
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul] at h
    rw [d2N_symm_EX027 w u v] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have h1 : d2N_EX027 w v u ^ 2 ≤ d2N_EX027 w v v * d2N_EX027 w u u := by nlinarith
  have h2 := d2N_le_EX027 w v
  have h3 := d2N_le_EX027 w u
  have h4 := d2N_nonneg_EX027 w v
  have h5 := d2N_nonneg_EX027 w u
  have h6 : d2N_EX027 w v u ^ 2 ≤ (‖v‖ * ‖u‖) ^ 2 := by
    calc d2N_EX027 w v u ^ 2 ≤ d2N_EX027 w v v * d2N_EX027 w u u := h1
      _ ≤ ‖v‖ ^ 2 * ‖u‖ ^ 2 := by gcongr
      _ = (‖v‖ * ‖u‖) ^ 2 := by ring
  exact abs_le.2 (abs_le_of_sq_le_sq' h6 (by positivity))


/-- The first basis vector `e₁`. -/
noncomputable def e1_EX027 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The affine map `z ↦ h e₁ + 4 z`. -/
noncomputable def A_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  h • e1_EX027 + (4 : ℝ) • z

/-- The free-energy function `Ψ_h(z) = 2|z|² - log I₀(|h e₁ + 4 z|)`. -/
noncomputable def Psi_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  2 * ‖z‖ ^ 2 - Real.log (besselI 0 ‖A_EX027 h z‖)

theorem Psi_eq_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    Psi_EX027 h z = 2 * ‖z‖ ^ 2 - N_EX027 (A_EX027 h z) := by
  unfold Psi_EX027 N_EX027 Z_EX027
  rw [Z_eq_bessel_EX027]

theorem A_apply0_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : A_EX027 h z 0 = h + 4 * z 0 := by
  simp [A_EX027, e1_EX027]

theorem A_apply1_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : A_EX027 h z 1 = 4 * z 1 := by
  simp [A_EX027, e1_EX027]

theorem hasFDerivAt_A_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (A_EX027 h) ((4 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) z :=
  ((hasFDerivAt_id z).const_smul (4 : ℝ)).const_add (h • e1_EX027)

/-- The identity bilinear form `(z, u) ↦ ∑ zᵢ uᵢ` as a continuous linear map. -/
noncomputable def Sq_EX027 :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  ∑ i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).smulRight
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

theorem Sq_apply_EX027 (z u : EuclideanSpace ℝ (Fin 2)) : Sq_EX027 z u = z 0 * u 0 + z 1 * u 1 := by
  simp [Sq_EX027, Fin.sum_univ_two]

theorem innerSL_eq_Sq_EX027 (z : EuclideanSpace ℝ (Fin 2)) : innerSL ℝ z = Sq_EX027 z := by
  ext u
  rw [innerSL_apply_apply, Sq_apply_EX027]
  simp [Fin.sum_univ_two, PiLp.inner_apply]
  ring

/-- The gradient of `Ψ_h`. -/
noncomputable def gradPsi_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (4 : ℝ) • Sq_EX027 z - (4 : ℝ) • dN_EX027 (A_EX027 h z)

theorem hasFDerivAt_Psi_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (Psi_EX027 h) (gradPsi_EX027 h z) z := by
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := (hasFDerivAt_N_EX027 (A_EX027 h z)).comp z (hasFDerivAt_A_EX027 h z)
  have h3 := (h1.const_mul 2).sub h2
  have e : Psi_EX027 h = fun x => 2 * ‖x‖ ^ 2 - (N_EX027 ∘ A_EX027 h) x := by
    funext x; exact Psi_eq_EX027 h x
  rw [e]
  refine h3.congr_fderiv ?_
  unfold gradPsi_EX027
  rw [innerSL_eq_Sq_EX027]
  ext u
  simp
  ring

/-- The Hessian of `Ψ_h`. -/
noncomputable def hessPsi_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (4 : ℝ) • Sq_EX027 - (16 : ℝ) • d2N_EX027 (A_EX027 h z)

theorem hasFDerivAt_gradPsi_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (gradPsi_EX027 h) (hessPsi_EX027 h z) z := by
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => Sq_EX027 x) Sq_EX027 z :=
    Sq_EX027.hasFDerivAt
  have h2 := (hasFDerivAt_dN_EX027 (A_EX027 h z)).comp z (hasFDerivAt_A_EX027 h z)
  have h3 := (h1.const_smul (4 : ℝ)).sub (h2.const_smul (4 : ℝ))
  refine h3.congr_fderiv ?_
  unfold hessPsi_EX027
  ext v u
  simp
  ring


theorem fderiv_Psi_EX027 (h : ℝ) : fderiv ℝ (Psi_EX027 h) = gradPsi_EX027 h :=
  funext fun z => (hasFDerivAt_Psi_EX027 h z).fderiv

theorem fderiv_fderiv_Psi_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ (Psi_EX027 h)) z = hessPsi_EX027 h z := by
  rw [fderiv_Psi_EX027]; exact (hasFDerivAt_gradPsi_EX027 h z).fderiv

theorem differentiable_Psi_EX027 (h : ℝ) : Differentiable ℝ (Psi_EX027 h) :=
  fun z => (hasFDerivAt_Psi_EX027 h z).differentiableAt

theorem differentiable_fderiv_Psi_EX027 (h : ℝ) : Differentiable ℝ (fderiv ℝ (Psi_EX027 h)) := by
  rw [fderiv_Psi_EX027]; exact fun z => (hasFDerivAt_gradPsi_EX027 h z).differentiableAt

theorem abs_Sq_le_EX027 (v u : EuclideanSpace ℝ (Fin 2)) : |Sq_EX027 v u| ≤ ‖v‖ * ‖u‖ := by
  have : Sq_EX027 v u = inner ℝ v u := by
    rw [← innerSL_eq_Sq_EX027, innerSL_apply_apply]
  rw [this]
  exact abs_real_inner_le_norm v u

theorem norm_hessPsi_le_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ‖hessPsi_EX027 h z‖ ≤ 20 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have e : hessPsi_EX027 h z v u = 4 * Sq_EX027 v u - 16 * d2N_EX027 (A_EX027 h z) v u := by
    simp [hessPsi_EX027]
  rw [e, Real.norm_eq_abs]
  have h1 := abs_Sq_le_EX027 v u
  have h2 := d2N_cs_EX027 (A_EX027 h z) v u
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [mul_nonneg (norm_nonneg v) (norm_nonneg u)]

theorem lipschitz_gradPsi_EX027 (h : ℝ) (y z : EuclideanSpace ℝ (Fin 2)) :
    ‖gradPsi_EX027 h z - gradPsi_EX027 h y‖ ≤ 20 * ‖z - y‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (f := gradPsi_EX027 h) (C := 20)
    (fun x _ => (hasFDerivAt_gradPsi_EX027 h x).differentiableAt)
    (fun x _ => by rw [(hasFDerivAt_gradPsi_EX027 h x).fderiv]; exact norm_hessPsi_le_EX027 h x)
    convex_univ (Set.mem_univ y) (Set.mem_univ z)

theorem psi_taylor_EX027 (h : ℝ) (y z : EuclideanSpace ℝ (Fin 2)) :
    Psi_EX027 h z ≤ Psi_EX027 h y + gradPsi_EX027 h y (z - y) + 10 * ‖z - y‖ ^ 2 := by
  set d := z - y with hd
  let φ : ℝ → ℝ := fun τ =>
    Psi_EX027 h (y + τ • d) - τ * gradPsi_EX027 h y d - 10 * τ ^ 2 * ‖d‖ ^ 2
  have hder : ∀ τ : ℝ, HasDerivAt φ
      (gradPsi_EX027 h (y + τ • d) d - gradPsi_EX027 h y d - 10 * (2 * τ) * ‖d‖ ^ 2) τ := by
    intro τ
    have hγ : HasDerivAt (fun τ : ℝ => y + τ • d) d τ :=
      (((hasDerivAt_id τ).smul_const d).const_add y).congr_deriv (one_smul ℝ d)
    have h1 := (hasFDerivAt_Psi_EX027 h (y + τ • d)).comp_hasDerivAt τ hγ
    have h2 := (hasDerivAt_id τ).mul_const (gradPsi_EX027 h y d)
    have h3 := ((hasDerivAt_pow 2 τ).const_mul 10).mul_const (‖d‖ ^ 2)
    have h4 := (h1.sub h2).sub h3
    refine h4.congr_deriv ?_
    simp
  have hanti : AntitoneOn φ (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun τ _ => (hder τ).continuousAt.continuousWithinAt)
      (fun τ _ => (hder τ).differentiableAt.differentiableWithinAt) ?_
    intro τ hτ
    rw [interior_Ici] at hτ
    have hτ0 : 0 < τ := hτ
    rw [(hder τ).deriv]
    have h1 := lipschitz_gradPsi_EX027 h y (y + τ • d)
    have h2 := ContinuousLinearMap.le_opNorm (gradPsi_EX027 h (y + τ • d) - gradPsi_EX027 h y) d
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0, sub_apply] at h1 h2
    have h3 : 0 ≤ ‖d‖ := norm_nonneg d
    have h4 := le_trans (le_abs_self _) h2
    have h5 := mul_le_mul_of_nonneg_right h1 h3
    nlinarith [h4, h5]
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [φ, zero_smul, add_zero, one_smul, sub_zero, zero_mul, one_mul, one_pow, mul_one] at this
  have e : y + (z - y) = z := by abel
  rw [← hd] at e
  rw [e] at this
  linarith

theorem xyTrig_eq_lin_EX027 (w : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    xyTrig (w 0) (w 1) 0 x = lin_EX027 w x := by
  simp [xyTrig, lin_EX027, phi_EX027, Fin.sum_univ_two]

theorem M_eq_integral_EX027 (i : Fin 2) (w : EuclideanSpace ℝ (Fin 2)) :
    M_EX027 i w = ∫ x, phi_EX027 i x ∂(xyFrozen (w 0) (w 1)).measure := by
  rw [frozen_measure_EX026]
  change _ = ∫ x, phi_EX027 i x ∂(haar 1).tilted (xyTrig (w 0) (w 1) 0)
  rw [integral_tilted]
  simp_rw [xyTrig_eq_lin_EX027, smul_eq_mul]
  have e : ∀ x, Real.exp (lin_EX027 w x) / (∫ y, Real.exp (lin_EX027 w y) ∂haar 1) * phi_EX027 i x =
      (phi_EX027 i x * Real.exp (lin_EX027 w x)) / (∫ y, Real.exp (lin_EX027 w y) ∂haar 1) := by
    intro x; ring
  simp_rw [e]
  rw [integral_div]
  simp [M_EX027, J_EX027, Z_EX027]

/-- The first component of the residual `R_h(z) = z - T_h(z)`. -/
noncomputable def R1_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  z 0 - xyZ1 (xyFrozen (h + 4 * z 0) (4 * z 1)).measure

/-- The second component of the residual. -/
noncomputable def R2_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  z 1 - xyZ2 (xyFrozen (h + 4 * z 0) (4 * z 1)).measure

theorem gradPsi_apply_EX027 (h : ℝ) (z u : EuclideanSpace ℝ (Fin 2)) :
    gradPsi_EX027 h z u = 4 * (R1_EX027 h z * u 0 + R2_EX027 h z * u 1) := by
  have m0 := M_eq_integral_EX027 0 (A_EX027 h z)
  have m1 := M_eq_integral_EX027 1 (A_EX027 h z)
  rw [A_apply0_EX027, A_apply1_EX027] at m0 m1
  have e0 : xyZ1 (xyFrozen (h + 4 * z 0) (4 * z 1)).measure = M_EX027 0 (A_EX027 h z) := by
    rw [m0]; rfl
  have e1 : xyZ2 (xyFrozen (h + 4 * z 0) (4 * z 1)).measure = M_EX027 1 (A_EX027 h z) := by
    rw [m1]; rfl
  simp only [R1_EX027, R2_EX027, e0, e1, gradPsi_EX027, dN_EX027, sub_apply, smul_apply, add_apply,
    Sq_apply_EX027, Fin.sum_univ_two, smul_eq_mul, EuclideanSpace.coe_proj]
  ring

theorem gradPsi_zstar_EX027 {h t : ℝ} (ht : t = 4 * besselRatio t + h) :
    gradPsi_EX027 h (besselRatio t • e1_EX027) = 0 := by
  ext u
  rw [gradPsi_apply_EX027]
  have h0 : h + 4 * (besselRatio t • e1_EX027) 0 = t := by simp [e1_EX027]; linarith
  have h1 : 4 * (besselRatio t • e1_EX027) 1 = 0 := by simp [e1_EX027]
  have hR1 : R1_EX027 h (besselRatio t • e1_EX027) = 0 := by
    unfold R1_EX027
    rw [h0, h1]
    have := law_cos_EX023 t
    have h2 : (xyFrozen t 0).measure = (xyLaw_EX023 t : Measure (Torus 1)) := rfl
    rw [h2, this]; simp [e1_EX027]
  have hR2 : R2_EX027 h (besselRatio t • e1_EX027) = 0 := by
    unfold R2_EX027
    rw [h0, h1]
    have := law_sin_EX023 t
    have h2 : (xyFrozen t 0).measure = (xyLaw_EX023 t : Measure (Torus 1)) := rfl
    rw [h2, this]; simp [e1_EX027]
  rw [hR1, hR2]; simp

theorem norm_smul_e1_EX027 (c : ℝ) : ‖c • e1_EX027‖ = |c| := by
  simp [e1_EX027, norm_smul]

theorem Psi_zstar_EX027 {h t : ℝ} (ht : 0 < t) (hte : t = 4 * besselRatio t + h) :
    Psi_EX027 h (besselRatio t • e1_EX027) =
      2 * besselRatio t ^ 2 - Real.log (besselI 0 t) := by
  have hA : A_EX027 h (besselRatio t • e1_EX027) = t • e1_EX027 := by
    unfold A_EX027
    rw [smul_smul, ← add_smul]
    congr 1
    linarith
  unfold Psi_EX027
  rw [hA, norm_smul_e1_EX027, norm_smul_e1_EX027, abs_of_pos ht, sq_abs]

theorem freeEnergyMinimumReal_EX027 {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hte : t = 4 * besselRatio t + h) :
    freeEnergyMinimumReal (attractiveXY 4 h) =
      2 + Psi_EX027 h (besselRatio t • e1_EX027) := by
  obtain ⟨t', ht', hte', hu, -, -, -, hmin, -⟩ :=
    (tilted_stationary_scalar_root_and_global_minimizer (κ := 4) (h := h) (by norm_num) hh).2.2
  have htt : t = t' := hu t ht hte
  subst htt
  have h1 := (hmin (xyLaw_EX023 t)).2 rfl
  rw [law_freeEnergy_EX023, ← coe_freeEnergyMinimumReal, EReal.coe_eq_coe_iff] at h1
  rw [← h1, Psi_zstar_EX027 ht hte]
  have : t * besselRatio t = (4 * besselRatio t + h) * besselRatio t := by rw [← hte]
  nlinarith [this]

/-- The mean vector `(∫ cos dν, ∫ sin dν)` of a measure on the circle. -/
noncomputable def zvec_EX027 (ν : Measure (Torus 1)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![xyZ1 ν, xyZ2 ν]

theorem zvec_apply0_EX027 (ν : Measure (Torus 1)) : zvec_EX027 ν 0 = xyZ1 ν := by
  simp [zvec_EX027]

theorem zvec_apply1_EX027 (ν : Measure (Torus 1)) : zvec_EX027 ν 1 = xyZ2 ν := by
  simp [zvec_EX027]

theorem xyPartition_eq_EX027 (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    xyPartition (h + 4 * z 0) (4 * z 1) = besselI 0 ‖A_EX027 h z‖ := by
  rw [← Z_eq_bessel_EX027, J_one_EX027, ← A_apply0_EX027, ← A_apply1_EX027]

theorem cross_EX027 (ρ : AbsoluteDensity 1) (a b : ℝ) :
    ∫ x, ρ.density x * Real.log ((xyFrozen a b).density x) ∂haar 1 =
      a * xyZ1 (densityMeasure ρ : Measure (Torus 1)) +
        b * xyZ2 (densityMeasure ρ : Measure (Torus 1)) - Real.log (xyPartition a b) := by
  rw [← integral_densityMeasure]
  simp_rw [log_xyFrozen_density, xyTrig]
  have hc : Continuous fun x : Torus 1 => (xyMode x).re :=
    Complex.continuous_re.comp continuous_xyMode
  have hs : Continuous fun x : Torus 1 => (xyMode x).im :=
    Complex.continuous_im.comp continuous_xyMode
  have i1 := integrable_xyMode_re (densityMeasure ρ : Measure (Torus 1))
  have i2 := integrable_xyMode_im (densityMeasure ρ : Measure (Torus 1))
  have j1 : Integrable (fun x : Torus 1 => a * (xyMode x).re) (densityMeasure ρ : Measure (Torus 1)) :=
    i1.const_mul a
  have j2 : Integrable (fun x : Torus 1 => b * (xyMode x).im) (densityMeasure ρ : Measure (Torus 1)) :=
    i2.const_mul b
  have j12 : Integrable (fun x : Torus 1 => a * (xyMode x).re + b * (xyMode x).im)
      (densityMeasure ρ : Measure (Torus 1)) := j1.add j2
  rw [integral_add j12 (integrable_const _), integral_add j1 j2, integral_const_mul,
    integral_const_mul]
  simp [xyZ1, xyZ2]
  ring

theorem gap_identity_EX027 {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hte : t = 4 * besselRatio t + h) (F : SpeciesFamily 1) :
    (speciesGap (attractiveXY 4 h) F : ℝ) =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
        (xyFrozen (h + 4 * xyZ1 (densityMeasure (barycenter F) : Measure (Torus 1)))
          (4 * xyZ2 (densityMeasure (barycenter F) : Measure (Torus 1)))).measure).toReal +
      (Psi_EX027 h (zvec_EX027 (densityMeasure (barycenter F) : Measure (Torus 1))) -
        Psi_EX027 h (besselRatio t • e1_EX027)) := by
  set ν : ProbabilityMeasure (Torus 1) := densityMeasure (barycenter F) with hν
  set z := zvec_EX027 (ν : Measure (Torus 1)) with hz
  set P := xyFrozen (h + 4 * xyZ1 (ν : Measure (Torus 1))) (4 * xyZ2 (ν : Measure (Torus 1)))
    with hP
  have hS := DGPS.Structural.sum_relativeEntropy_reference_sub F P
  have hR := (DGPS.Structural.relativeEntropy_reference P (barycenter F)).2
  have hcr := cross_EX027 (barycenter F) (h + 4 * xyZ1 (ν : Measure (Torus 1)))
    (4 * xyZ2 (ν : Measure (Torus 1)))
  have hF := freeEnergyMinimumReal_EX027 hh ht hte
  have hZ : xyPartition (h + 4 * xyZ1 (ν : Measure (Torus 1))) (4 * xyZ2 (ν : Measure (Torus 1))) =
      besselI 0 ‖A_EX027 h z‖ := by
    have := xyPartition_eq_EX027 h z
    rwa [hz, zvec_apply0_EX027, zvec_apply1_EX027] at this
  have hn : ‖z‖ ^ 2 = xyZ1 (ν : Measure (Torus 1)) ^ 2 + xyZ2 (ν : Measure (Torus 1)) ^ 2 := by
    rw [norm_sq_EX027, hz, zvec_apply0_EX027, zvec_apply1_EX027]
  rw [coe_speciesGap]
  unfold speciesRawGap
  rw [potentialEnergy_attractiveXY, interactionEnergy_attractiveXY, hF]
  unfold Psi_EX027
  rw [hZ] at hcr
  rw [hn]
  have hcr' : ∫ x, (barycenter F).density x * Real.log (P.density x) ∂haar 1 =
      (h + 4 * xyZ1 (ν : Measure (Torus 1))) * xyZ1 (ν : Measure (Torus 1)) +
        4 * xyZ2 (ν : Measure (Torus 1)) * xyZ2 (ν : Measure (Torus 1)) -
          Real.log (besselI 0 ‖A_EX027 h z‖) := hcr
  rw [hcr'] at hR
  nlinarith [hS, hR]

theorem unit_disk_EX027 (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    xyZ1 ν ^ 2 + xyZ2 ν ^ 2 ≤ 1 := by
  set c := xyZ1 ν with hc
  set s := xyZ2 ν with hs
  have i1 := integrable_xyMode_re ν
  have i2 := integrable_xyMode_im ν
  have j1 : Integrable (fun x : Torus 1 => c * (xyMode x).re) ν := i1.const_mul c
  have j2 : Integrable (fun x : Torus 1 => s * (xyMode x).im) ν := i2.const_mul s
  have hint : ∫ x, (c * (xyMode x).re + s * (xyMode x).im) ∂ν = c ^ 2 + s ^ 2 := by
    rw [integral_add j1 j2, integral_const_mul, integral_const_mul]
    simp only [hc, hs, xyZ1, xyZ2]
    ring
  have hle : ∫ x, (c * (xyMode x).re + s * (xyMode x).im) ∂ν ≤ ∫ x, ((c ^ 2 + s ^ 2 + 1) / 2) ∂ν :=
    integral_mono (j1.add j2) (integrable_const _) fun x => by
      have h1 := xyMode_norm x
      have h2 := Complex.sq_norm (xyMode x)
      rw [h1, Complex.normSq_apply] at h2
      nlinarith [sq_nonneg (c - (xyMode x).re), sq_nonneg (s - (xyMode x).im)]
  rw [hint] at hle
  simp at hle
  linarith

theorem residual_tv_EX027 (ν : Measure (Torus 1)) [IsProbabilityMeasure ν]
    (P : BoundedPositiveReference 1) (hH : relativeEntropy ν P.measure ≠ ⊤) :
    (xyZ1 ν - xyZ1 P.measure) ^ 2 + (xyZ2 ν - xyZ2 P.measure) ^ 2 ≤
      2 * (relativeEntropy ν P.measure).toReal := by
  set r1 := xyZ1 ν - xyZ1 P.measure with hr1
  set r2 := xyZ2 ν - xyZ2 P.measure with hr2
  set Rn := r1 ^ 2 + r2 ^ 2 with hRn
  set q := Real.sqrt Rn with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = Rn := Real.sq_sqrt (by positivity)
  let g : Torus 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => r1 * (xyMode x).re + r2 * (xyMode x).im,
      ((continuous_const.mul (Complex.continuous_re.comp continuous_xyMode)).add
        (continuous_const.mul (Complex.continuous_im.comp continuous_xyMode)))⟩
  have hpt : ∀ x, |r1 * (xyMode x).re + r2 * (xyMode x).im| ≤ q := by
    intro x
    refine Real.abs_le_sqrt ?_
    have h1 := xyMode_norm x
    have h2 := Complex.sq_norm (xyMode x)
    rw [h1, Complex.normSq_apply] at h2
    nlinarith [sq_nonneg (r1 * (xyMode x).im - r2 * (xyMode x).re)]
  have hg : ‖g‖ ≤ q := (BoundedContinuousFunction.norm_le hq0).2 fun x => by
    simpa [g, Real.norm_eq_abs] using hpt x
  have hint : ∀ m : Measure (Torus 1), IsProbabilityMeasure m →
      ∫ x, g x ∂m = r1 * xyZ1 m + r2 * xyZ2 m := by
    intro m hm
    have i1 := integrable_xyMode_re m
    have i2 := integrable_xyMode_im m
    show ∫ x, (r1 * (xyMode x).re + r2 * (xyMode x).im) ∂m = _
    rw [integral_add (i1.const_mul r1) (i2.const_mul r2), integral_const_mul, integral_const_mul]
    rfl
  have hdiff : (∫ x, g x ∂ν) - ∫ x, g x ∂P.measure = Rn := by
    rw [hint ν inferInstance, hint P.measure inferInstance, hRn, hr1, hr2]
    ring
  have hTV := DGPS.Structural.abs_integral_sub_le_fullVariation ν P.measure g
  have hT0 : 0 ≤ fullVariation ν P.measure := fullVariation_nonneg _ _
  have hpin := pinsker_fullVariation_real ν P.measure hH
  rw [hdiff, abs_of_nonneg (by rw [hRn]; positivity)] at hTV
  have h3 : Rn ≤ q * fullVariation ν P.measure :=
    hTV.trans (mul_le_mul_of_nonneg_right hg hT0)
  have h4 : q ^ 2 ≤ fullVariation ν P.measure ^ 2 := by
    by_cases hz : q = 0
    · rw [hz]; nlinarith [sq_nonneg (fullVariation ν P.measure)]
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hz)
      have : q ≤ fullVariation ν P.measure := by
        refine le_of_mul_le_mul_left ?_ hqpos
        nlinarith [hqq]
      exact pow_le_pow_left₀ hq0 this 2
  linarith

/-- The mean vector `z = ρ̄(φ⃗) = (∫ cos dρ̄, ∫ sin dρ̄)` of the barycenter of a species family. -/
noncomputable def zbar_EX027 (F : SpeciesFamily 1) : EuclideanSpace ℝ (Fin 2) :=
  zvec_EX027 (densityMeasure (barycenter F) : Measure (Torus 1))

theorem zbar_apply0_EX027 (F : SpeciesFamily 1) :
    zbar_EX027 F 0 = xyZ1 (densityMeasure (barycenter F) : Measure (Torus 1)) :=
  zvec_apply0_EX027 _

theorem zbar_apply1_EX027 (F : SpeciesFamily 1) :
    zbar_EX027 F 1 = xyZ2 (densityMeasure (barycenter F) : Measure (Torus 1)) :=
  zvec_apply1_EX027 _

/-- `E = ∑ θ_s H(ρ_s | p_{h,z})` with `z = ρ̄(φ⃗)` and `p_{h,z}` the frozen law of the
attractive XY model; the entropies are the real parts of the (finite) relative entropies. -/
noncomputable def E_EX027 (h : ℝ) (F : SpeciesFamily 1) : ℝ :=
  ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
    (xyFrozen (h + 4 * zbar_EX027 F 0) (4 * zbar_EX027 F 1)).measure).toReal

theorem E_eq_EX027 (h : ℝ) (F : SpeciesFamily 1) :
    E_EX027 h F = ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
        (xyFrozen (h + 4 * xyZ1 (densityMeasure (barycenter F) : Measure (Torus 1)))
          (4 * xyZ2 (densityMeasure (barycenter F) : Measure (Torus 1)))).measure).toReal := by
  unfold E_EX027
  rw [zbar_apply0_EX027, zbar_apply1_EX027]

theorem gap_identity'_EX027 {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    (hte : t = 4 * besselRatio t + h) (F : SpeciesFamily 1) :
    (speciesGap (attractiveXY 4 h) F : ℝ) =
      E_EX027 h F + (Psi_EX027 h (zbar_EX027 F) - Psi_EX027 h (besselRatio t • e1_EX027)) := by
  rw [E_eq_EX027]
  exact gap_identity_EX027 hh ht hte F

theorem residual_E_EX027 (h : ℝ) (F : SpeciesFamily 1) :
    R1_EX027 h (zbar_EX027 F) ^ 2 + R2_EX027 h (zbar_EX027 F) ^ 2 ≤ 2 * E_EX027 h F := by
  set ν : ProbabilityMeasure (Torus 1) := densityMeasure (barycenter F) with hν
  set P := xyFrozen (h + 4 * xyZ1 (ν : Measure (Torus 1))) (4 * xyZ2 (ν : Measure (Torus 1)))
    with hP
  have hνH := (DGPS.Structural.relativeEntropy_reference P (barycenter F)).1
  have hle := DGPS.Structural.relativeEntropy_barycenter_le_sum F P
  have htv := residual_tv_EX027 (ν : Measure (Torus 1)) P hνH
  rw [E_eq_EX027]
  unfold R1_EX027 R2_EX027
  rw [zbar_apply0_EX027, zbar_apply1_EX027]
  linarith

theorem dissipation_bound_EX027 {hc ε : ℝ} (hc0 : 0 < hc) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (b : AbsoluteDrift (attractiveXY 4 (hc + ε))) (F : SpeciesFamily 1) :
    ENNReal.ofReal (2 * (a0 * Real.exp (-(2 * (hc + 5)))) * E_EX027 (hc + ε) F) ≤
      speciesDissipation (attractiveXY 4 (hc + ε)) b F := by
  set ν : ProbabilityMeasure (Torus 1) := densityMeasure (barycenter F) with hν
  set P := xyFrozen (hc + ε + 4 * xyZ1 (ν : Measure (Torus 1))) (4 * xyZ2 (ν : Measure (Torus 1)))
    with hP
  set ℓ0 : ℝ := a0 * Real.exp (-(2 * (hc + 5))) with hℓ0
  have hℓpos : 0 < ℓ0 := mul_pos a0_pos (Real.exp_pos _)
  have hfin : ∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
      P.measure ≠ ⊤ := fun s => (DGPS.Structural.relativeEntropy_reference P (F.density s)).1
  have hlsi : ENNReal.ofReal ℓ0 ≤ ordinaryLSRate P :=
    xyFrozen_lsi_EX026 hc0 hε0 hε1 (unit_disk_EX027 (ν : Measure (Torus 1)))
  have hterm : ∀ s, ENNReal.ofReal (F.weight s * (2 * ℓ0 *
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1)) P.measure).toReal)) =
      ENNReal.ofReal (F.weight s) * (2 * ENNReal.ofReal ℓ0 *
        relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1)) P.measure) := by
    intro s
    rw [ENNReal.ofReal_mul (F.weight_nonneg s), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_toReal (hfin s)]
  have hrw : 2 * ℓ0 * E_EX027 (hc + ε) F = ∑ s, F.weight s * (2 * ℓ0 *
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1)) P.measure).toReal) := by
    rw [E_eq_EX027, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hrw, ENNReal.ofReal_sum_of_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) (mul_nonneg (by positivity) ENNReal.toReal_nonneg),
    speciesDissipation_attractiveXY]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [hterm s]
  refine mul_le_mul' le_rfl (le_trans ?_
    (DGPS.Structural.budget_lsi_fisher P _ (hfin s)))
  exact mul_le_mul' (mul_le_mul' le_rfl hlsi) le_rfl

theorem norm_sub_zstar_sq_EX027 (z : EuclideanSpace ℝ (Fin 2)) (c : ℝ) :
    ‖z - c • e1_EX027‖ ^ 2 = (z 0 - c) ^ 2 + z 1 ^ 2 := by
  rw [norm_sq_EX027]
  simp [e1_EX027]

/-- The real inequality behind the rate bound: `ε² G ≤ (1 + 20 C_R²) E`. -/
theorem gap_le_EX027 {s hc : ℝ} (hs : 0 < s) (hd : deriv besselRatio s = 1 / 4)
    (hhc : hc = 4 * besselRatio s - s) {ε t : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hte : t = 4 * besselRatio t + (hc + ε)) (F : SpeciesFamily 1) :
    0 ≤ E_EX027 (hc + ε) F ∧
    ε ^ 2 * (speciesGap (attractiveXY 4 (hc + ε)) F : ℝ) ≤
      (1 + 20 * (max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc))) ^ 2) *
        E_EX027 (hc + ε) F := by
  obtain ⟨hc0, -, hres, -, -⟩ := uniform_fold_residual_bound hs hd hhc
  set CR := max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc)) with hCR
  set z := zbar_EX027 F with hzdef
  set E := E_EX027 (hc + ε) F with hE
  have hunit : z 0 ^ 2 + z 1 ^ 2 ≤ 1 := by
    rw [hzdef, zbar_apply0_EX027, zbar_apply1_EX027]
    exact unit_disk_EX027 _
  have hresid := hres ε (z 0) (z 1) t hε0 hε1 hunit ht hte
  set Y := R1_EX027 (hc + ε) z ^ 2 + R2_EX027 (hc + ε) z ^ 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hYE : Y ≤ 2 * E := residual_E_EX027 (hc + ε) F
  have hE0 : 0 ≤ E := by linarith
  refine ⟨hE0, ?_⟩
  set X := (z 0 - besselRatio t) ^ 2 + z 1 ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hresid' : Real.sqrt X ≤ CR * Real.sqrt Y / ε := by
    simpa [hX, hY, R1_EX027, R2_EX027] using hresid
  have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg X) hresid' 2
  rw [Real.sq_sqrt hX0, div_pow, mul_pow, Real.sq_sqrt hY0,
    le_div_iff₀ (by positivity)] at h1
  set G : ℝ := (speciesGap (attractiveXY 4 (hc + ε)) F : ℝ) with hGdef
  set Dp : ℝ := Psi_EX027 (hc + ε) z - Psi_EX027 (hc + ε) (besselRatio t • e1_EX027) with hDp
  have hG : G = E + Dp := gap_identity'_EX027 (h := hc + ε) (by linarith) ht hte F
  have hT := psi_taylor_EX027 (hc + ε) (besselRatio t • e1_EX027) z
  rw [gradPsi_zstar_EX027 hte] at hT
  have hn := norm_sub_zstar_sq_EX027 z (besselRatio t)
  have hCR0 : 0 ≤ CR ^ 2 := sq_nonneg _
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hε2' : 0 ≤ ε ^ 2 := sq_nonneg _
  simp only [zero_apply, add_zero] at hT
  rw [hn] at hT
  have hkey : Dp ≤ 10 * X := by
    rw [hDp]
    linarith
  have h2 : ε ^ 2 * (10 * X) ≤ 10 * (CR ^ 2 * Y) := by nlinarith [h1]
  have h3 : CR ^ 2 * Y ≤ CR ^ 2 * (2 * E) := mul_le_mul_of_nonneg_left hYE hCR0
  have h4 : ε ^ 2 * E ≤ E := by nlinarith
  have h5 : ε ^ 2 * Dp ≤ ε ^ 2 * (10 * X) := mul_le_mul_of_nonneg_left hkey hε2'
  calc ε ^ 2 * G = ε ^ 2 * E + ε ^ 2 * Dp := by rw [hG]; ring
    _ ≤ E + 10 * (CR ^ 2 * (2 * E)) := by linarith
    _ = (1 + 20 * CR ^ 2) * E := by ring

theorem rate_bound_EX027 {s hc : ℝ} (hs : 0 < s) (hd : deriv besselRatio s = 1 / 4)
    (hhc : hc = 4 * besselRatio s - s) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (b : AbsoluteDrift (attractiveXY 4 (hc + ε))) :
    ENNReal.ofReal (a0 * Real.exp (-(2 * (hc + 5))) * ε ^ 2 /
        (1 + 20 * (max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc))) ^ 2)) ≤
      speciesRate (attractiveXY 4 (hc + ε)) b := by
  obtain ⟨hc0, hex, -, -, -⟩ := uniform_fold_residual_bound hs hd hhc
  obtain ⟨t, ⟨ht0, hte⟩, -⟩ := hex ε hε0 hε1
  set CR := max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc)) with hCR
  set ℓ0 : ℝ := a0 * Real.exp (-(2 * (hc + 5))) with hℓ0
  have hℓpos : 0 < ℓ0 := mul_pos a0_pos (Real.exp_pos _)
  have hden : 0 < 1 + 20 * CR ^ 2 := by positivity
  refine le_iInf fun F => ?_
  obtain ⟨hE0, hkey⟩ := gap_le_EX027 hs hd hhc hε0 hε1 ht0 hte F.1
  have hD := dissipation_bound_EX027 hc0 hε0 hε1 b F.1
  have hG : 0 < speciesGap (attractiveXY 4 (hc + ε)) F.1 := F.2
  unfold speciesQuotient
  have hne0 : (2 : ℝ≥0∞) * (speciesGap (attractiveXY 4 (hc + ε)) F.1 : ℝ≥0∞) ≠ 0 := by
    simp [hG.ne']
  have hnetop : (2 : ℝ≥0∞) * (speciesGap (attractiveXY 4 (hc + ε)) F.1 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnetop)]
  refine le_trans ?_ hD
  have hGnn : (0 : ℝ) ≤ (speciesGap (attractiveXY 4 (hc + ε)) F.1 : ℝ) := NNReal.coe_nonneg _
  rw [show (2 : ℝ≥0∞) * (speciesGap (attractiveXY 4 (hc + ε)) F.1 : ℝ≥0∞) =
      ENNReal.ofReal (2 * (speciesGap (attractiveXY 4 (hc + ε)) F.1 : ℝ)) by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal],
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hkey hℓpos.le]

end DGPS.Examples.AttractiveXYFoldEX027

namespace DGPS.Examples

open DGPS DGPS.Examples.AttractiveXYFoldEX027 DGPS.Examples.AttractiveXY DGPS.Models
open scoped ENNReal NNReal

/-- **EX027 (all-species fold lower bound).**  Let `s > 0` solve `g'(s) = 1/4` and
`h_c = 4 g(s) - s` (the fold parameter), `κ = 4`, `M0 = h_c + 5`,
`C_R = max {8, 16/h_c, (2+√2) M0/h_c}`, `a0 = 4π²`, and `0 < ε ≤ 1`, `h = h_c + ε`.  Write
`Ψ_h(z) = 2|z|² - log I_0(|h e₁ + 4 z|)` on `ℝ²`.  Then:

* (Hessian) `Ψ_h` is differentiable with differentiable derivative and `‖Hess Ψ_h(z)‖ ≤ 20`
  for every `h` and `z`;
* for every drift `b` and every finite positive-weight species family `F`, with
  `z = ρ̄(φ⃗)` the mean vector of the barycenter, `p_{h,z}` the frozen law and
  `E = ∑ θ_s H(ρ_s | p_{h,z})`:
  `E ≤ exp(2 M0) D / (2 a0)` (in `ℝ≥0∞`), and `|R_h(z)|² ≤ 2 E` for the residual
  `R_h(z) = z - T_h(z)`;
* for every positive root `t = 4 g(t) + h` and every family, the gap is
  `G = E + Ψ_h(z) - Ψ_h(z_*)` with `z_* = g(t) e₁`;
* hence `r_ms ≥ a0 exp(-2 M0) ε² / (1 + 20 C_R²)` (the infimum is over all positive-gap families
  and does not depend on the number of species or their weights). -/
theorem all_species_fold_lower_bound {s hc : ℝ} (hs : 0 < s)
    (hd : deriv besselRatio s = 1 / 4) (hhc : hc = 4 * besselRatio s - s) :
    (∀ (h : ℝ) (z : EuclideanSpace ℝ (Fin 2)),
      Differentiable ℝ (Psi_EX027 h) ∧ Differentiable ℝ (fderiv ℝ (Psi_EX027 h)) ∧
        ‖fderiv ℝ (fderiv ℝ (Psi_EX027 h)) z‖ ≤ 20) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∀ (b : AbsoluteDrift (attractiveXY 4 (hc + ε))) (F : SpeciesFamily 1),
        ENNReal.ofReal (E_EX027 (hc + ε) F) ≤
          ENNReal.ofReal (Real.exp (2 * (hc + 5)) / (2 * a0)) *
            speciesDissipation (attractiveXY 4 (hc + ε)) b F) ∧
      (∀ F : SpeciesFamily 1,
        R1_EX027 (hc + ε) (zbar_EX027 F) ^ 2 + R2_EX027 (hc + ε) (zbar_EX027 F) ^ 2 ≤
          2 * E_EX027 (hc + ε) F) ∧
      (∀ t : ℝ, 0 < t → t = 4 * besselRatio t + (hc + ε) → ∀ F : SpeciesFamily 1,
        (speciesGap (attractiveXY 4 (hc + ε)) F : ℝ) =
          E_EX027 (hc + ε) F +
            (Psi_EX027 (hc + ε) (zbar_EX027 F) -
              Psi_EX027 (hc + ε) (besselRatio t • e1_EX027))) ∧
      (∀ b : AbsoluteDrift (attractiveXY 4 (hc + ε)),
        ENNReal.ofReal (a0 * Real.exp (-(2 * (hc + 5))) * ε ^ 2 /
            (1 + 20 * (max 8 (max (16 / hc) ((2 + Real.sqrt 2) * (hc + 5) / hc))) ^ 2)) ≤
          speciesRate (attractiveXY 4 (hc + ε)) b) := by
  obtain ⟨hc0, -, -, -, -⟩ := uniform_fold_residual_bound hs hd hhc
  refine ⟨fun h z => ⟨differentiable_Psi_EX027 h, differentiable_fderiv_Psi_EX027 h, ?_⟩,
    fun ε hε0 hε1 => ⟨fun b F => ?_, fun F => residual_E_EX027 (hc + ε) F,
      fun t ht hte F => gap_identity'_EX027 (by linarith) ht hte F,
      fun b => rate_bound_EX027 hs hd hhc hε0 hε1 b⟩⟩
  · rw [fderiv_fderiv_Psi_EX027]
    exact norm_hessPsi_le_EX027 h z
  · have hD := dissipation_bound_EX027 hc0 hε0 hε1 b F
    have hR := residual_E_EX027 (hc + ε) F
    have hR1 := sq_nonneg (R1_EX027 (hc + ε) (zbar_EX027 F))
    have hR2 := sq_nonneg (R2_EX027 (hc + ε) (zbar_EX027 F))
    have hE0 : 0 ≤ E_EX027 (hc + ε) F := by linarith
    have hexp : Real.exp (2 * (hc + 5)) * Real.exp (-(2 * (hc + 5))) = 1 := by
      rw [← Real.exp_add]; simp
    have ha0 : a0 ≠ 0 := a0_pos.ne'
    have hid : Real.exp (2 * (hc + 5)) / (2 * a0) *
        (2 * (a0 * Real.exp (-(2 * (hc + 5)))) * E_EX027 (hc + ε) F) = E_EX027 (hc + ε) F := by
      field_simp
      rw [hexp, one_mul]
    calc ENNReal.ofReal (E_EX027 (hc + ε) F)
        = ENNReal.ofReal (Real.exp (2 * (hc + 5)) / (2 * a0)) *
            ENNReal.ofReal (2 * (a0 * Real.exp (-(2 * (hc + 5)))) * E_EX027 (hc + ε) F) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le (by linarith [a0_pos])), hid]
      _ ≤ _ := mul_le_mul' le_rfl hD

end DGPS.Examples
