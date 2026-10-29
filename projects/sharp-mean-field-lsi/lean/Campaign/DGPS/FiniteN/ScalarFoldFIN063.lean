import DGPS.FiniteN.ScalarFoldFIN061
import DGPS.FiniteN.Tools.GaussianCoupling

/-!
# FIN063: fold empirical core lower bound by conditional variance

For the one-dimensional Hubbard model with `k = 1`, cosine feature `φ(θ) = cos θ` on the
angular circle, reference law `angHaar`, and diagonal precision `D = κ` at fold field
`h_c = scalarFoldField κ`, the empirical posterior center `z_N = posteriorCenter ... x 0` is
conditionally (given the latent `w`) an average of `N` i.i.d. `cos` values with mean
`κ · besselRatio w` and variance `≤ κ²/N`.  On the latent box `|w - t_*| ≤ d_N/(2κ)` the
conditional mean is within `d_N/2` of `t_*`, so conditional Chebyshev gives core probability at
least `1/2`; integrating over the box and using FIN061 gives the lower bound
`c N^{1/6} e^{-NΔ}`.

The main theorem is `DGPS.FiniteN.fold_empirical_core_lower_by_conditional_variance`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open DGPS.Circle.BesselMoments DGPS.Circle.AngularNormalization
open DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling

namespace DGPS.FiniteN.ScalarFoldFIN063

theorem besselI_zero_eq_FIN063 (t : ℝ) :
    besselI 0 t = ∫ θ, Real.exp (t * angCos θ) ∂angHaar := by
  simp [besselI, angMode_zero]

theorem besselI_one_eq_FIN063 (t : ℝ) :
    besselI 1 t = ∫ θ, Real.exp (t * angCos θ) * angCos θ ∂angHaar := rfl

theorem integrable_exp_FIN063 (t : ℝ) :
    Integrable (fun θ : AngCircle => Real.exp (t * angCos θ)) angHaar := by
  have := integrable_exp_mul t (fun _ => (1 : ℝ)) continuous_const (fun _ => by simp)
  simpa using this

theorem besselI_zero_pos_FIN063 (t : ℝ) : 0 < besselI 0 t := besselI_zero_pos t

theorem abs_besselI_one_le_FIN063 (t : ℝ) : |besselI 1 t| ≤ besselI 0 t := by
  rw [besselI_one_eq_FIN063, besselI_zero_eq_FIN063]
  have hc : Continuous angCos := continuous_angMode 1
  have hI : Integrable (fun θ : AngCircle => Real.exp (t * angCos θ) * angCos θ) angHaar :=
    integrable_exp_mul t angCos hc (abs_angMode_le 1)
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono hI.abs (integrable_exp_FIN063 t) fun θ => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have := abs_angMode_le 1 θ
  have h1 : |angCos θ| ≤ 1 := this
  exact mul_le_of_le_one_right (Real.exp_pos _).le h1

theorem besselRatio_abs_le_one_FIN063 (t : ℝ) : |besselRatio t| ≤ 1 := by
  unfold besselRatio
  rw [abs_div, abs_of_pos (besselI_zero_pos t), div_le_one (besselI_zero_pos t)]
  exact abs_besselI_one_le_FIN063 t

theorem besselA_bounds_FIN063 (t : ℝ) :
    0 ≤ (∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar) / besselI 0 t ∧
      (∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar) / besselI 0 t ≤ 1 := by
  have hc : Continuous angCos := continuous_angMode 1
  have hcc : ∀ θ : AngCircle, |angCos θ * angCos θ| ≤ 1 := fun θ => by
    have h := abs_angMode_le 1 θ
    rw [abs_mul]
    nlinarith [abs_nonneg (angCos θ)]
  have hfun : (fun θ : AngCircle => angCos θ * Real.exp (t * angCos θ) * angCos θ) =
      fun θ => Real.exp (t * angCos θ) * (angCos θ * angCos θ) := by
    funext θ; ring
  have hI : Integrable (fun θ : AngCircle => Real.exp (t * angCos θ) * (angCos θ * angCos θ))
      angHaar :=
    integrable_exp_mul t (fun θ => angCos θ * angCos θ) (hc.mul hc) hcc
  have hA0 : 0 ≤ ∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar := by
    rw [hfun]
    refine integral_nonneg fun θ => ?_
    exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)
  have hA1 : ∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar ≤ besselI 0 t := by
    rw [hfun, besselI_zero_eq_FIN063]
    refine integral_mono hI (integrable_exp_FIN063 t) fun θ => ?_
    have h := hcc θ
    exact mul_le_of_le_one_right (Real.exp_pos _).le (le_trans (le_abs_self _) h)
  have hI0 := besselI_zero_pos_FIN063 t
  exact ⟨div_nonneg hA0 hI0.le, (div_le_one hI0).2 hA1⟩

theorem deriv_besselRatio_bound_FIN063 (t : ℝ) : |deriv besselRatio t| ≤ 1 := by
  rw [(hasDerivAt_besselRatio t).deriv]
  obtain ⟨hA0, hA1⟩ := besselA_bounds_FIN063 t
  have hI0 := besselI_zero_pos_FIN063 t
  have hR := besselRatio_abs_le_one_FIN063 t
  have hsq : (besselI 1 t / besselI 0 t) ^ 2 ≤ 1 := by
    have : |besselI 1 t / besselI 0 t| ≤ 1 := by
      unfold besselRatio at hR; exact hR
    nlinarith [abs_nonneg (besselI 1 t / besselI 0 t), sq_abs (besselI 1 t / besselI 0 t)]
  have hsq0 : 0 ≤ (besselI 1 t / besselI 0 t) ^ 2 := sq_nonneg _
  have key : ∀ A I0 I1 : ℝ, I0 ≠ 0 → (A * I0 - I1 * I1) / I0 ^ 2 = A / I0 - (I1 / I0) ^ 2 := by
    intro A I0 I1 h
    field_simp
  rw [key _ _ _ hI0.ne']
  rw [abs_le]
  constructor <;> linarith [hA0, hA1, hsq, hsq0]

theorem besselRatio_lipschitz_FIN063 (a b : ℝ) : |besselRatio a - besselRatio b| ≤ |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := besselRatio) (s := (univ : Set ℝ))
    (C := 1) (fun x _ => (hasDerivAt_besselRatio x).differentiableAt)
    (fun x _ => by
      rw [Real.norm_eq_abs]
      exact deriv_besselRatio_bound_FIN063 x)
    convex_univ (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h


/-! ### Hubbard `k = 1` specialization -/

/-- The cosine feature `θ ↦ (cos θ)` in dimension one. -/
noncomputable def cosVec_FIN063 (θ : AngCircle) : Fin 1 → ℝ := fun _ => angCos θ

/-- The diagonal precision `D = κ` in dimension one. -/
noncomputable def D_FIN063 (κ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ => κ

theorem abs_angCos_le_FIN063 (θ : AngCircle) : |angCos θ| ≤ 1 := abs_angMode_le 1 θ

theorem norm_cosVec_le_FIN063 (θ : AngCircle) : ‖cosVec_FIN063 θ‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  exact abs_angCos_le_FIN063 θ

theorem measurable_cosVec_FIN063 : Measurable cosVec_FIN063 :=
  measurable_pi_iff.mpr fun _ => (continuous_angMode 1).measurable

theorem hyp_FIN063 : HubbardHyp angHaar (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 where
  m_ne_zero := IsProbabilityMeasure.ne_zero angHaar
  U_meas := measurable_const
  U_lower := ⟨0, fun _ => le_rfl⟩
  φ_meas := measurable_cosVec_FIN063
  φ_bound := ⟨1, norm_cosVec_le_FIN063⟩

theorem posDef_D_FIN063 {κ : ℝ} (hκ : 0 < κ) : (D_FIN063 κ).PosDef := by
  unfold D_FIN063
  rw [Matrix.posDef_diagonal_iff]
  intro _
  exact hκ

theorem auxPartition_FIN063 (w : Fin 1 → ℝ) :
    auxPartition (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w = besselI 0 (w 0) := by
  rw [besselI_zero_eq_FIN063]
  unfold auxPartition expTerm
  congr 1
  funext θ
  simp [cosVec_FIN063, dotProduct]

theorem siteMean_FIN063 (w : Fin 1 → ℝ) :
    siteMean (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w 0 = besselRatio (w 0) := by
  simp only [siteMean]
  rw [integral_siteLaw hyp_FIN063 w, auxPartition_FIN063]
  unfold besselRatio
  rw [besselI_one_eq_FIN063, div_eq_inv_mul]
  congr 1
  unfold expTerm
  congr 1
  funext θ
  simp [cosVec_FIN063, dotProduct]

theorem integral_fieldSum0_FIN063 (N : ℕ+) (w : Fin 1 → ℝ) :
    ∫ x : Fin N → AngCircle, fieldSum cosVec_FIN063 x 0
      ∂(Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w)
      = N * besselRatio (w 0) := by
  rw [integral_fieldSum hyp_FIN063 N w 0, siteMean_FIN063]

theorem abs_fieldSum0_le_FIN063 (N : ℕ+) (x : Fin N → AngCircle) :
    |fieldSum cosVec_FIN063 x 0| ≤ N := by
  simp only [fieldSum, Finset.sum_apply, cosVec_FIN063]
  calc |∑ i, angCos (x i)| ≤ ∑ i, |angCos (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => abs_angCos_le_FIN063 _
    _ = N := by simp

theorem memLp_fieldSum0_FIN063 (N : ℕ+) (w : Fin 1 → ℝ) :
    MemLp (fun x : Fin N → AngCircle => fieldSum cosVec_FIN063 x 0) 2
      (Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w) := by
  have := isProbabilityMeasure_siteLaw hyp_FIN063 (m := angHaar) w
  have hm : Measurable (fun x : Fin N → AngCircle => fieldSum cosVec_FIN063 x 0) :=
    (measurable_pi_apply 0).comp (measurable_fieldSum (N := N) hyp_FIN063)
  exact MemLp.of_bound hm.aestronglyMeasurable (N : ℝ) (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    exact abs_fieldSum0_le_FIN063 N x)

theorem variance_fieldSum0_FIN063 (N : ℕ+) (w : Fin 1 → ℝ) :
    variance (fun x : Fin N → AngCircle => fieldSum cosVec_FIN063 x 0)
      (Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w)
      ≤ N := by
  have := isProbabilityMeasure_siteLaw hyp_FIN063 (m := angHaar) w
  have hb := variance_bound hyp_FIN063 N w (fun _ => (1 : ℝ)) (L := 1) norm_cosVec_le_FIN063
  have hv : ∀ x : Fin N → AngCircle,
      (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ fieldSum cosVec_FIN063 x = fieldSum cosVec_FIN063 x 0 := by
    intro x
    simp [dotProduct]
  simp only [hv] at hb
  have hmeas := (memLp_fieldSum0_FIN063 N w).aestronglyMeasurable.aemeasurable
  rw [variance_eq_integral hmeas]
  refine le_trans (le_of_eq ?_) (hb.trans (le_of_eq ?_))
  · rfl
  · simp [dotProduct]

theorem posteriorCenter_FIN063 (κ hc : ℝ) (N : ℕ+) (x : Fin N → AngCircle) :
    posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0 =
      ((N : ℝ)⁻¹ * κ) * fieldSum cosVec_FIN063 x 0 + hc := by
  simp only [posteriorCenter, Pi.add_apply, Pi.smul_apply, smul_eq_mul, D_FIN063,
    Matrix.mulVec_diagonal]
  ring

theorem integral_center_FIN063 (κ hc : ℝ) (N : ℕ+) (w : Fin 1 → ℝ) :
    ∫ x : Fin N → AngCircle, ((N : ℝ)⁻¹ * κ) * fieldSum cosVec_FIN063 x 0 + hc
      ∂(Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w)
      = hc + κ * besselRatio (w 0) := by
  have := isProbabilityMeasure_siteLaw hyp_FIN063 (m := angHaar) w
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [integral_add ((integrable_fieldSum hyp_FIN063 N w 0).const_mul _) (integrable_const hc),
    integral_const_mul, integral_fieldSum0_FIN063, integral_const]
  simp only [probReal_univ, one_smul]
  field_simp
  ring

theorem ratio_FIN063 {κ N : ℝ} (hκ : 0 < κ) (hN : (8 * κ ^ 2) ^ 3 ≤ N) :
    (N⁻¹ * κ) ^ 2 * N / ((N ^ (-(1 / 3) : ℝ)) / 2) ^ 2 ≤ 1 / 2 := by
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ N = s ^ 3 :=
    ⟨N ^ (1 / 3 : ℝ), Real.rpow_pos_of_pos hN0 _, by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num⟩
  have hneg : (s ^ 3) ^ (-(1 / 3) : ℝ) = s⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]; norm_num [Real.rpow_neg_one]
  have hs8 : 8 * κ ^ 2 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 3 < (8 * κ ^ 2) ^ 3 := pow_lt_pow_left₀ hlt hs0.le (by norm_num)
    linarith
  rw [hneg]
  have hsne : s ≠ 0 := hs0.ne'
  have e : ((s ^ 3)⁻¹ * κ) ^ 2 * s ^ 3 / (s⁻¹ / 2) ^ 2 = 4 * κ ^ 2 / s := by
    field_simp
    ring
  rw [e, div_le_iff₀ hs0]
  linarith

theorem prob_near_FIN063 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : MemLp Z 2 P) {t ε : ℝ} (hε : 0 < ε)
    (hμ : |∫ ω, Z ω ∂P - t| ≤ ε / 2) (hvar : variance Z P / (ε / 2) ^ 2 ≤ 1 / 2) :
    ENNReal.ofReal (1 / 2) ≤ P {ω | |Z ω - t| ≤ ε} := by
  have hC : MeasurableSet {ω | |Z ω - t| ≤ ε} :=
    measurableSet_le (continuous_abs.measurable.comp (hZm.sub measurable_const)) measurable_const
  have hsub : {ω | |Z ω - t| ≤ ε}ᶜ ⊆ {ω | ε / 2 ≤ |Z ω - ∫ ω', Z ω' ∂P|} := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
    simp only [mem_ofPred_eq]
    have h1 := abs_sub_le (Z ω) (∫ ω', Z ω' ∂P) t
    have h2 := abs_sub_le_iff.mp hμ
    linarith [h1, h2.1, h2.2]
  have hcheb := meas_ge_le_variance_div_sq hZ (c := ε / 2) (by positivity)
  have h2 : P {ω | |Z ω - t| ≤ ε}ᶜ ≤ ENNReal.ofReal (1 / 2) :=
    (measure_mono hsub).trans (hcheb.trans (ENNReal.ofReal_le_ofReal hvar))
  have h3 := prob_add_prob_compl (μ := P) hC
  have h4 : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  refine ENNReal.le_of_add_le_add_right (measure_ne_top P {ω | |Z ω - t| ≤ ε}ᶜ) ?_
  calc ENNReal.ofReal (1 / 2) + P {ω | |Z ω - t| ≤ ε}ᶜ
      ≤ ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) := add_le_add le_rfl h2
    _ = 1 := h4
    _ = P {ω | |Z ω - t| ≤ ε} + P {ω | |Z ω - t| ≤ ε}ᶜ := h3.symm

theorem core_prob_FIN063 {κ hc t : ℝ} (hκ : 0 < κ) (hfix : hc + κ * besselRatio t = t)
    (N : ℕ+) (hN : (8 * κ ^ 2) ^ 3 ≤ (N : ℝ)) (w : Fin 1 → ℝ)
    (hw : |w 0 - t| ≤ (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ENNReal.ofReal (1 / 2) ≤
      (Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w)
        {x | |posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0 - t|
          ≤ (N : ℝ) ^ (-(1 / 3) : ℝ)} := by
  have := isProbabilityMeasure_siteLaw hyp_FIN063 (m := angHaar) w
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hdpos : (0 : ℝ) < (N : ℝ) ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hZfun : (fun x : Fin N → AngCircle =>
      posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0) =
      fun x => ((N : ℝ)⁻¹ * κ) * fieldSum cosVec_FIN063 x 0 + hc :=
    funext (posteriorCenter_FIN063 κ hc N)
  have hZm : Measurable (fun x : Fin N → AngCircle =>
      posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0) :=
    (measurable_pi_apply 0).comp (measurable_posteriorCenter hyp_FIN063 _ _ N)
  have hX := (memLp_fieldSum0_FIN063 N w).const_mul ((N : ℝ)⁻¹ * κ)
  have hZ : MemLp (fun x : Fin N → AngCircle =>
      posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0) 2
      (Measure.pi fun _ : Fin N => siteLaw (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w) := by
    rw [hZfun]
    exact hX.add (memLp_const hc)
  refine prob_near_FIN063 _ hZm hZ hdpos ?_ ?_
  · rw [hZfun, integral_center_FIN063]
    have e : hc + κ * besselRatio (w 0) - t = κ * (besselRatio (w 0) - besselRatio t) := by
      linear_combination hfix
    rw [e, abs_mul, abs_of_pos hκ]
    have hL := besselRatio_lipschitz_FIN063 (w 0) t
    calc κ * |besselRatio (w 0) - besselRatio t| ≤ κ * |w 0 - t| :=
          mul_le_mul_of_nonneg_left hL hκ.le
      _ ≤ κ * ((1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ)) := mul_le_mul_of_nonneg_left hw hκ.le
      _ = (N : ℝ) ^ (-(1 / 3) : ℝ) / 2 := by field_simp
  · rw [hZfun, variance_add_const hX.aestronglyMeasurable hc, variance_const_mul]
    refine le_trans ?_ (ratio_FIN063 hκ hN)
    gcongr
    exact variance_fieldSum0_FIN063 N w

/-! ### Auxiliary potential, transfer to FIN061, and the joint lower bound -/

theorem fixed_point_FIN063 (κ : ℝ) :
    scalarFoldField κ + κ * besselRatio (-scalarFoldPoint κ) = -scalarFoldPoint κ := by
  unfold scalarFoldField
  rw [besselRatio_neg]
  ring

theorem auxPotential_FIN063 {κ hc : ℝ} (hκ : 0 < κ) (w : Fin 1 → ℝ) :
    auxPotential (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 (D_FIN063 κ) (fun _ => hc) angHaar w
      = scalarPsi κ hc (w 0) := by
  have hinv : (D_FIN063 κ)⁻¹ = Matrix.diagonal fun _ => κ⁻¹ := by
    unfold D_FIN063
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp [hκ.ne']
  unfold auxPotential scalarPsi quadForm
  rw [auxPartition_FIN063, hinv]
  simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_one, Pi.sub_apply]
  ring

theorem measurable_center_FIN063 (κ hc : ℝ) (N : ℕ+) :
    Measurable (fun x : Fin N → AngCircle =>
      posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0) :=
  (measurable_pi_apply 0).comp (measurable_posteriorCenter hyp_FIN063 _ _ N)

theorem auxLaw_preimage_FIN063 {κ hc : ℝ} (hκ : 0 < κ) (N : ℕ+) {S : Set ℝ}
    (hS : MeasurableSet S) :
    auxLaw (D_FIN063 κ) (fun _ => hc) (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar N
        ((fun w : Fin 1 → ℝ => w 0) ⁻¹' S) =
      foldLatentEtaFIN061 (scalarPsi κ hc) (N : ℝ) S := by
  have hψm : Measurable (scalarPsi κ hc) :=
    (ScalarFoldFIN057.scalarPsi_contDiff_FIN057 κ hc).continuous.measurable
  have hgm : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-((N : ℝ) * scalarPsi κ hc t)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_const.mul hψm).neg))
  have hmp : MeasurePreserving (fun w : Fin 1 → ℝ => w 0) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  have hemb : MeasurableEmbedding (fun w : Fin 1 → ℝ => w 0) :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
  have hdens : (fun w : Fin 1 → ℝ => ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 (D_FIN063 κ) (fun _ => hc)
        angHaar w))) =
      fun w => ENNReal.ofReal (Real.exp (-((N : ℝ) * scalarPsi κ hc (w 0)))) := by
    funext w
    rw [auxPotential_FIN063 hκ, neg_mul]
  have hpre : MeasurableSet ((fun w : Fin 1 → ℝ => w 0) ⁻¹' S) :=
    (measurable_pi_apply (0 : Fin 1)) hS
  have hmass : auxMass (D_FIN063 κ) (fun _ => hc) (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063
      angHaar N = ∫⁻ t, ENNReal.ofReal (Real.exp (-((N : ℝ) * scalarPsi κ hc t))) := by
    unfold auxMass
    rw [hdens]
    exact hmp.lintegral_comp hgm
  unfold auxLaw foldLatentEtaFIN061
  rw [hmass, Measure.smul_apply, Measure.smul_apply, withDensity_apply _ hpre,
    withDensity_apply _ hS, hdens, smul_eq_mul, smul_eq_mul]
  congr 1
  exact hmp.setLIntegral_comp_preimage_emb hemb
    (fun t : ℝ => ENNReal.ofReal (Real.exp (-((N : ℝ) * scalarPsi κ hc t)))) S

theorem particle_ne_top_FIN063 {κ hc : ℝ} (hκ : 0 < κ) (N : ℕ+) {C : Set (Fin N → AngCircle)}
    (hC : MeasurableSet C) :
    hubbardParticleLaw (D_FIN063 κ) (fun _ => hc) (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063
      angHaar N C ≠ ⊤ := by
  have := isProbabilityMeasure_hubbardJoint hyp_FIN063 (posDef_D_FIN063 hκ) (fun _ => hc) N
  rw [← hubbardJoint_map_snd hyp_FIN063 (posDef_D_FIN063 hκ) (fun _ => hc) N,
    Measure.map_apply measurable_snd hC]
  exact measure_ne_top _ _

theorem particle_eq_FIN063 {κ hc : ℝ} (hκ : 0 < κ) (N : ℕ+) {C : Set (Fin N → AngCircle)}
    (hC : MeasurableSet C) :
    hubbardParticleLaw (D_FIN063 κ) (fun _ => hc) (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063
        angHaar N C =
      ∫⁻ w, (Measure.pi fun _ : Fin N =>
          siteLaw (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063 angHaar w) C
        ∂(auxLaw (D_FIN063 κ) (fun _ => hc) (fun _ : AngCircle => (0 : ℝ)) cosVec_FIN063
            angHaar N) := by
  rw [← hubbardJoint_map_snd hyp_FIN063 (posDef_D_FIN063 hκ) (fun _ => hc) N,
    Measure.map_apply measurable_snd hC,
    hubbardJoint_apply hyp_FIN063 (posDef_D_FIN063 hκ) (fun _ => hc) N (measurable_snd hC)]
  rfl

theorem particle_lower_FIN063 {κ hc t : ℝ} (hκ : 0 < κ) (hfix : hc + κ * besselRatio t = t)
    (N : ℕ+) (hN : (8 * κ ^ 2) ^ 3 ≤ (N : ℝ)) :
    ENNReal.ofReal (1 / 2) * auxLaw (D_FIN063 κ) (fun _ => hc) (fun _ : AngCircle => (0 : ℝ))
        cosVec_FIN063 angHaar N
        ((fun w : Fin 1 → ℝ => w 0) ⁻¹'
          Icc (t - (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))
            (t + (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))) ≤
      hubbardParticleLaw (D_FIN063 κ) (fun _ => hc) (fun _ : AngCircle => (0 : ℝ))
        cosVec_FIN063 angHaar N
        {x | |posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0 - t|
          ≤ (N : ℝ) ^ (-(1 / 3) : ℝ)} := by
  have hCm : MeasurableSet {x : Fin N → AngCircle |
      |posteriorCenter (D_FIN063 κ) (fun _ => hc) cosVec_FIN063 N x 0 - t|
        ≤ (N : ℝ) ^ (-(1 / 3) : ℝ)} :=
    measurableSet_le (continuous_abs.measurable.comp
      ((measurable_center_FIN063 κ hc N).sub measurable_const)) measurable_const
  rw [particle_eq_FIN063 hκ N hCm]
  have hbox : MeasurableSet ((fun w : Fin 1 → ℝ => w 0) ⁻¹'
      Icc (t - (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))
        (t + (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))) :=
    (measurable_pi_apply (0 : Fin 1)) measurableSet_Icc
  rw [← lintegral_indicator_const hbox]
  refine lintegral_mono fun w => ?_
  by_cases hw : w ∈ ((fun w : Fin 1 → ℝ => w 0) ⁻¹'
      Icc (t - (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))
        (t + (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ)))
  · rw [Set.indicator_of_mem hw]
    have hw' : w 0 ∈ Icc (t - (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))
        (t + (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ)) := hw
    exact core_prob_FIN063 hκ hfix N hN w
      (abs_le.2 ⟨by linarith [(Set.mem_Icc.1 hw').1], by linarith [(Set.mem_Icc.1 hw').2]⟩)
  · rw [Set.indicator_of_notMem hw]
    exact zero_le

end DGPS.FiniteN.ScalarFoldFIN063

namespace DGPS.FiniteN

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling

/-- FIN063: for `κ > 2` and the fold field `h_c = scalarFoldField κ`, the Hubbard particle law
(`k = 1`, cosine feature, reference `angHaar`, precision `κ`) gives the core set
`{|z_N - t_*| ≤ N^{-1/3}}` mass at least `c N^{1/6} e^{-NΔ}` for all large `N`, where `Δ` is the
fold gap from FIN061. -/
theorem fold_empirical_core_lower_by_conditional_variance (κ : ℝ) (hκ : 2 < κ) :
    let hc := scalarFoldField κ
    let ψ := scalarPsi κ hc
    let tStar := -scalarFoldPoint κ
    ∃ tPlus Δ : ℝ, 0 < tPlus ∧ (∀ t : ℝ, t ≠ tPlus → ψ tPlus < ψ t) ∧
      Δ = ψ tStar - ψ tPlus ∧ 0 < Δ ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℕ+, N0 ≤ (N : ℝ) →
        c * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ)) ≤
          (hubbardParticleLaw (ScalarFoldFIN063.D_FIN063 κ) (fun _ => hc)
            (fun _ : AngCircle => (0 : ℝ)) ScalarFoldFIN063.cosVec_FIN063 angHaar N
            {x | |posteriorCenter (ScalarFoldFIN063.D_FIN063 κ) (fun _ => hc)
                ScalarFoldFIN063.cosVec_FIN063 N x 0 - tStar|
              ≤ (N : ℝ) ^ (-(1 / 3) : ℝ)}).toReal := by
  intro hc ψ tStar
  have hκ0 : 0 < κ := by linarith
  obtain ⟨tp, Δ, htp0, hmin, hΔ, hΔpos, hK⟩ := fold_latent_rare_box_mass κ hκ
  refine ⟨tp, Δ, htp0, hmin, hΔ, hΔpos, ?_⟩
  obtain ⟨c, hc0, C, hC0, N0, hN0, hbd⟩ := hK (1 / (2 * κ)) (one_div_pos.2 (by linarith))
  refine ⟨c / 2, half_pos hc0, max N0 ((8 * κ ^ 2) ^ 3), le_trans hN0 (le_max_left _ _),
    fun N hN => ?_⟩
  have hN1 : N0 ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hN2 : (8 * κ ^ 2) ^ 3 ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hlow : c * (N : ℝ) ^ (1 / 6 : ℝ) * Real.exp (-((N : ℝ) * Δ)) ≤
      (foldLatentEtaFIN061 ψ (N : ℝ) (Icc (tStar - (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))
        (tStar + (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ)))).toReal :=
    (hbd (N : ℝ) hN1).1
  have hA : auxLaw (ScalarFoldFIN063.D_FIN063 κ) (fun _ => hc)
        (fun _ : AngCircle => (0 : ℝ)) ScalarFoldFIN063.cosVec_FIN063 angHaar N
        ((fun w : Fin 1 → ℝ => w 0) ⁻¹'
          Icc (tStar - (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))
            (tStar + (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))) =
      foldLatentEtaFIN061 ψ (N : ℝ) (Icc (tStar - (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))
        (tStar + (1 / (2 * κ)) * (N : ℝ) ^ (-(1 / 3) : ℝ))) :=
    ScalarFoldFIN063.auxLaw_preimage_FIN063 hκ0 N measurableSet_Icc
  have hlb := ScalarFoldFIN063.particle_lower_FIN063 (hc := hc) (t := tStar) hκ0
    (ScalarFoldFIN063.fixed_point_FIN063 κ) N hN2
  rw [hA] at hlb
  have hCm : MeasurableSet {x : Fin N → AngCircle |
      |posteriorCenter (ScalarFoldFIN063.D_FIN063 κ) (fun _ => hc)
          ScalarFoldFIN063.cosVec_FIN063 N x 0 - tStar| ≤ (N : ℝ) ^ (-(1 / 3) : ℝ)} :=
    measurableSet_le (continuous_abs.measurable.comp
      ((ScalarFoldFIN063.measurable_center_FIN063 κ hc N).sub measurable_const)) measurable_const
  have hmono := ENNReal.toReal_mono (ScalarFoldFIN063.particle_ne_top_FIN063 hκ0 N hCm) hlb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at hmono
  linarith

end DGPS.FiniteN
