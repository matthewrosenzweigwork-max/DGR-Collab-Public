import DGPS.FiniteN.ScalarFoldFIN060G
import DGPS.Particle.DiagonalForce
import DGPS.FiniteN.Tools.PositiveRate

/-!
# FIN060 (part H): conditional Poincare inequality for the scalar cosine model

Single-site Poincare inequality on `Torus 1` for smooth periodic tests, Holley-Stroock comparison
with the site law `q_w ∝ exp (w cos) dm`, and tensorization over the `N` sites.  This yields the
`hcond` hypothesis of the FIN013 transfer with a constant `exp (2 |w|) / (4 π²)`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.AuxiliaryTransfer
  DGPS.FiniteN.Tools.BoundedComparison DGPS.FiniteN.Tools.ConditionalMeanDerivative
  DGPS.FiniteN.Tools.AuxiliaryTransferTorus DGPS.FiniteN.Tools.GaussianCoupling

/-- Site carre du champ on `Torus 1`. -/
noncomputable def thetaFIN060 (f : Torus 1 → ℝ) (t : Torus 1) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ j : Fin 1, coordPartial j f t ^ 2)

theorem memLp_two_smooth_FIN060 {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) :
    MemLp f 2 (haar 1) := hf.memLp_top.mono_exponent le_top

theorem site_poincare_haar_FIN060 :
    PoincareAt (haar 1) IsSmoothPeriodic thetaFIN060 (4 * Real.pi ^ 2)⁻¹ := by
  intro f hf
  have hw := hf.isWeakGradient
  have hP := DGPS.FiniteN.PositiveRate.torus_poincare hw
  have hmem := memLp_two_smooth_FIN060 hf
  have hint : Integrable (fun y => ‖smoothGrad f y‖ ^ 2) (haar 1) := by
    have : (fun y => ‖smoothGrad f y‖ ^ 2) = fun y => ∑ j : Fin 1, coordPartial j f y ^ 2 := by
      funext y; rw [tangent_norm_sq]; rfl
    rw [this]
    refine integrable_finsetSum _ fun j _ => ?_
    exact ((hf.memLp_top_coordPartial j).mono_exponent le_top).integrable_sq
  have hE : ∫⁻ y, thetaFIN060 f y ∂haar 1 = ENNReal.ofReal (∫ y, ‖smoothGrad f y‖ ^ 2 ∂haar 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    unfold thetaFIN060
    rw [tangent_norm_sq]; rfl
  rw [← hmem.ofReal_variance_eq, hE, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hpi]
  linarith

theorem lintegral_exp_gauss_FIN060 (t : ℝ) :
    ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (t * y)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (t ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal t)
    (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
  have := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf] at this
  rw [this]
  simp

theorem lintegral_exp_abs_affine_FIN060 (c a : ℝ) :
    ∫⁻ ξ : Fin 1 → ℝ, ENNReal.ofReal (Real.exp (2 * |c + a * ξ 0|)) ∂(stdGaussianPi 1) ≤
      ENNReal.ofReal (2 * Real.exp (2 * |c| + 2 * a ^ 2)) := by
  have hmp : MeasurePreserving (fun ξ : Fin 1 → ℝ => ξ 0) (stdGaussianPi 1) (gaussianReal 0 1) :=
    measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0
  have hpt : ∀ y : ℝ, Real.exp (2 * |c + a * y|) ≤
      Real.exp (2 * |c|) * (Real.exp ((2 * a) * y) + Real.exp ((-(2 * a)) * y)) := by
    intro y
    have h1 : 2 * |c + a * y| ≤ 2 * |c| + 2 * |a * y| := by
      have := abs_add_le c (a * y); linarith
    have h2 : Real.exp (2 * |a * y|) ≤ Real.exp ((2 * a) * y) + Real.exp ((-(2 * a)) * y) := by
      rcases abs_cases (a * y) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
        have : 2 * (a * y) = (2 * a) * y := by ring
        rw [this]; linarith [Real.exp_pos ((-(2 * a)) * y)]
      · rw [h]
        have : 2 * -(a * y) = (-(2 * a)) * y := by ring
        rw [this]; linarith [Real.exp_pos ((2 * a) * y)]
    calc Real.exp (2 * |c + a * y|) ≤ Real.exp (2 * |c| + 2 * |a * y|) := Real.exp_le_exp.2 h1
      _ = Real.exp (2 * |c|) * Real.exp (2 * |a * y|) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hmeas : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (2 * |c + a * y|)) := by
    fun_prop
  refine (le_of_eq (hmp.lintegral_comp hmeas)).trans ?_
  calc ∫⁻ y, ENNReal.ofReal (Real.exp (2 * |c + a * y|)) ∂(gaussianReal 0 1)
      ≤ ∫⁻ y, (ENNReal.ofReal (Real.exp (2 * |c|) * Real.exp ((2 * a) * y)) +
          ENNReal.ofReal (Real.exp (2 * |c|) * Real.exp ((-(2 * a)) * y))) ∂(gaussianReal 0 1) := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc _ ≤ _ := hpt y
          _ = _ := by ring
    _ = ENNReal.ofReal (Real.exp (2 * |c|)) * ∫⁻ y, ENNReal.ofReal (Real.exp ((2 * a) * y)) ∂(gaussianReal 0 1)
        + ENNReal.ofReal (Real.exp (2 * |c|)) * ∫⁻ y, ENNReal.ofReal (Real.exp ((-(2 * a)) * y)) ∂(gaussianReal 0 1) := by
        rw [lintegral_add_left]
        · simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop)]
        · simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          exact (by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (2 * |c|)) * ENNReal.ofReal (Real.exp ((2 * a) * y)))
    _ = ENNReal.ofReal (2 * Real.exp (2 * |c| + 2 * a ^ 2)) := by
        rw [lintegral_exp_gauss_FIN060, lintegral_exp_gauss_FIN060,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
        congr 1
        rw [← Real.exp_add, ← Real.exp_add]
        have e1 : (2 * a) ^ 2 / 2 = 2 * a ^ 2 := by ring
        have e2 : (-(2 * a)) ^ 2 / 2 = 2 * a ^ 2 := by ring
        rw [e1, e2]; ring


theorem expTerm_FIN060 (w : Fin 1 → ℝ) (x : Torus 1) :
    expTerm uSFIN060 phiSFIN060 w x = Real.exp (w 0 * scalarCos x) := by
  simp [expTerm, uSFIN060, phiSFIN060, dotProduct]

theorem abs_mul_scalarCos_le_FIN060 (w : Fin 1 → ℝ) (x : Torus 1) : |w 0 * scalarCos x| ≤ |w 0| := by
  rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (scalarCos_bound x)

theorem siteDensity_osc_FIN060 (w : Fin 1 → ℝ) (x y : Torus 1) :
    siteDensity uSFIN060 phiSFIN060 (haar 1) w x ≤
      Real.exp (2 * |w 0|) * siteDensity uSFIN060 phiSFIN060 (haar 1) w y := by
  have hz := auxPartition_pos hubbardHyp_FIN060 (m := haar 1) w
  unfold siteDensity
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ hz.le
  rw [expTerm_FIN060, expTerm_FIN060]
  have h1 := (le_abs_self _).trans (abs_mul_scalarCos_le_FIN060 w x)
  have h2 := (neg_le_abs _).trans (abs_mul_scalarCos_le_FIN060 w y)
  calc Real.exp (w 0 * scalarCos x) ≤ Real.exp (2 * |w 0| + w 0 * scalarCos y) :=
        Real.exp_le_exp.2 (by linarith [abs_nonneg (w 0)])
    _ = _ := Real.exp_add _ _

theorem site_poincare_FIN060 (w : Fin 1 → ℝ) :
    PoincareAt (siteLaw uSFIN060 phiSFIN060 (haar 1) w) IsSmoothPeriodic thetaFIN060
      (Real.exp (2 * |w 0|) * (4 * Real.pi ^ 2)⁻¹) := by
  have := isProbabilityMeasure_siteLaw hubbardHyp_FIN060 (m := haar 1) w
  exact poincare_comparison (Q := haar 1) (P := siteLaw uSFIN060 phiSFIN060 (haar 1) w)
    (ρ := siteDensity uSFIN060 phiSFIN060 (haar 1) w) rfl
    (fun x => div_nonneg (expTerm_pos w x).le (auxPartition_pos hubbardHyp_FIN060 (m := haar 1) w).le)
    (siteDensity_osc_FIN060 w) (fun f hf => memLp_two_smooth_FIN060 hf) site_poincare_haar_FIN060

theorem hcond_FIN060 (N : ℕ+) (w : Fin 1 → ℝ) :
    PoincareAt (condLaw uSFIN060 phiSFIN060 (haar 1) N w) IsSmoothPeriodicParticle smoothGamma
      (Real.exp (2 * |w 0|) * (4 * Real.pi ^ 2)⁻¹) := by
  have := isProbabilityMeasure_siteLaw hubbardHyp_FIN060 (m := haar 1) w
  intro f hf
  have hdens : ∀ (i : Fin N) (x : ParticleSpace 1 N), dens thetaFIN060 f i x =
      ENNReal.ofReal (∑ j : Fin 1, particlePartial i j f x ^ 2) := by
    intro i x
    unfold dens thetaFIN060
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    show coordPartial j (fun t => f (Function.update x i t)) (x i) ^ 2 = _
    rw [DGPS.Lipschitz.df_coordPartial_slice hf x i j (x i), Function.update_eq_self]
  have hTP : TP IsSmoothPeriodic thetaFIN060
      (fun _ : Fin N => siteLaw uSFIN060 phiSFIN060 (haar 1) w) f := by
    obtain ⟨hm, B, hB⟩ := measurable_bounded_of_smooth hf
    refine ⟨hm, ?_, fun x i => DGPS.Lipschitz.df_isSmoothPeriodic_slice hf x i, fun i => ?_⟩
    · exact MemLp.of_bound hm.aestronglyMeasurable B
        (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
    · have : dens thetaFIN060 f i = fun x => ENNReal.ofReal (∑ j : Fin 1, particlePartial i j f x ^ 2) :=
        funext (hdens i)
      rw [this]
      exact (ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ =>
        (measurable_bounded_partial_of_smooth hf i j).1.pow_const 2)).aemeasurable
  have hT := poincare_tensorization (fun _ : Fin N => siteLaw uSFIN060 phiSFIN060 (haar 1) w)
    (fun _ => site_poincare_FIN060 w) f hTP
  refine hT.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun x => ?_
  show ∑ i, dens thetaFIN060 f i x = smoothGamma f x
  simp_rw [hdens]
  unfold smoothGamma
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]

theorem sqrtD_sq_FIN060 {κ : ℝ} (hκ : 0 < κ) : (sqrtD (dSFIN060 κ) 0 0) ^ 2 = κ := by
  have h := congrFun (congrFun (sqrtD_mul_self (dSFIN060_posDef hκ)) 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_one] at h
  rw [sq]; rw [h]; simp [dSFIN060]

theorem posteriorCenter_zero_FIN060 (κ h : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    |posteriorCenter (dSFIN060 κ) (hSFIN060 h) phiSFIN060 N x 0| ≤ |h| + |κ| := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hS : |fieldSum phiSFIN060 x 0| ≤ N := by
    have : fieldSum phiSFIN060 x 0 = ∑ i, scalarCos (x i) := by
      simp [fieldSum, phiSFIN060, Finset.sum_apply]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |scalarCos (x i)| ≤ ∑ _i : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => scalarCos_bound (x i)
      _ = N := by simp
  have e : posteriorCenter (dSFIN060 κ) (hSFIN060 h) phiSFIN060 N x 0 =
      h + (N : ℝ)⁻¹ * (κ * fieldSum phiSFIN060 x 0) := by
    simp [posteriorCenter, hSFIN060, dSFIN060]
  rw [e]
  have hb : |(N : ℝ)⁻¹ * (κ * fieldSum phiSFIN060 x 0)| ≤ |κ| := by
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hN]
    calc (N : ℝ)⁻¹ * (|κ| * |fieldSum phiSFIN060 x 0|) ≤ (N : ℝ)⁻¹ * (|κ| * N) := by gcongr
      _ = |κ| := by field_simp
  calc _ ≤ |h| + |(N : ℝ)⁻¹ * (κ * fieldSum phiSFIN060 x 0)| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem hK_FIN060 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (2 * |w 0|) * (4 * Real.pi ^ 2)⁻¹)
        ∂(gaussLaw (dSFIN060 κ) N (posteriorCenter (dSFIN060 κ) (hSFIN060 h) phiSFIN060 N x)) ≤
      ENNReal.ofReal (2 * Real.exp (2 * (|h| + |κ|) + 2 * κ) * (4 * Real.pi ^ 2)⁻¹) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  set c := posteriorCenter (dSFIN060 κ) (hSFIN060 h) phiSFIN060 N x with hc
  have hmeasF : Measurable fun w : Fin 1 → ℝ =>
      ENNReal.ofReal (Real.exp (2 * |w 0|) * (4 * Real.pi ^ 2)⁻¹) := by fun_prop
  rw [← map_stdGaussian_affine (dSFIN060_posDef hκ) N c, lintegral_map hmeasF
    (measurable_affineMap _ N c)]
  set a : ℝ := (Real.sqrt (N : ℝ))⁻¹ * sqrtD (dSFIN060 κ) 0 0 with ha
  have hpt : ∀ ξ : Fin 1 → ℝ, affineMap (dSFIN060 κ) N c ξ 0 = c 0 + a * ξ 0 := by
    intro ξ
    simp [affineMap, Matrix.mulVec, dotProduct, ha, mul_assoc]
  have ha2 : a ^ 2 ≤ κ := by
    have hs : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by linarith)
    have : a ^ 2 = (N : ℝ)⁻¹ * κ := by
      rw [ha, mul_pow, inv_pow, hs, sqrtD_sq_FIN060 hκ]
    rw [this]
    calc (N : ℝ)⁻¹ * κ ≤ 1 * κ := by gcongr; exact inv_le_one_of_one_le₀ hN
      _ = κ := one_mul _
  have hc0 : |c 0| ≤ |h| + |κ| := posteriorCenter_zero_FIN060 κ h N x
  have hq : 0 ≤ (4 * Real.pi ^ 2)⁻¹ := by positivity
  simp_rw [hpt]
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr
  refine (lintegral_exp_abs_affine_FIN060 (c 0) a).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  gcongr

end DGPS.FiniteN.ScalarFoldFIN060
