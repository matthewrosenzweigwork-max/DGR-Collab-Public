import FullLabeledLSI.Nonvacuity.Prop82.Subthreshold
import FullLabeledLSI.Paper.Sec8Approx

/-!
# Test-function bounds for the original Poincare constant

The zero-first-moment branch needs no nodal theorem: the two trigonometric
variances sum to one, and their Dirichlet energies are interchanged after
multiplication by `aCos`. One of the two Rayleigh quotients is at most `aCos`.

This file is proof source, not a claim of successful compilation.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

theorem SmoothProbability.memH1_weighted {rho f : Torus 1 → Real}
    (h : SmoothProbability rho) (hf : IsSmoothT f) : MemH1 (densMeasure rho) f := by
  obtain ⟨m, M, hm, hmrho, hrhoM⟩ :=
    Sec8.exists_pos_bounds (Sec8.continuous_of_smooth h.smooth) h.positive
  have hle := Sec8.densMeasure_le_smul hrhoM
  have hH := Sec8.memH1_of_smooth hf
  exact ⟨hH.1,
    hH.2.1.of_measure_le_smul ENNReal.ofReal_ne_top hle,
    hH.2.2.of_measure_le_smul ENNReal.ofReal_ne_top hle⟩

/-- A real Rayleigh bound, translated back to the original `ENNReal` infimum.
The denominator is proved positive; a total division cannot create the bound. -/
theorem poincare_le_of_smooth_test {rho k : Torus 1 → Real}
    (hrho : SmoothProbability rho) (hk : IsSmoothT k)
    (hm : ∫ x, rho x * k x ∂haar 1 = 0)
    (hv : 0 < ∫ x, rho x * k x ^ 2 ∂haar 1) :
    poincareConst (densMeasure rho) ≤ ENNReal.ofReal
      ((∫ x, rho x * Sec8.gradSq k x ∂haar 1) /
        (∫ x, rho x * k x ^ 2 ∂haar 1)) := by
  haveI := isProbabilityMeasure_densMeasure hrho.nonneg hrho.mass
  have hH := hrho.memH1_weighted hk
  have hmean : ∫ x, k x ∂densMeasure rho = 0 := by
    rw [integral_densMeasure hrho.nonneg hrho.mass, hm]
  have hvar : var (densMeasure rho) k =
      ENNReal.ofReal (∫ x, rho x * k x ^ 2 ∂haar 1) := by
    rw [var, ← ProbabilityTheory.ofReal_variance hH.2.1,
      ProbabilityTheory.variance_eq_sub hH.2.1]
    simp only [Pi.pow_apply, hmean, zero_pow (by norm_num : (2 : Nat) ≠ 0), sub_zero]
    rw [integral_densMeasure hrho.nonneg hrho.mass]
  have hvarpos : 0 < var (densMeasure rho) k := by
    rw [hvar]
    exact ENNReal.ofReal_pos.mpr hv
  calc
    poincareConst (densMeasure rho) ≤
        dirichlet (densMeasure rho) k / var (densMeasure rho) k :=
      iInf₂_le k ⟨hH, hvarpos⟩
    _ = _ := by
      rw [Sec8.dirichlet_smooth hrho.nonneg hrho.mass hk, hvar,
        ← ENNReal.ofReal_div_of_pos hv]

theorem poincare_lt_of_smooth_test {rho k : Torus 1 → Real}
    (hrho : SmoothProbability rho) (hk : IsSmoothT k)
    (hm : ∫ x, rho x * k x ∂haar 1 = 0)
    (hv : 0 < ∫ x, rho x * k x ^ 2 ∂haar 1)
    (he : (∫ x, rho x * Sec8.gradSq k x ∂haar 1) <
      realRate * (∫ x, rho x * k x ^ 2 ∂haar 1)) :
    poincareConst (densMeasure rho) < mfRate := by
  have hle := poincare_le_of_smooth_test hrho hk hm hv
  have he0 : 0 ≤ ∫ x, rho x * Sec8.gradSq k x ∂haar 1 :=
    integral_nonneg fun x => mul_nonneg (hrho.nonneg x) (Sec8.gradSq_nonneg k x)
  have hq : ENNReal.ofReal
      ((∫ x, rho x * Sec8.gradSq k x ∂haar 1) /
        (∫ x, rho x * k x ^ 2 ∂haar 1)) < ENNReal.ofReal realRate :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (div_nonneg he0 hv.le)).mpr
      ((div_lt_iff₀ hv).mpr he)
  rw [ofReal_realRate] at hq
  exact hle.trans_lt hq

theorem gCos_smooth : IsSmoothT gCos := contDiff_gCos_lift

theorem sCos_lift : sCos ∘ liftT =
    fun z : Fin 1 → Real => Real.sin (2 * Real.pi * z 0) := by
  funext z
  exact expT_im_coe (liftT z) (z 0) rfl

theorem sCos_smooth : IsSmoothT sCos := by
  unfold IsSmoothT
  rw [sCos_lift]
  exact (Real.contDiff_sin.comp
    (contDiff_const.mul (contDiff_apply Real Real 0))).of_le le_top

theorem fderiv_sCos_lift (z : Fin 1 → Real) :
    fderiv Real (sCos ∘ liftT) z (Pi.single 0 1) =
      (2 * Real.pi) * Real.cos (2 * Real.pi * z 0) := by
  refine fderiv_apply_of_line ((sCos_smooth.differentiable (by simp)) z) ?_
  rw [sCos_lift]
  have hh := (((hasDerivAt_id (0 : Real)).const_add (z 0)).const_mul
    (2 * Real.pi)).sin
  convert hh using 1
  · funext t; simp
  · simp; ring

theorem gradSq_gCos (x : Torus 1) : Sec8.gradSq gCos x = aCos * sCos x ^ 2 := by
  unfold Sec8.gradSq
  rw [Fin.sum_univ_one]
  change (fderiv Real (gCos ∘ liftT) (secT x) (Pi.single 0 1)) ^ 2 = _
  rw [fderiv_gCos_lift, sCos_secT]
  unfold aCos
  ring

theorem gradSq_sCos (x : Torus 1) : Sec8.gradSq sCos x = aCos * gCos x ^ 2 := by
  unfold Sec8.gradSq
  rw [Fin.sum_univ_one]
  change (fderiv Real (sCos ∘ liftT) (secT x) (Pi.single 0 1)) ^ 2 = _
  rw [fderiv_sCos_lift, gCos_secT]
  unfold aCos
  ring

theorem gCos_sq_add_sCos_sq (x : Torus 1) : gCos x ^ 2 + sCos x ^ 2 = 1 := by
  rw [gCos_secT, sCos_secT]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * secT x 0)]

theorem zero_means_of_firstMode_zero {rho : Torus 1 → Real}
    (hrho : SmoothProbability rho) (hQ : firstMode rho = 0) :
    (∫ x, rho x * gCos x ∂haar 1 = 0) ∧
      (∫ x, rho x * sCos x ∂haar 1 = 0) := by
  rw [firstMode_eq (Sec8.integrable_of_smooth hrho.smooth)] at hQ
  have hc : ∫ x, gCos x * rho x ∂haar 1 = 0 := by
    nlinarith [sq_nonneg (∫ x, sCos x * rho x ∂haar 1)]
  have hs : ∫ x, sCos x * rho x ∂haar 1 = 0 := by
    nlinarith [sq_nonneg (∫ x, gCos x * rho x ∂haar 1)]
  simpa only [mul_comm] using And.intro hc hs

/-- An unconditional bound for every smooth positive density with zero first
Fourier moment. No quotient optimizer is needed for this theorem. -/
theorem poincare_le_a_of_firstMode_zero {rho : Torus 1 → Real}
    (hrho : SmoothProbability rho) (hQ : firstMode rho = 0) :
    poincareConst (densMeasure rho) ≤ ENNReal.ofReal aCos := by
  let C : Real := ∫ x, rho x * gCos x ^ 2 ∂haar 1
  let S : Real := ∫ x, rho x * sCos x ^ 2 ∂haar 1
  have hC0 : 0 ≤ C := integral_nonneg fun x => mul_nonneg (hrho.nonneg x) (sq_nonneg _)
  have hS0 : 0 ≤ S := integral_nonneg fun x => mul_nonneg (hrho.nonneg x) (sq_nonneg _)
  have hc := Sec8.continuous_of_smooth hrho.smooth
  have hCS : C + S = 1 := by
    have h1 : Integrable (fun x => rho x * gCos x ^ 2) (haar 1) :=
      SharpLSI.integrable_of_continuous (hc.mul (continuous_gCos.pow 2))
    have h2 : Integrable (fun x => rho x * sCos x ^ 2) (haar 1) :=
      SharpLSI.integrable_of_continuous (hc.mul (continuous_sCos.pow 2))
    rw [← integral_add h1 h2]
    calc
      (∫ x, rho x * gCos x ^ 2 + rho x * sCos x ^ 2 ∂haar 1) =
          ∫ x, rho x ∂haar 1 := by
        congr 1
        funext x
        rw [← mul_add, gCos_sq_add_sCos_sq, mul_one]
      _ = 1 := hrho.mass
  have hEg : (∫ x, rho x * Sec8.gradSq gCos x ∂haar 1) = aCos * S := by
    simp_rw [gradSq_gCos]
    change (∫ x, rho x * (aCos * sCos x ^ 2) ∂haar 1) = _
    simp_rw [show ∀ x, rho x * (aCos * sCos x ^ 2) =
      aCos * (rho x * sCos x ^ 2) from fun x => by ring]
    rw [integral_const_mul]
  have hEs : (∫ x, rho x * Sec8.gradSq sCos x ∂haar 1) = aCos * C := by
    simp_rw [gradSq_sCos]
    change (∫ x, rho x * (aCos * gCos x ^ 2) ∂haar 1) = _
    simp_rw [show ∀ x, rho x * (aCos * gCos x ^ 2) =
      aCos * (rho x * gCos x ^ 2) from fun x => by ring]
    rw [integral_const_mul]
  obtain ⟨hmg, hms⟩ := zero_means_of_firstMode_zero hrho hQ
  rcases le_total S C with hSC | hCS'
  · have hC : 0 < C := by linarith
    have hb := poincare_le_of_smooth_test hrho gCos_smooth hmg hC
    rw [hEg] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    apply (div_le_iff₀ hC).mpr
    exact mul_le_mul_of_nonneg_left hSC a_pos.le
  · have hS : 0 < S := by linarith
    have hb := poincare_le_of_smooth_test hrho sCos_smooth hms hS
    rw [hEs] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    apply (div_le_iff₀ hS).mpr
    exact mul_le_mul_of_nonneg_left hCS' a_pos.le

theorem poincare_lt_rate_of_firstMode_zero {rho : Torus 1 → Real}
    (hrho : SmoothProbability rho) (hQ : firstMode rho = 0) :
    poincareConst (densMeasure rho) < mfRate := by
  exact (poincare_le_a_of_firstMode_zero hrho hQ).trans_lt
    (cosine_strict_aux (by norm_num : (0 : Real) < 1))

/-- General test-function version of the nonzero-moment argument. The actual
logarithmic-score construction and heat-stationarity identity are not assumed
silently: their precise consequences occur as explicit parameters here. -/
theorem poincare_lt_rate_of_score_data {rho k : Torus 1 → Real} {beta : Real}
    (hrho : SmoothProbability rho) (hk : IsSmoothT k)
    (hm : ∫ x, rho x * k x ∂haar 1 = 0)
    (hv : 0 < ∫ x, rho x * k x ^ 2 ∂haar 1)
    (hQ : 0 < firstMode rho) (hR : realRate < aCos * (3 / 2))
    (hb : beta < 2 / 3)
    (hstationary : 0 = -2 * (∫ x, rho x * Sec8.gradSq k x ∂haar 1) -
      5 * aCos ^ 2 * firstMode rho + 3 * aCos ^ 2 * firstMode rho * beta +
      2 * realRate * ((∫ x, rho x * k x ^ 2 ∂haar 1) + aCos * firstMode rho)) :
    poincareConst (densMeasure rho) < mfRate := by
  apply poincare_lt_of_smooth_test hrho hk hm hv
  exact score_energy_strict a_pos hQ hR hb
    (score_energy_of_stationarity hstationary)

end SharpLSI.FL.Prop82
