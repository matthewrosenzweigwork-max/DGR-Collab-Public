import DGPS.FiniteN.AnisotropicQuarticPatchCover
import DGPS.FiniteN.AnisotropicQuarticGradientGap

/-! Actual centered IMS globalization of the quartic auxiliary lower estimate. -/

open MeasureTheory Set Metric
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.TiltedXY.Fin049
open scoped ContDiff

namespace DGPS.FiniteN

/-- Actual global auxiliary square-root-N lower rate on compact smooth mean-zero
tests. This is the IMS core of FIN070, before the bounded-test domain closure. -/
theorem quartic_auxiliary_global_sqrt_poincare :
    ∃ a : ℝ, 0 < a ∧ ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F →
        (∫ w, F w ∂imsEta N quarticPsi_FIN066) = 0 →
          a * Real.sqrt N * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
            ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
  classical
  obtain ⟨t, ht, hroot, r, c1, hr, hc1, hess, htail,
    m, U, j0, hU0, hUo, hUc, hcov, a, ha, hlocal⟩ := quartic_finite_critical_patch_cover
  let w0 : EuclideanSpace ℝ (Fin 2) := !₂[t, 0]
  obtain ⟨δ, hδ, hgap⟩ := quartic_gradient_gap_off_critical_cover
    (⋃ j, U j) (isOpen_iUnion hUo) hcov
  let W := {w : EuclideanSpace ℝ (Fin 2) | δ / 2 < ‖fderiv ℝ quarticPsi_FIN066 w‖}
  have hgcont : Continuous (fun w => ‖fderiv ℝ quarticPsi_FIN066 w‖) :=
    (continuous_norm (E := EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).comp
      (quartic_potential_contDiff.continuous_fderiv (by simp))
  have hWo : IsOpen W := isOpen_lt continuous_const hgcont
  have hcover : Wᶜ ⊆ ⋃ j, U j := by
    intro w hw
    by_contra hu
    have hh := hgap w hu
    apply hw
    change δ / 2 < ‖fderiv ℝ quarticPsi_FIN066 w‖
    linarith
  have hsmall : closure (ball w0 (r / 2)) ⊆ U j0 := by
    rw [hU0]
    exact closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  obtain ⟨χ, hχ, hχpos, hsum, hχU, hχW, hχV, Cims, hCims⟩ :=
    ims_cutoffs_nonneg_FIN049 U hUo hUc W hWo hcover j0 (ball w0 (r / 2)) hsmall
  obtain ⟨ae, hae, Ne, hNe, hext⟩ := quartic_gradient_level_dirichlet (δ / 2) (half_pos hδ)
  obtain ⟨bA, hbA, CA, hCA, NA, hNA, htA⟩ := htail (r / 2) (half_pos hr)
  obtain ⟨bB, hbB, CB, hCB, NB, hNB, htB⟩ := htail r hr
  let N1 := max NA (max NB (max Ne (max 1 (2 * CB / bB))))
  have hNpack : ∀ N : ℝ, N1 ≤ N → NA ≤ N ∧ NB ≤ N ∧ Ne ≤ N ∧ 1 ≤ N ∧ 2 * CB / bB ≤ N := by
    intro N hN
    simpa only [N1, max_le_iff] using hN
  have hmass : ∀ N : ℝ, N1 ≤ N →
      (1 / 2 : ℝ) ≤ ((imsEta N quarticPsi_FIN066) (ball w0 r)).toReal := by
    intro N hN
    obtain ⟨hNa, hNb, hNe', hN1, hNm⟩ := hNpack N hN
    have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN1
    have hZ := quartic_partition_pos N hNp
    have hint := quartic_weight_integrable N hNp
    have hmeas : MeasurableSet {w : EuclideanSpace ℝ (Fin 2) | r ≤ dist w w0} :=
      (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
    have hcompl : {w : EuclideanSpace ℝ (Fin 2) | r ≤ dist w w0} = (ball w0 r)ᶜ := by
      ext w; simp only [mem_setOf_eq, mem_compl_iff, mem_ball, not_lt]
    have hsum1 : ((imsEta N quarticPsi_FIN066) (ball w0 r)).toReal +
        ((imsEta N quarticPsi_FIN066) {w | r ≤ dist w w0}).toReal = 1 := by
      rw [imsEta_real_FIN049 N quarticPsi_FIN066 hZ _ measurableSet_ball,
        imsEta_real_FIN049 N quarticPsi_FIN066 hZ _ hmeas,
        ← add_div, div_eq_one_iff_eq hZ.ne', hcompl]
      exact integral_add_compl measurableSet_ball hint
    have htailN := htB N hNb
    change ((imsEta N quarticPsi_FIN066) {w | r ≤ dist w w0}).toReal ≤
      CB * Real.exp (-(bB * N)) at htailN
    have hsmallN : CB * Real.exp (-(bB * N)) ≤ 1 / 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have h1 := Real.add_one_le_exp (bB * N)
      have h2 : 2 * CB ≤ N * bB := (div_le_iff₀ hbB).mp hNm
      nlinarith
    linarith
  have hout : ∀ N : ℝ, N1 ≤ N →
      ((imsEta N quarticPsi_FIN066) {w | χ (some j0) w ≠ 1}).toReal ≤
        CA * Real.exp (-(bA * N)) := by
    intro N hN
    obtain ⟨hNa, hNb, hNe', hN1, hNm⟩ := hNpack N hN
    haveI := quartic_imsEta_probability N (lt_of_lt_of_le zero_lt_one hN1)
    refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)).trans (htA N hNa)
    intro w (hw : χ (some j0) w ≠ 1)
    show r / 2 ≤ dist w w0
    by_contra h
    exact hw (hχV w (mem_ball.mpr (not_le.mp h)))
  let c := min a ae
  have hc : 0 < c := lt_min ha hae
  have hother : ∀ j, j ≠ j0 → ∀ N : ℝ, N1 ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ U j →
        c * N ^ (1 / 2 : ℝ) * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
          ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
    intro j hj N hN F hF hFc hFU
    have hN1 := (hNpack N hN).2.2.2.1
    have h := hlocal j hj N hN1 F hF hFc hFU
    rw [← Real.sqrt_eq_rpow]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left a ae) (Real.sqrt_nonneg N))
      (integral_nonneg fun w => sq_nonneg (F w))).trans h
  have houtside : ∀ N : ℝ, N1 ≤ N → ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ W →
        c * N ^ 2 * (∫ w, F w ^ 2 ∂imsEta N quarticPsi_FIN066) ≤
          ∫ w, ‖fderiv ℝ F w‖ ^ 2 ∂imsEta N quarticPsi_FIN066 := by
    intro N hN F hF hFc hFW
    have hNge := (hNpack N hN).2.2.1
    have h := hext N hNge F hF hFc (fun w hw => by
      change δ / 2 ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖
      exact (hFW hw).le)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right a ae) (sq_nonneg N))
      (integral_nonneg fun w => sq_nonneg (F w))).trans h
  obtain ⟨b, hb, N0, hglobal⟩ := auxiliary_poincare_globalization_with_the_mean
    quarticPsi_FIN066 quartic_potential_contDiff U W j0 χ Cims hχ hsum hCims hχU hχW
    w0 r c1 hc1 hU0 hess (hχpos _) N1 CA bA (1 / 2) hbA (by norm_num)
    hmass hout (1 / 2) c (by norm_num) (by norm_num) hc hother houtside
  refine ⟨b, hb, max N0 1, le_max_right _ _, fun N hN F hF hFc hF0 => ?_⟩
  have h := hglobal N ((le_max_left _ _).trans hN) F hF hFc hF0
  simpa only [Real.sqrt_eq_rpow] using h

end DGPS.FiniteN
