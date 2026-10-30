import DGPS.FiniteN.AnisotropicQuarticAuxiliaryMass
import DGPS.FiniteN.Tools.Exterior

/-! Actual gradient and Laplacian bounds for the FIN070 exterior argument. -/

open MeasureTheory
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.AttractiveLandscape
open scoped ContDiff RealInnerProductSpace

namespace DGPS.FiniteN

/-- The actual derivative grows at least linearly outside a fixed ball. This uses
its exact mean-field derivative formula, rather than inferring a gradient from growth. -/
theorem quartic_gradient_far_bound :
    ∃ ρ > 0, ∃ c > 0, ∀ w : EuclideanSpace ℝ (Fin 2),
      ρ ≤ ‖w‖ → c * ‖w‖ ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖ := by
  have hk := quarticKappa_pos_FIN066
  let L := Real.sqrt (quarticKappa * (1 + quarticEta))
  let ρ := 2 + 2 * quarticKappa * L ^ 2
  have hκL : 0 ≤ 2 * quarticKappa * L ^ 2 := by positivity
  refine ⟨ρ, by dsimp [ρ]; positivity, 1 / (8 * quarticKappa), by positivity,
    fun w hw => ?_⟩
  let u : EuclideanSpace ℝ (Fin 2) := w - !₂[1, 0]
  let z := amap_FIN066 w
  have heq : Alin_FIN066 u = z := by
    ext i
    fin_cases i <;> simp [u, z, Alin_apply_FIN066, amap_FIN066]
  have hunit : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hu : ‖w‖ - 1 ≤ ‖u‖ := by
    simpa only [u, hunit] using norm_sub_norm_le w (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
  have hu1 : 1 ≤ ‖u‖ := by dsimp [ρ] at hw; linarith
  have hul : 2 * quarticKappa * L ^ 2 ≤ ‖u‖ ^ 2 := by
    dsimp [ρ] at hw
    nlinarith [sq_nonneg (‖u‖ - 1)]
  have huhalf : ‖w‖ / 2 ≤ ‖u‖ := by dsimp [ρ] at hw; linarith
  have hA := norm_Alin_FIN066 u
  rw [heq] at hA
  have hm := norm_featureMean_le continuous_U_FIN066 continuous_Phi_FIN066 norm_Phi_le_FIN066 z
  have him : ⟪featureMean featU_FIN066 featPhi_FIN066 z, z⟫ ≤ L * ‖z‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hm (norm_nonneg z))
  have heval : fderiv ℝ quarticPsi_FIN066 w u =
      ‖z‖ ^ 2 - ⟪featureMean featU_FIN066 featPhi_FIN066 z, z⟫ := by
    rw [fderiv_quarticPsi_FIN066, ContinuousLinearMap.comp_apply,
      fderiv_psi continuous_U_FIN066 continuous_Phi_FIN066]
    change ⟪z - featureMean featU_FIN066 featPhi_FIN066 z, Alin_FIN066 u⟫ = _
    rw [heq, inner_sub_left, real_inner_self_eq_norm_sq]
  have hevalLower : ‖u‖ ^ 2 / (2 * quarticKappa) - L ^ 2 / 2 ≤
      fderiv ℝ quarticPsi_FIN066 w u := by
    rw [heval, show ‖u‖ ^ 2 / (2 * quarticKappa) = (‖u‖ ^ 2 / quarticKappa) / 2 by ring]
    nlinarith [sq_nonneg (‖z‖ - L)]
  have hevalOp : fderiv ℝ quarticPsi_FIN066 w u ≤
      ‖fderiv ℝ quarticPsi_FIN066 w‖ * ‖u‖ :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using (fderiv ℝ quarticPsi_FIN066 w).le_opNorm u)
  have hsmall : L ^ 2 / 2 ≤ ‖u‖ ^ 2 / (4 * quarticKappa) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * quarticKappa)).2
    nlinarith only [hul]
  have hstep : ‖u‖ ^ 2 / (4 * quarticKappa) ≤
      ‖fderiv ℝ quarticPsi_FIN066 w‖ * ‖u‖ := by
    have hre : ‖u‖ ^ 2 / (2 * quarticKappa) =
        2 * (‖u‖ ^ 2 / (4 * quarticKappa)) := by ring
    rw [hre] at hevalLower
    linarith only [hevalLower, hevalOp, hsmall]
  have hgrad : ‖u‖ / (4 * quarticKappa) ≤ ‖fderiv ℝ quarticPsi_FIN066 w‖ := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * quarticKappa)).2
    have hclear := (div_le_iff₀ (by positivity : 0 < 4 * quarticKappa)).mp hstep
    have hprod : ‖u‖ * ‖u‖ ≤ (‖fderiv ℝ quarticPsi_FIN066 w‖ * (4 * quarticKappa)) * ‖u‖ := by
      nlinarith only [hclear]
    exact le_of_mul_le_mul_right hprod (lt_of_lt_of_le zero_lt_one hu1)
  calc
    _ = (‖w‖ / 2) / (4 * quarticKappa) := by ring
    _ ≤ ‖u‖ / (4 * quarticKappa) := div_le_div_of_nonneg_right huhalf (by positivity)
    _ ≤ _ := hgrad

/-- A global upper Laplacian bound from the actual nonnegative covariance term. -/
theorem quartic_laplacian_upper (w : EuclideanSpace ℝ (Fin 2)) :
    Laplacian.laplacian quarticPsi_FIN066 w ≤
      1 / quarticKappa + 1 / (quarticKappa * quarticEta) := by
  have hk := quarticKappa_pos_FIN066
  have hke := kappa_eta_pos_FIN066
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hd : Differentiable ℝ (fderiv ℝ quarticPsi_FIN066) :=
    (quartic_potential_contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hdir : ∀ i : Fin 2,
      fderiv ℝ (fun y => fderiv ℝ quarticPsi_FIN066 y (e i)) w (e i) =
        fderiv ℝ (fderiv ℝ quarticPsi_FIN066) w (e i) (e i) := by
    intro i
    rw [fderiv_clm_apply (hd w) (differentiableAt_const (e i))]
    simp
  calc
    _ = ∑ i, fderiv ℝ (fderiv ℝ quarticPsi_FIN066) w (e i) (e i) := by
      rw [groundState_laplacian_eq_sum_basis quarticPsi_FIN066 quartic_potential_contDiff]
      exact Finset.sum_congr rfl fun i _ => hdir i
    _ ≤ ∑ i, ‖Alin_FIN066 (e i)‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hessian_quarticPsi_FIN066,
        hessian_psi continuous_U_FIN066 continuous_Phi_FIN066, real_inner_self_eq_norm_sq]
      linarith [featureCov_self_nonneg (U := featU_FIN066) (Φ := featPhi_FIN066)
        (amap_FIN066 w) (Alin_FIN066 (e i))]
    _ = _ := by
      simp [e, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Alin_apply_FIN066,
        div_pow, Real.sq_sqrt hk.le, Real.sq_sqrt hke.le]

end DGPS.FiniteN
