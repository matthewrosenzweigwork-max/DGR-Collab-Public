import DGPS.FiniteN.QuarticSaddleCriticalFIN067
import DGPS.FiniteN.Tools.NegativeDirection

/-! Actual nondegenerate negative-axis patches needed by the FIN070 IMS assembly. -/

open MeasureTheory Set
open scoped ContDiff
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

/-- Every actual negative-axis critical point other than the quartic saddle has a
fixed open patch with an unnormalized Dirichlet lower rate proportional to N. -/
theorem quartic_other_critical_local_dirichlet {s : ℝ} (hs : 0 < s) (hs4 : s < 4)
    (hcrit : fderiv ℝ quarticPsi_FIN066 !₂[-s, 0] = 0) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ !₂[-s, 0] ∈ U ∧
      ∃ a : ℝ, 0 < a ∧ ∀ N : ℝ, 0 ≤ N →
      ∀ F : EuclideanSpace ℝ (Fin 2) → ℝ, ContDiff ℝ ∞ F →
        HasCompactSupport F → tsupport F ⊆ U →
        a * N * (∫ x, F x ^ 2 * Real.exp (-(N * quarticPsi_FIN066 x))) ≤
          ∫ x, ‖fderiv ℝ F x‖ ^ 2 * Real.exp (-(N * quarticPsi_FIN066 x)) := by
  have hmap : ContDiff ℝ ∞ amap_FIN066 := by
    rw [show amap_FIN066 = fun z => Alin_FIN066 z +
      !₂[-1 / Real.sqrt quarticKappa, 0] from funext amap_eq_FIN066]
    exact Alin_FIN066.contDiff.add contDiff_const
  have hψ : ContDiff ℝ ∞ quarticPsi_FIN066 := by
    rw [quarticPsi_eq_FIN066]
    exact (DGPS.FiniteN.AttractiveLandscape.contDiff_psi_infty
      continuous_U_FIN066 continuous_Phi_FIN066).comp hmap
  let v := EuclideanSpace.basisFun (Fin 2) ℝ (1 : Fin 2)
  have hv : ‖v‖ = 1 := by simp [v]
  have hvect : v = !₂[0, 1] := by
    ext i
    fin_cases i <;> simp [v]
  let H : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => fderiv ℝ (fderiv ℝ quarticPsi_FIN066) x v v
  have hH : Continuous H :=
    (((hψ.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).clm_apply
      continuous_const).clm_apply continuous_const
  have hneg : H !₂[-s, 0] < 0 := by
    dsimp [H]
    rw [hvect]
    exact (quartic_complete_critical_point_exclusion.2.2.2.2.2.1 s hs hs4 hcrit).2.2
  let c := -H !₂[-s, 0] / 2
  have hc : 0 < c := by dsimp [c]; linarith
  let U := H ⁻¹' Iio (-c)
  have hU : IsOpen U := isOpen_Iio.preimage hH
  have hw : !₂[-s, 0] ∈ U := by change H !₂[-s, 0] < -c; dsimp [c]; linarith
  have hd : Differentiable ℝ (fderiv ℝ quarticPsi_FIN066) :=
    (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hdir : ∀ x ∈ U,
      fderiv ℝ (fun y => fderiv ℝ quarticPsi_FIN066 y v) x v ≤ -c := by
    intro x hx
    have heq : fderiv ℝ (fun y => fderiv ℝ quarticPsi_FIN066 y v) x =
        (fderiv ℝ (fderiv ℝ quarticPsi_FIN066) x).flip v := by
      rw [fderiv_clm_apply (hd x) (differentiableAt_const v)]
      simp
    rw [heq]
    exact le_of_lt hx
  refine ⟨U, hU, hw, c / 2, by positivity, fun N hN F hF hFc hFU => ?_⟩
  convert negative_direction_local_dirichlet_rate quarticPsi_FIN066 hψ v hv U c hc hdir
    N hN F hF hFc hFU using 1 <;> ring

end DGPS.FiniteN
