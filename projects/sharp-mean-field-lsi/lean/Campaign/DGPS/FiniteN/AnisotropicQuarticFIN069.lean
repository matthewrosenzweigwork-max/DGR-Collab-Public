import DGPS.FiniteN.AnisotropicQuarticLocalLower

/-!
# FIN069: the actual anisotropic quartic local Dirichlet estimate

This restores the exact Euclidean volume and derivative norm of the public auxiliary
statement from the actual same-chart product-coordinate lower bound. It makes no claim
about the global auxiliary Poincare inequality or the final T13 particle rate row.
-/

open MeasureTheory Filter Topology Set
open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.FiniteN

/-- Actual FIN069: a fixed remote patch in the Euclidean auxiliary plane has local
Dirichlet rate at least a positive constant times sqrt N, for every real N at least one. -/
theorem quartic_unstable_local_dirichlet_square_root_n :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ !₂[-4, 0] ∈ U ∧
      ∃ a : ℝ, 0 < a ∧ ∀ N : ℝ, 1 ≤ N → ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ U →
        a * Real.sqrt N * (∫ w, f w ^ 2 * Real.exp (-(N * quarticPsi_FIN066 w))) ≤
          ∫ w, ‖fderiv ℝ f w‖ ^ 2 * Real.exp (-(N * quarticPsi_FIN066 w)) := by
  let S : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨W, hWo, hW0, a, ha, hlocal⟩ := quartic_product_local_dirichlet
  let U : Set (EuclideanSpace ℝ (Fin 2)) := S ⁻¹' W
  have hvol : MeasurePreserving S := by
    convert quartic_euclidean_volume_preserving using 1 <;> rfl
  have hemb : MeasurableEmbedding S := S.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  refine ⟨U, hWo.preimage S.continuous, ?_, a, ha, fun N hN f hf hfc hfu => ?_⟩
  · change (-4, 0) ∈ W
    exact hW0
  · let F : ℝ × ℝ → ℝ := f ∘ S.symm
    have hF : ContDiff ℝ ∞ F := hf.comp S.symm.contDiff
    have hFc : HasCompactSupport F := hfc.comp_homeomorph S.symm.toHomeomorph
    have hFU : tsupport F ⊆ W := by
      change tsupport (f ∘ S.symm.toHomeomorph) ⊆ W
      rw [tsupport_comp_eq_preimage]
      intro p hp
      have h := hfu hp
      change S (S.symm p) ∈ W at h
      simpa only [S.apply_symm_apply] using h
    have hFS : ∀ w : EuclideanSpace ℝ (Fin 2), F (S w) = f w := by
      intro w
      change f (S.symm (S w)) = f w
      rw [S.symm_apply_apply]
    have hfun : (fun w : EuclideanSpace ℝ (Fin 2) => F (w 0, w 1)) = f := by
      funext w
      exact hFS w
    have henergy : ∀ w : EuclideanSpace ℝ (Fin 2),
        ‖fderiv ℝ f w‖ ^ 2 = (fderiv ℝ F (S w) (1, 0)) ^ 2 +
          (fderiv ℝ F (S w) (0, 1)) ^ 2 := by
      intro w
      have h := quartic_euclidean_energy F w ((hF.differentiable (by simp)) (S w))
      rw [hfun] at h
      exact h
    have hmass : (∫ w, f w ^ 2 * Real.exp (-(N * quarticPsi_FIN066 w))) =
        ∫ p : ℝ × ℝ, F p ^ 2 * Real.exp (-(N * quarticPsi_FIN066 !₂[p.1, p.2])) := by
      have h := hvol.integral_comp hemb (fun p => F p ^ 2 *
        Real.exp (-(N * quarticPsi_FIN066 (S.symm p))))
      change (∫ w, F (S w) ^ 2 * Real.exp (-(N * quarticPsi_FIN066 (S.symm (S w))))) = _ at h
      simp only [hFS, S.symm_apply_apply] at h
      exact h
    have hdir : (∫ w, ‖fderiv ℝ f w‖ ^ 2 * Real.exp (-(N * quarticPsi_FIN066 w))) =
        ∫ p : ℝ × ℝ, ((fderiv ℝ F p (1, 0)) ^ 2 + (fderiv ℝ F p (0, 1)) ^ 2) *
          Real.exp (-(N * quarticPsi_FIN066 !₂[p.1, p.2])) := by
      have h := hvol.integral_comp hemb (fun p =>
        ((fderiv ℝ F p (1, 0)) ^ 2 + (fderiv ℝ F p (0, 1)) ^ 2) *
          Real.exp (-(N * quarticPsi_FIN066 (S.symm p))))
      change (∫ w, ((fderiv ℝ F (S w) (1, 0)) ^ 2 + (fderiv ℝ F (S w) (0, 1)) ^ 2) *
        Real.exp (-(N * quarticPsi_FIN066 (S.symm (S w))))) = _ at h
      simp only [S.symm_apply_apply, ← henergy] at h
      exact h
    have h := hlocal N hN F hF hFc hFU
    rw [← hmass, ← hdir] at h
    exact h

end DGPS.FiniteN
