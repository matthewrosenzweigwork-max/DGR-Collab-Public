import SharpSymmetricLSI.Paper.GaussForm1

/-!
# R32 (A2): Stein's lemma for linear images of the standard Gaussian

For a matrix `A` and `g ∈ C¹` bounded with bounded continuous derivative:
`∫ (Ay)_k g(Ay) dγ_N(y) = ∑_l (AAᵀ)_{kl} ∫ ∂_l g(Ay) dγ_N(y)` (`stein_matrix`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal Matrix

namespace SharpLSI

/-- `y ↦ A y` as a continuous linear map. -/
noncomputable def matCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

theorem matCLM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    matCLM A y = A *ᵥ y := rfl

theorem matCLM_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n) :
    matCLM A (Pi.single m 1) = ∑ l, A l m • (Pi.single l 1 : Fin n → ℝ) := by
  funext i
  simp [matCLM_apply, Matrix.mulVec_single, Finset.sum_apply, Pi.single_apply]

theorem fderiv_apply_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (c : Fin n → ℝ) :
    L (∑ l, c l • (Pi.single l 1 : Fin n → ℝ)) = ∑ l, c l * L (Pi.single l 1) := by
  simp [map_sum, map_smul]

/-- **Stein's lemma for `A y`, `y` standard Gaussian.** -/
theorem stein_matrix {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {g : (Fin (n + 1) → ℝ) → ℝ} (hg : Differentiable ℝ g) (hgc : Continuous fun y => fderiv ℝ g y)
    {B : ℝ} (hgB : ∀ y, |g y| ≤ B) (hdB : ∀ y, ‖fderiv ℝ g y‖ ≤ B) (k : Fin (n + 1)) :
    ∫ y, (A *ᵥ y) k * g (A *ᵥ y) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∑ l, (A * Aᵀ) k l * ∫ y, fderiv ℝ g (A *ᵥ y) (Pi.single l 1)
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  set P := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  set L := matCLM A
  set F : (Fin (n + 1) → ℝ) → ℝ := fun y => g (L y)
  have hFd : ∀ y, HasFDerivAt F ((fderiv ℝ g (L y)).comp L) y := fun y =>
    (hg (L y)).hasFDerivAt.comp y L.hasFDerivAt
  have hF : Differentiable ℝ F := fun y => (hFd y).differentiableAt
  have hFder : ∀ y, fderiv ℝ F y = (fderiv ℝ g (L y)).comp L := fun y => (hFd y).fderiv
  have hFc : Continuous fun y => fderiv ℝ F y := by
    simp_rw [hFder]
    exact (ContinuousLinearMap.compL ℝ _ _ _ |>.flip L).continuous.comp (hgc.comp L.continuous)
  have hFB : ∀ y, |F y| ≤ B := fun y => hgB _
  have hFdB : ∀ y, ‖fderiv ℝ F y‖ ≤ B * ‖L‖ := fun y => by
    rw [hFder]; exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hdB _) (norm_nonneg _))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB 0)
  set B' := max B (B * ‖L‖)
  have hst : ∀ m, ∫ y, y m * F y ∂P = ∫ y, fderiv ℝ F y (Pi.single m 1) ∂P := fun m =>
    stein_pi hF hFc (B := B') (fun y => (hFB y).trans (le_max_left _ _))
      (fun y => (hFdB y).trans (le_max_right _ _)) m
  -- expand `(A y)_k = ∑_m A_{km} y_m`
  have hm : ∀ m, Integrable (fun y : Fin (n + 1) → ℝ => y m) P := fun m =>
    (measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) m).integrable_comp_of_integrable
      (g := id) ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl)
  have hFm : Continuous F := hF.continuous
  have hint : ∀ m, Integrable (fun y => y m * F y) P := fun m =>
    ((hm m).abs.mul_const B).mono' ((continuous_apply m).mul hFm).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hFB y) (abs_nonneg _))
  have hIc : ∀ l, Continuous fun y => fderiv ℝ g (L y) (Pi.single l 1) := fun l =>
    (hgc.comp L.continuous).clm_apply continuous_const
  have hIb : ∀ l y, |fderiv ℝ g (L y) (Pi.single l 1)| ≤ B := fun l y => by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have : ‖(Pi.single l 1 : Fin (n + 1) → ℝ)‖ = 1 := by simp [Pi.norm_single]
    rw [this, mul_one]; exact hdB _
  have hIi : ∀ l, Integrable (fun y => fderiv ℝ g (L y) (Pi.single l 1)) P := fun l =>
    (integrable_const B).mono' (hIc l).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hIb l y)
  have hdF : ∀ m y, fderiv ℝ F y (Pi.single m 1) =
      ∑ l, A l m * fderiv ℝ g (L y) (Pi.single l 1) := fun m y => by
    rw [hFder, ContinuousLinearMap.comp_apply, matCLM_single, fderiv_apply_sum]
  have hL : ∀ y, A *ᵥ y = L y := fun y => rfl
  calc ∫ y, (A *ᵥ y) k * g (A *ᵥ y) ∂P
      = ∫ y, ∑ m, A k m * (y m * F y) ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, F, hL]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ = ∑ m, A k m * ∫ y, y m * F y ∂P := by
        rw [integral_finsetSum _ fun m _ => (hint m).const_mul _]
        exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
    _ = ∑ m, A k m * ∑ l, A l m * ∫ y, fderiv ℝ g (L y) (Pi.single l 1) ∂P := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hst m]
        simp_rw [hdF m]
        rw [integral_finsetSum _ fun l _ => (hIi l).const_mul _]
        exact congrArg _ (Finset.sum_congr rfl fun l _ => integral_const_mul _ _)
    _ = ∑ l, (A * Aᵀ) k l * ∫ y, fderiv ℝ g (A *ᵥ y) (Pi.single l 1) ∂P := by
        simp_rw [Finset.mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        simp only [hL]
        ring

end SharpLSI
