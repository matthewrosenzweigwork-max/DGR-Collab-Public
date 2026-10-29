import SharpSymmetricLSI.Paper.GaussFormClause4
import SharpSymmetricLSI.Paper.FormDuality4
import SharpSymmetricLSI.Paper.GaussForm31

/-!
# R32 form clause (lane s42), step 5: the Gaussian identity in the variables `ξ`

For `F ∈ C^∞_c(ℝ^J)` and the standard Gaussian `N(0,1)^{⊗J}`:
`∫ F (y_j ∂_jF - ∂_{jj}F) = ∫ (∂_jF)²` (`integral_stein_sq`, Stein's lemma applied to `F ∂_jF`).
-/

noncomputable section
open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal ContDiff

namespace SharpLSI

/-- Stein's lemma on `ℝ^J` for `g ∈ C^∞_c`. -/
theorem stein_pi_cc {J : ℕ} {g : (Fin J → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (j : Fin J) :
    ∫ y, y j * g y ∂Measure.pi (fun _ : Fin J => gaussianReal 0 1) =
      ∫ y, pd g j y ∂Measure.pi (fun _ : Fin J => gaussianReal 0 1) := by
  obtain ⟨B, hB1, hB2, hc, hd⟩ := exists_bounds_of_cc hg hgc
  cases J with
  | zero => exact j.elim0
  | succ n => exact stein_pi hd hc hB1 hB2 j

theorem integrable_coord_pi {J : ℕ} (j : Fin J) :
    Integrable (fun y : Fin J → ℝ => y j) (Measure.pi fun _ : Fin J => gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin J => gaussianReal 0 1) j).integrable_comp_of_integrable
    (g := id) ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl)

theorem integrable_of_bdd_cont {J : ℕ} {h : (Fin J → ℝ) → ℝ} (hc : Continuous h) {B : ℝ}
    (hB : ∀ y, |h y| ≤ B) :
    Integrable h (Measure.pi fun _ : Fin J => gaussianReal 0 1) :=
  Integrable.of_bound hc.aestronglyMeasurable B (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hB y)

/-- **`∫ F (y_j ∂_jF - ∂_{jj}F) dN(0,1)^J = ∫ (∂_jF)² dN(0,1)^J`.** -/
theorem integral_stein_sq {J : ℕ} {F : (Fin J → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (j : Fin J) :
    ∫ y, F y * (y j * pd F j y - pd (pd F j) j y) ∂Measure.pi (fun _ : Fin J => gaussianReal 0 1) =
      ∫ y, pd F j y ^ 2 ∂Measure.pi (fun _ : Fin J => gaussianReal 0 1) := by
  set π := Measure.pi fun _ : Fin J => gaussianReal 0 1
  have hd1 := contDiff_pd hF j
  have hd2 := contDiff_pd hd1 j
  have hc1 := hasCompactSupport_pd hFc j
  have hc2 := hasCompactSupport_pd hc1 j
  set g : (Fin J → ℝ) → ℝ := fun y => F y * pd F j y
  have hg : ContDiff ℝ ∞ g := hF.mul hd1
  have hgc : HasCompactSupport g := hFc.mul_right
  have hst := stein_pi_cc hg hgc j
  have hpd : ∀ y, pd g j y = pd F j y * pd F j y + F y * pd (pd F j) j y := fun y => by
    have hFd : DifferentiableAt ℝ F y := (hF.differentiable (by simp)) y
    have h1d : DifferentiableAt ℝ (pd F j) y := (hd1.differentiable (by simp)) y
    show fderiv ℝ (fun y => F y * pd F j y) y (Pi.single j 1) =
      pd F j y * pd F j y + F y * pd (pd F j) j y
    rw [fderiv_fun_mul hFd h1d]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, pd]
    ring
  obtain ⟨BF, hBF⟩ := hFc.exists_bound_of_continuous hF.continuous
  obtain ⟨B1, hB1⟩ := hc1.exists_bound_of_continuous hd1.continuous
  obtain ⟨B2, hB2⟩ := hc2.exists_bound_of_continuous hd2.continuous
  have iF2 : Integrable (fun y => F y * pd (pd F j) j y) π :=
    integrable_of_bdd_cont (hF.continuous.mul hd2.continuous) (B := BF * B2) fun y => by
      rw [abs_mul]; exact mul_le_mul (by simpa using hBF y) (by simpa using hB2 y) (abs_nonneg _)
        ((norm_nonneg _).trans (hBF y))
  have iD : Integrable (fun y => pd F j y ^ 2) π :=
    integrable_of_bdd_cont (hd1.continuous.pow 2) (B := B1 ^ 2) fun y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using hB1 y) 2
  have iyg : Integrable (fun y => y j * g y) π := by
    refine ((integrable_coord_pi j).abs.mul_const (BF * B1)).mono'
      ((continuous_apply j).mul hg.continuous).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (by simpa using hBF y) (by simpa using hB1 y)
      (abs_nonneg _) ((norm_nonneg _).trans (hBF y))) (abs_nonneg _)
  have e1 : (fun y => F y * (y j * pd F j y - pd (pd F j) j y)) =
      fun y => y j * g y - F y * pd (pd F j) j y := by
    funext y; simp only [g]; ring
  rw [e1, integral_sub iyg iF2, hst]
  have e2 : (fun y => pd g j y) = fun y => pd F j y ^ 2 + F y * pd (pd F j) j y := by
    funext y; rw [hpd]; ring
  rw [e2, integral_add iD iF2]
  ring

end SharpLSI
