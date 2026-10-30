import DGPS.FiniteN.AnisotropicQuarticHubbard
import DGPS.FiniteN.AnisotropicQuarticAuxiliaryMass

/-! Actual conditional field moments and local mean control for the rare core. -/

open MeasureTheory Matrix Filter Topology
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
open scoped ContDiff

namespace DGPS.FiniteN

noncomputable def quarticConditionalFieldMean (w : Fin 2 → ℝ) : Fin 2 → ℝ :=
  w - quarticHubbardD *ᵥ auxGrad quarticHubbardD quarticHubbardField
    quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w

private theorem quartic_native_potential :
    auxPotential quarticHubbardU quarticHubbardFeature quarticHubbardD quarticHubbardField
      (DGPS.haar 1) = fun w => quarticPsi_FIN066 (WithLp.toLp 2 w) := by
  funext w
  rw [quartic_hubbard_aux_potential]
  congr 1
  ext i
  fin_cases i <;> rfl

private theorem quartic_native_potential_smooth :
    ContDiff ℝ ∞ (auxPotential quarticHubbardU quarticHubbardFeature quarticHubbardD
      quarticHubbardField (DGPS.haar 1)) := by
  rw [quartic_native_potential]
  exact quartic_potential_contDiff.comp PiLp.contDiff_toLp

private theorem quartic_native_gradient_coordinate (w : Fin 2 → ℝ) (i : Fin 2) :
    auxGrad quarticHubbardD quarticHubbardField quarticHubbardU quarticHubbardFeature
      (DGPS.haar 1) w i =
      fderiv ℝ (auxPotential quarticHubbardU quarticHubbardFeature quarticHubbardD
        quarticHubbardField (DGPS.haar 1)) w (Pi.single i 1) := by
  rw [(hasFDerivAt_auxPotential quartic_hubbard_hyp quartic_hubbard_D_posDef quarticHubbardField w).fderiv,
    dotCLM_apply]
  fin_cases i <;> simp [Fin.sum_univ_two, Pi.single_apply]

theorem quarticConditionalFieldMean_smooth : ContDiff ℝ ∞ quarticConditionalFieldMean := by
  have hg : ContDiff ℝ ∞ (auxGrad quarticHubbardD quarticHubbardField
      quarticHubbardU quarticHubbardFeature (DGPS.haar 1)) := by
    apply contDiff_pi.mpr
    intro i
    have he : (fun w => auxGrad quarticHubbardD quarticHubbardField
        quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w i) =
        fun w => fderiv ℝ (auxPotential quarticHubbardU quarticHubbardFeature quarticHubbardD
          quarticHubbardField (DGPS.haar 1)) w (Pi.single i 1) :=
      funext fun w => quartic_native_gradient_coordinate w i
    rw [he]
    exact (quartic_native_potential_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  unfold quarticConditionalFieldMean mulVec dotProduct
  exact contDiff_id.sub (contDiff_pi.mpr fun i =>
    ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_apply ℝ ℝ j).comp hg))

theorem quarticConditionalFieldMean_remote :
    quarticConditionalFieldMean ![-4, 0] = ![-4, 0] := by
  let T : (Fin 2 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm
  have hT0 : T ![-4, 0] = !₂[-4, 0] := by
    ext i
    fin_cases i <;> rfl
  have hz : fderiv ℝ (auxPotential quarticHubbardU quarticHubbardFeature quarticHubbardD
      quarticHubbardField (DGPS.haar 1)) ![-4, 0] = 0 := by
    rw [quartic_native_potential]
    change fderiv ℝ (quarticPsi_FIN066 ∘ T) ![-4, 0] = 0
    rw [fderiv_comp _ ((quartic_potential_contDiff.differentiable (by simp)) _)
      T.differentiableAt, hT0, critical_quarticPsi_FIN066 remote_neg_four_FIN066]
    exact ContinuousLinearMap.zero_comp _
  have hg : auxGrad quarticHubbardD quarticHubbardField quarticHubbardU
      quarticHubbardFeature (DGPS.haar 1) ![-4, 0] = 0 := by
    ext i
    rw [quartic_native_gradient_coordinate, hz]
    rfl
  simp only [quarticConditionalFieldMean, hg, mulVec_zero, sub_zero]

/-- Actual local Lipschitz control of the conditional field mean at the remote
critical point; no differentiated remainder estimate is assumed. -/
theorem quartic_conditional_mean_local_bound :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ w : Fin 2 → ℝ, ‖w - ![-4, 0]‖ ≤ r →
      ‖quarticConditionalFieldMean w - ![-4, 0]‖ ≤ C * ‖w - ![-4, 0]‖ := by
  have hC1 : ContDiff ℝ 1 quarticConditionalFieldMean :=
    quarticConditionalFieldMean_smooth.of_le (by simp)
  obtain ⟨K, U, hU, hLip⟩ := hC1.contDiffAt.exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε / 2, (K : ℝ) + 1, by positivity, by positivity, fun w hw => ?_⟩
  have hwU : w ∈ U := hball (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
  have hzU : (![-4, 0] : Fin 2 → ℝ) ∈ U := hball (Metric.mem_ball_self hε)
  have h := hLip.dist_le_mul w hwU ![-4, 0] hzU
  rw [quarticConditionalFieldMean_remote, dist_eq_norm, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by simp) (norm_nonneg _))

/-- Genuine product-law conditional mean and coordinate variance, uniform in the
field and particle number, for the actual empirical field. -/
theorem quartic_conditional_field_moments :
    ∃ V : ℝ, 0 < V ∧ ∀ N : ℕ+, ∀ w : Fin 2 → ℝ, ∀ j : Fin 2,
      (∫ x : ParticleSpace 1 N, posteriorCenter quarticHubbardD quarticHubbardField
          quarticHubbardFeature N x j
        ∂(Measure.pi fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w)) =
          quarticConditionalFieldMean w j ∧
      (∫ x : ParticleSpace 1 N, (posteriorCenter quarticHubbardD quarticHubbardField
          quarticHubbardFeature N x j - quarticConditionalFieldMean w j) ^ 2
        ∂(Measure.pi fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (DGPS.haar 1) w)) ≤
          V / (N : ℝ) := by
  obtain ⟨B, hB⟩ := quartic_hubbard_hyp.φ_bound
  let V := 2 * B ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, quarticHubbardD i j ^ 2) + 1
  refine ⟨V, by dsimp only [V]; positivity, fun N w j => ?_⟩
  constructor
  · exact integral_posteriorCenter quartic_hubbard_hyp quartic_hubbard_D_posDef quarticHubbardField N w j
  · have h := covariance_bound quartic_hubbard_hyp quartic_hubbard_D_posDef quarticHubbardField
      N w (Pi.single j 1) hB
    have hv : (2 * B ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, quarticHubbardD i j ^ 2)) /
        (N : ℝ) ≤ V / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      dsimp only [V]
      linarith
    refine le_trans ?_ hv
    fin_cases j <;> simpa [quarticConditionalFieldMean, dotProduct, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail] using h

end DGPS.FiniteN
