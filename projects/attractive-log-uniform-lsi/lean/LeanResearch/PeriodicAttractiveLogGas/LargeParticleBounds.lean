import LeanResearch.PeriodicAttractiveLogGas.GlobalInequalityParameters

/-! The two uniform large-particle inputs in the final source proof.
All kernel, occupation, mesh and far-imbalance choices are discharged.
The remaining finite-particle input is deliberately not assumed here. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace PeriodicAttractiveLogGas.LargeParticleBounds
open GlobalInequalityParameters ResolutionEnergy

/-- Both constants and the one particle threshold are chosen before N and
beta. The energy is the unscaled sum of the actual physical gradients. -/
theorem exists_large_particle_bounds {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) :
    ∃ Cpi A B : ℝ, 0 ≤ Cpi ∧ 0 ≤ A ∧ 0 ≤ B ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ f : C(Configuration N, ℝ), ∀ K : ℝ≥0,
          LipschitzWith K (fun y ↦ f (configurationQuotient N y)) →
            variance f (gibbsMeasure greenRealRepresentative N β) ≤ Cpi * energy β f ∧
            entropy (gibbsMeasure greenRealRepresentative N β) (fun X ↦ f X ^ 2) ≤
              ((A * energy β f + B * squareIntegral β f : ℝ) : EReal) := by
  obtain ⟨P⟩ := exists_parameters hβ₀
  obtain ⟨cFar, hcFar, NFar, hNFar, hfar⟩ := StationaryUniqueness.exists_FarImbalance
    hsub P.t_pos P.t_lt.le P.mesh
  let Cpi : ℝ := max 0 (GlobalPoincare.poincareConstant P.J β₀ P.t)
  let A : ℝ := GlobalDefectiveEntropy.energyCoefficient P.J β₀ P.t P.C₂ cFar
  let B : ℝ := GlobalDefectiveEntropy.massCoefficient P.J β₀ P.t P.C₂ cFar
  let N₀ : ℕ := max NFar (max (GlobalPoincare.particleThreshold P.J β₀ P.t cFar)
    (GlobalDefectiveEntropy.particleThreshold P.J β₀ P.t cFar))
  obtain ⟨hA, hB⟩ := GlobalDefectiveEntropy.coefficients_nonneg
    (ConditionalLawEstimates.mesh_pos P.mesh) hβ₀ hsub P.t_pos P.kernel_nonneg hcFar
  refine ⟨Cpi, A, B, le_max_left _ _, hA, hB, N₀,
    hNFar.trans (le_max_left _ _), ?_⟩
  intro N hN β hβ hβle f K hf
  have hNF : NFar ≤ N := (le_max_left _ _).trans hN
  have hNP : GlobalPoincare.particleThreshold P.J β₀ P.t cFar ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNE : GlobalDefectiveEntropy.particleThreshold P.J β₀ P.t cFar ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hfarN := (hfar N hNF).2 β hβ hβle
  constructor
  · have hh := GlobalPoincare.global_poincare_of_far hβ hβle hsub P.t_pos P.t_lt
      P.mesh P.heavy_mesh P.near_mesh P.inverse_mesh hcFar hNP hfarN f hf
    rw [configurationLipschitzAmbient_energy_eq_integral] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (energy_nonneg β f))
  · exact GlobalDefectiveEntropy.global_defective_entropy_of_far hβ hβle hsub
      P.kernel_nonneg P.kernel_bound P.mesh P.residual_mesh P.t_pos P.t_lt
      P.residual_small P.reference_scale P.reference_small P.near_mesh P.heavy_mesh P.inverse_mesh
      hcFar hNE hfarN f hf

end PeriodicAttractiveLogGas.LargeParticleBounds
