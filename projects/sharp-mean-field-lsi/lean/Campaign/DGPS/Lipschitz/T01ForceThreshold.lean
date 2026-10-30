import DGPS.Lipschitz.T01ParticleReferenceBridge
import DGPS.Lipschitz.T01SymmetricLower

/-! Identification of the actual residual weak force and the chosen legacy force energy. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

/-- A genuine current particle gradient computes the chosen legacy gradient energy under
its actual Gibbs law. Fixed-N equivalence is sufficient; no uniform density bound is used. -/
theorem actual_legacy_force_integral_eq {d : ℕ} (J : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs J μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    {u : ParticleSpace d N → ℝ} {g : ParticleSpace d N → Fin N → Tangent d}
    (hg : IsParticleHaarWeakGradient N u g) :
    (∫⁻ X, ENNReal.ofReal (SharpLSI.gradSqC u X) ∂particleLaw J N) =
      ENNReal.ofReal (∫ X, particleTangentNormSq (g X) ∂particleLaw J N) := by
  have hae := (legacy_particle_reference_form (frozenGibbs J μ) hg).2.1
  rw [hfix] at hae
  have hac : particleLaw J N ≪ Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
    rw [particleLaw_eq_centered_reference J μ hfix N]
    exact withDensity_absolutelyContinuous _ _
  have hsq : (fun X => SharpLSI.gradSqC u X) =ᵐ[particleLaw J N]
      (fun X => particleTangentNormSq (g X)) := by
    filter_upwards [hac.ae_le hae] with X hX
    simp only [SharpLSI.gradSqC, hX, particleTangentNormSq_eq]
  have heq : (fun X => ENNReal.ofReal (SharpLSI.gradSqC u X)) =ᵐ[particleLaw J N]
      (fun X => ENNReal.ofReal (particleTangentNormSq (g X))) :=
    hsq.mono fun X hX => congrArg ENNReal.ofReal hX
  rw [lintegral_congr_ae heq]
  have hi := integrable_particleTangentNormSq
    ((DGPS.Particle.memLp_particleLaw_iff J N).2 hg.memLp_grad)
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun X => particleTangentNormSq_nonneg' (g X))).symm

/-- Retained upper boundedness turns the real force limsup into the exact nested rank and
particle threshold. The gradient is a genuine current weak gradient of the actual residual. -/
theorem actual_force_threshold_of_real_limsup {d : ℕ} (J : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs J μ).measure = (μ : Measure (Torus d)))
    (u : (R : ℕ) → (N : ℕ+) → ParticleSpace d N → ℝ)
    (g : (R N : ℕ) → (Fin N → Torus d) → Fin N → Tangent d)
    (hg : ∀ R N, IsParticleHaarWeakGradient N (u R N) (g R N))
    (P : (N : ℕ) → Measure (Fin N → Torus d))
    (hP : ∀ N : ℕ+, P N = particleLaw J N)
    (hbd : ∀ R, IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ => ∫ X, particleTangentNormSq (g R N X) ∂P N))
    (hlim : Tendsto (fun R => limsup
      (fun N : ℕ => ∫ X, particleTangentNormSq (g R N X) ∂P N) atTop) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ᶠ N : ℕ+ in atTop,
      (∫⁻ X, ENNReal.ofReal (SharpLSI.gradSqC (u R N) X) ∂particleLaw J N) ≤
        ENNReal.ofReal η := by
  intro η hη
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hη))
  refine ⟨R₀, fun R hR => ?_⟩
  have hev := Filter.eventually_lt_of_limsup_lt (hR₀ R hR) (hbd R)
  filter_upwards [tendsto_PNat_val_atTop_atTop.eventually hev] with N hN
  rw [actual_legacy_force_integral_eq J μ hfix N (hg R N)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [hP N] using hN.le

end DGPS.Lipschitz
