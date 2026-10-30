import DGPS.Lipschitz.T01SymmetricLower
import DGPS.Lipschitz.DualGenerator

/-!
# The canonical Haar Gibbs square-root gradient

The centered Hamiltonian identity binds the frozen reference drift and the actual centered
particle force to the canonical particle density. This is the density multiplier used in the
conditional-score argument.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace DGPS.Lipschitz

open DGPS.Particle DGPS.Particle.ProductForceFisher

variable {d : ℕ}

theorem particleHamiltonian_centered_weakGradient (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+)
    {gμ : Torus d → Tangent d}
    (hμ : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) gμ)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU) :
    IsParticleHaarWeakGradient N (particleHamiltonian A N)
      (fun x i => gμ (x i) + gU x i) := by
  classical
  have hs := dg_sum (N := N) (Finset.univ : Finset (Fin N))
    (fun i _ => dg_slot i hμ)
  have h := dg_add (dg_add hs hU) (dg_const (N := N) (-(N : ℝ) * DGPS.meanInteraction A μ / 2))
  convert h using 1
  · funext x
    rw [particleHamiltonian_eq_centered]
    ring
  · funext x i
    simp [Finset.sum_apply]

theorem sqrt_particleDensity_eq (A : InteractionData d) (N : ℕ+)
    (x : ParticleSpace d N) :
    Real.sqrt (particleDensity A N x) = (Real.sqrt (particlePartition A N))⁻¹ *
      Real.exp (-particleHamiltonian A N x / 2) := by
  have hE : Real.exp (-particleHamiltonian A N x) =
      Real.exp (-particleHamiltonian A N x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [particleDensity, ← div_eq_inv_mul, Real.sqrt_div (Real.exp_pos _).le, hE,
    Real.sqrt_sq (Real.exp_pos _).le, div_eq_mul_inv, mul_comm]

theorem sqrt_particleDensity_weakGradient (A : InteractionData d)
    (N : ℕ+)
    {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (particleHamiltonian A N) g) :
    IsParticleHaarWeakGradient N (fun x => Real.sqrt (particleDensity A N x))
      (fun x => (-Real.sqrt (particleDensity A N x) / 2) • g x) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hU ⊢
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (particleHamiltonian_continuous A N).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (fun _ => 0) (Set.mem_univ _))
  have hab : -M < M + 1 := by linarith
  have hrng : ∀ z : Torus ((N : ℕ) * d),
      particleHamiltonian A N ((particleTorusEquiv d N).symm z) ∈ Icc (-M) (M + 1) := by
    intro z
    have h := hM ((particleTorusEquiv d N).symm z) (Set.mem_univ _)
    rw [Real.norm_eq_abs, abs_le] at h
    exact ⟨h.1, by linarith [h.2]⟩
  let F : ℝ → ℝ := fun t => (Real.sqrt (particlePartition A N))⁻¹ *
    Real.exp (-t / 2)
  have hFd : ContDiffOn ℝ ∞ F (Icc (-M) (M + 1)) :=
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))).contDiffOn
  have hch := chain_rule_of_cont_rep hU
    ((particleHamiltonian_continuous A N).comp continuous_particleTorusEquiv_symm)
    (Eventually.of_forall fun _ => rfl) hab hrng hFd
  have hderiv : ∀ t ∈ Icc (-M) (M + 1), derivWithin F (Icc (-M) (M + 1)) t =
      -F t / 2 := by
    intro t ht
    have hd : HasDerivAt F
        ((Real.sqrt (particlePartition A N))⁻¹ *
          (Real.exp (-t / 2) * (-1 / 2))) t := by
      simpa only [F, id_eq, Pi.neg_apply, neg_div] using
        (((hasDerivAt_id t).neg.div_const 2).exp.const_mul
          (Real.sqrt (particlePartition A N))⁻¹)
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)]
    dsimp only [F]
    ring
  rw [particleGradT_smul]
  refine hch.congr_ae (Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · exact (sqrt_particleDensity_eq A N _).symm
  · simp only [Function.comp_apply, hderiv _ (hrng z), F,
      sqrt_particleDensity_eq]

/-- The exact canonical square-root score, with the actual reference and centered gradients. -/
theorem sqrt_particleDensity_centered_weakGradient (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+)
    {gμ : Torus d → Tangent d}
    (hμ : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) gμ)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU) :
    IsParticleHaarWeakGradient N (fun x => Real.sqrt (particleDensity A N x))
      (fun x => (-Real.sqrt (particleDensity A N x) / 2) • (fun i => gμ (x i) + gU x i)) :=
  sqrt_particleDensity_weakGradient A N (particleHamiltonian_centered_weakGradient A μ N hμ hU)

end DGPS.Lipschitz
