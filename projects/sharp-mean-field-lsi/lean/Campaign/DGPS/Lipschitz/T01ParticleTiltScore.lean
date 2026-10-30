import DGPS.Lipschitz.T01ParticleDensityGradient

/-!
# The genuine normalized joint density and its particle score

For a positive bounded canonical Sobolev test, square the Haar root obtained by multiplying
the test by the square root of the actual particle density. The resulting normalized Haar
density has the expected score, with the true reference and centered particle derivatives.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open DGPS.Particle.ProductForceFisher

variable {d : ℕ} {A : InteractionData d} {N : ℕ+}

noncomputable def positiveParticleTiltDensity (f : ParticleH1 A N) : ParticleSpace d N → ℝ :=
  fun x => f x ^ 2 * particleDensity A N x / (∫ y, f y ^ 2 ∂particleLaw A N)

/-- The derivative is an actual distributional derivative of the normalized joint Haar
density, not a formal score identity. Positivity and boundedness are confined to this stage. -/
theorem positiveParticleTiltDensity_isWeakGradient (f : ParticleH1 A N)
    {c C : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x) (hfC : ∀ x, f x ≤ C)
    (μ : ProbabilityMeasure (Torus d))
    {gμ : Torus d → Tangent d}
    (hμ : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) gμ)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU) :
    IsParticleHaarWeakGradient N (positiveParticleTiltDensity f)
      (fun x => positiveParticleTiltDensity f x •
        (fun i => (2 / f x) • particleWeakGradient f x i - (gμ (x i) + gU x i))) := by
  let Z : ℝ := ∫ y, f y ^ 2 ∂particleLaw A N
  let p : ParticleSpace d N → ℝ := fun x => Real.sqrt (particleDensity A N x)
  let H : ParticleSpace d N → Fin N → Tangent d := fun x i => gμ (x i) + gU x i
  have hf := (isParticleWeakGradient_iff A N _ _).1
    (isParticleWeakGradient_particleWeakGradient f)
  have hfb : MemLp f.1 ∞ (particleHaar d N) :=
    memLp_top_of_bound hf.memLp.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hfc x))]
      exact hfC x)
  have hp := sqrt_particleDensity_centered_weakGradient A μ N hμ hU
  have hpc : Continuous p := Real.continuous_sqrt.comp (Particle.particleDensity_continuous A N)
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hpc.continuousOn
  have hpb : MemLp p ∞ (particleHaar d N) :=
    memLp_top_of_bound hpc.aestronglyMeasurable M
      (Eventually.of_forall fun x => hM x (Set.mem_univ x))
  have hR := isParticleHaarWeakGradient_mul_bdd hf hp hfb hpb
  have hRb : MemLp (fun x => f x * p x) ∞ (particleHaar d N) := hfb.mul (r := ∞) hpb
  have hSq := isParticleHaarWeakGradient_mul_bdd hR hR hRb hRb
  have hQ := dg_smul hSq Z⁻¹
  have hfun : (fun x => Z⁻¹ * ((f x * p x) * (f x * p x))) = positiveParticleTiltDensity f := by
    funext x
    have he : p x ^ 2 = particleDensity A N x := Real.sq_sqrt (Particle.particleDensity_pos A N x).le
    dsimp [positiveParticleTiltDensity]
    change Z⁻¹ * ((f x * p x) * (f x * p x)) = f x ^ 2 * particleDensity A N x / Z
    rw [← he]
    ring
  rw [hfun] at hQ
  have hgrad : (fun x => Z⁻¹ •
      ((f x * p x) • (p x • particleWeakGradient f x + f x • ((-p x / 2) • H x)) +
        (f x * p x) • (p x • particleWeakGradient f x + f x • ((-p x / 2) • H x)))) =
      (fun x => positiveParticleTiltDensity f x •
        (fun i => (2 / f x) • particleWeakGradient f x i - (gμ (x i) + gU x i))) := by
    funext x i
    apply WithLp.ofLp_injective
    funext k
    have hf0 : f x ≠ 0 := (hc.trans_le (hfc x)).ne'
    have he : p x ^ 2 = particleDensity A N x := Real.sq_sqrt (Particle.particleDensity_pos A N x).le
    change Z⁻¹ * ((f x * p x) *
        (p x * particleWeakGradient f x i k + f x * (-p x / 2 * (gμ (x i) k + gU x i k))) +
        (f x * p x) *
        (p x * particleWeakGradient f x i k + f x * (-p x / 2 * (gμ (x i) k + gU x i k)))) =
      (f x ^ 2 * particleDensity A N x / Z) *
        (2 / f x * particleWeakGradient f x i k - (gμ (x i) k + gU x i k))
    rw [← he]
    field_simp [hf0]
    <;> ring
  rw [← hgrad]
  exact hQ

end DGPS.Lipschitz
