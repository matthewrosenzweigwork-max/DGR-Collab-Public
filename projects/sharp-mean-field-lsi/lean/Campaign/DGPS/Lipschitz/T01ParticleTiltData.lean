import DGPS.Lipschitz.T01ParticleTiltScore
import DGPS.Lipschitz.T01ParticleReferenceBridge

/-!
# Actual normalized joint-density data

The normalization, two-sided bounds, and measurable gradient representative below are for the
canonical particle law and the actual tilted Sobolev test. The bounds are fixed-particle bounds.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ} {A : InteractionData d} {N : ℕ+}

theorem positiveParticleTilt_mass_pos (f : ParticleH1 A N)
    {c : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x) :
    0 < ∫ x, f x ^ 2 ∂particleLaw A N := by
  have hI := (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
  have hle : c ^ 2 ≤ ∫ x, f x ^ 2 ∂particleLaw A N := by
    simpa using integral_mono (integrable_const (c ^ 2)) hI
      (fun x => pow_le_pow_left₀ hc.le (hfc x) 2)
  exact (sq_pos_of_pos hc).trans_le hle

/-- The joint Haar density has genuine pointwise bounds and unit mass. -/
theorem positiveParticleTilt_density_data (f : ParticleH1 A N)
    (hfm : Measurable (f : ParticleSpace d N → ℝ))
    {c C : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x) (hfC : ∀ x, f x ≤ C) :
    Measurable (positiveParticleTiltDensity f) ∧
      ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
        (∀ x, a ≤ positiveParticleTiltDensity f x ∧ positiveParticleTiltDensity f x ≤ b) ∧
        Integrable (positiveParticleTiltDensity f) (particleHaar d N) ∧
        (∫ x, positiveParticleTiltDensity f x ∂particleHaar d N) = 1 := by
  let Z := ∫ x, f x ^ 2 ∂particleLaw A N
  have hZ : 0 < Z := positiveParticleTilt_mass_pos f hc hfc
  have hQm : Measurable (positiveParticleTiltDensity f) :=
    ((hfm.pow_const 2).mul (Particle.particleDensity_measurable A N)).div_const Z
  obtain ⟨l, u, hl, hlu, hρ⟩ := Particle.particleDensity_bounded A N
  let a := c ^ 2 * l / Z
  let b := C ^ 2 * u / Z
  have hbounds : ∀ x, a ≤ positiveParticleTiltDensity f x ∧ positiveParticleTiltDensity f x ≤ b := by
    intro x
    have hfx : 0 ≤ f x := hc.le.trans (hfc x)
    have hnuml : c ^ 2 * l ≤ f x ^ 2 * particleDensity A N x :=
      mul_le_mul (pow_le_pow_left₀ hc.le (hfc x) 2) (hρ x).1 hl.le (sq_nonneg _)
    have hnumu : f x ^ 2 * particleDensity A N x ≤ C ^ 2 * u :=
      mul_le_mul (pow_le_pow_left₀ hfx (hfC x) 2) (hρ x).2
        (Particle.particleDensity_pos A N x).le (sq_nonneg _)
    exact ⟨div_le_div_of_nonneg_right hnuml hZ.le, div_le_div_of_nonneg_right hnumu hZ.le⟩
  have ha : 0 < a := div_pos (mul_pos (sq_pos_of_pos hc) hl) hZ
  have hab : a ≤ b := (hbounds (fun _ => 0)).1.trans (hbounds (fun _ => 0)).2
  have hQi : Integrable (positiveParticleTiltDensity f) (particleHaar d N) :=
    Integrable.of_bound hQm.aestronglyMeasurable b
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans (hbounds x).1)]
        exact (hbounds x).2)
  refine ⟨hQm, a, b, ha, hab, hbounds, hQi, ?_⟩
  unfold positiveParticleTiltDensity
  rw [integral_div]
  have hnum : (∫ x, f x ^ 2 * particleDensity A N x ∂particleHaar d N) = Z := by
    simpa only [Z, mul_comm] using
      (Particle.integral_particleLaw A N (fun x => f x ^ 2)).symm
  rw [hnum, div_self hZ.ne']

/-- Select a globally measurable actual gradient, retaining the real weak equation, its
legacy coordinate equation, coordinate L2 bounds, and the genuine score identity a.e. -/
theorem positiveParticleTilt_gradient_data (f : ParticleH1 A N)
    {c C : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x) (hfC : ∀ x, f x ≤ C)
    (μ : ProbabilityMeasure (Torus d))
    {gμ : Torus d → Tangent d}
    (hμ : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) gμ)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU) :
    ∃ G : ParticleSpace d N → Fin N → Tangent d,
      Measurable G ∧ MemLp G 2 (particleHaar d N) ∧
      (∀ i j, Measurable (fun x => G x i j) ∧ MemLp (fun x => G x i j) 2 (particleHaar d N)) ∧
      IsParticleHaarWeakGradient N (positiveParticleTiltDensity f) G ∧
      SharpLSI.IsWeakGrad (positiveParticleTiltDensity f ∘ SharpLSI.unflat)
        (fun y p => G (SharpLSI.unflat y) p.1 p.2) ∧
      G =ᵐ[particleHaar d N]
        (fun x => positiveParticleTiltDensity f x •
          (fun i => (2 / f x) • particleWeakGradient f x i - (gμ (x i) + gU x i))) := by
  have h := positiveParticleTiltDensity_isWeakGradient f hc hfc hfC μ hμ hU
  let G0 : ParticleSpace d N → Fin N → Tangent d := fun x =>
    positiveParticleTiltDensity f x •
      (fun i => (2 / f x) • particleWeakGradient f x i - (gμ (x i) + gU x i))
  let G := h.memLp_grad.aestronglyMeasurable.mk G0
  have hae : G0 =ᵐ[particleHaar d N] G := h.memLp_grad.aestronglyMeasurable.ae_eq_mk
  have hGm : Measurable G := h.memLp_grad.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hG2 : MemLp G 2 (particleHaar d N) := h.memLp_grad.ae_eq hae
  have hG : IsParticleHaarWeakGradient N (positiveParticleTiltDensity f) G := by
    refine ⟨h.memLp, hG2, ?_⟩
    intro φ hφ i j
    rw [h.ibp φ hφ i j]
    congr 1
    exact integral_congr_ae (hae.mono fun x hx =>
      congrArg (fun w : Fin N → Tangent d => w i j * φ x) hx)
  refine ⟨G, hGm, hG2, ?_, hG, legacy_isWeakGrad_of_particle hG, hae.symm⟩
  intro i j
  exact ⟨(EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).measurable.comp
      ((measurable_pi_apply i).comp hGm),
    memLp_piLp_iff.mp (memLp_pi_iff.mp hG2 i) j⟩

end DGPS.Lipschitz
