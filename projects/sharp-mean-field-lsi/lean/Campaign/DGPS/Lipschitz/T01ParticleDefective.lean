import DGPS.Lipschitz.T01LargeNDefective
import DGPS.Lipschitz.T01ParticleTiltNormalization
import DGPS.Lipschitz.T01DefectiveDomainClosure
import DGPS.Lipschitz.T01SymmetricDefectiveDomainClosure

/-!
# Eventual defective inequalities on the full canonical particle domain

The normalized-law estimate is multiplied by the exact square mass, using the unscaled
particle energy. Positive bounded tests are a proof stage only. The canonical-domain closure
then includes zeros, merely a.e. measurable representatives and infinite-entropy competitors.
The assertions are on a uniform tail of particle numbers; no finite-prefix bound is asserted.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

/-- Exact conversion of the actual normalized tilt estimate back to the particle test.
The entropy finiteness needed for real-valued arithmetic follows from the bounded test. -/
theorem particle_defective_of_normalized_tilt_bound {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) (hfm : Measurable (f : ParticleSpace d N → ℝ))
    {c C r K : ℝ} (hc : 0 < c) (hfc : ∀ X, c ≤ f X) (hfC : ∀ X, f X ≤ C)
    (hr : 0 < r) (hK : 0 ≤ K)
    (hbound : 2 * r *
      (klDiv (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) (particleLaw A N)).toReal ≤
        4 * particleEnergy A N f / (∫ X, f X ^ 2 ∂particleLaw A N) + K) :
    particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) +
      ENNReal.ofReal (K / (2 * r)) * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N := by
  let Z := ∫ X, f X ^ 2 ∂particleLaw A N
  let H := klDiv (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) (particleLaw A N)
  have hZ : 0 < Z := positiveParticleTilt_mass_pos f hc hfc
  have hEnt : particleEntropy A N f ≠ ⊤ := positiveParticleTilt_entropy_ne_top f hc hfc hfC
  have hKLreal : H.toReal = Z⁻¹ * (particleEntropy A N f).toReal := by
    change (klDiv (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) (particleLaw A N)).toReal = _
    rw [positiveParticleTilt_klDiv f hfm hc hfc, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hZ.le)]
    rfl
  have hEntZ : (particleEntropy A N f).toReal = Z * H.toReal := by
    rw [hKLreal, ← mul_assoc, mul_inv_cancel₀ hZ.ne', one_mul]
  have hreal : (particleEntropy A N f).toReal ≤
      (2 / r) * particleEnergy A N f + (K / (2 * r)) * Z := by
    rw [hEntZ]
    have hH : H.toReal ≤ (4 * particleEnergy A N f / Z + K) / (2 * r) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * r)]
      linarith [hbound]
    calc Z * H.toReal ≤ Z * ((4 * particleEnergy A N f / Z + K) / (2 * r)) :=
          mul_le_mul_of_nonneg_left hH hZ.le
      _ = _ := by field_simp [hZ.ne', hr.ne']; ring
  have hMass : ENNReal.ofReal Z = ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N :=
    ofReal_integral_eq_lintegral_ofReal (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
      (Eventually.of_forall fun X => sq_nonneg _)
  have hB : 0 ≤ K / (2 * r) := by positivity
  have hE : 0 ≤ (2 / r) * particleEnergy A N f :=
    mul_nonneg (by positivity) (particleEnergy_nonneg f)
  calc
    particleEntropy A N f = ENNReal.ofReal (particleEntropy A N f).toReal :=
      (ENNReal.ofReal_toReal hEnt).symm
    _ ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f + (K / (2 * r)) * Z) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_add hE (mul_nonneg hB hZ.le), ENNReal.ofReal_mul hB, hMass]

/-- The actual species subrate gives an eventual uniform defective inequality for every
canonical particle test, with the original unscaled energy and no positivity restriction. -/
theorem t01_eventual_particle_defective {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) {r : ℝ} (hr : 0 < r)
    (hrr : ENNReal.ofReal r < speciesRate A b) :
    ∃ N₀ : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ+), N₀ ≤ N → ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N := by
  obtain ⟨μ, hmin⟩ := (DGPS.Structural.gibbsMinimizer_exists A hA b).2.1
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA (μ : Measure (Torus d))
  obtain ⟨gδ, hδm, ⟨Mδ, hδb⟩, hδ⟩ := exists_centeredKernel_diagonal_gradient A hA
    (μ : Measure (Torus d))
  have hδ' : IsWeakGradient (fun x => D.K x x) gδ := by rw [hD]; exact hδ
  obtain ⟨N₀, K, hK, hlarge⟩ :=
    t01_large_N_species_score_bound A hA hd b hrate μ hmin D hD gδ hδm Mδ hδb hδ' hr hrr
  refine ⟨N₀, K / (2 * r), by positivity, fun N hN f => ?_⟩
  apply particle_defective_of_positive_bounded A N (by positivity : 0 ≤ 2 / r) ?_ f
  intro g hgm c C hc hgc hgC
  obtain ⟨a, a', GQ, s, hprob, hscore, hsae⟩ :=
    exists_actual_tilt_scoreData A hA μ D hD gδ hδm Mδ hδb hδ' N g hgm hc hgc hgC
  letI := hprob
  have hfin := positiveParticleTilt_klDiv_ne_top g hgm hc hgc hgC
  have hbound := hlarge N hN (SharpLSI.FL.qMeasure (positiveParticleTiltDensity g))
    (positiveParticleTiltDensity g) a a' GQ s hscore hfin
  rw [positiveParticleTilt_fisherS g hgm hc hgc s hsae] at hbound
  exact particle_defective_of_normalized_tilt_bound g hgm hc hgc hgC hr hK hbound

/-- The actual scalar subrate gives the eventual uniform defective inequality on the full
canonical symmetric class. Symmetry is imposed a.e. on the original test, not pointwise. -/
theorem t01_eventual_symmetric_particle_defective {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) {r : ℝ} (hr : 0 < r)
    (hrr : ENNReal.ofReal r < scalarRate A b) :
    ∃ N₀ : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ+), N₀ ≤ N → ∀ f : ParticleH1 A N,
      IsSymmetricParticleTest f →
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N := by
  obtain ⟨μ, hmin⟩ := (DGPS.Structural.gibbsMinimizer_exists A hA b).2.1
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA (μ : Measure (Torus d))
  obtain ⟨gδ, hδm, ⟨Mδ, hδb⟩, hδ⟩ := exists_centeredKernel_diagonal_gradient A hA
    (μ : Measure (Torus d))
  have hδ' : IsWeakGradient (fun x => D.K x x) gδ := by rw [hD]; exact hδ
  obtain ⟨N₀, K, hK, hlarge⟩ :=
    t01_large_N_scalar_score_bound A hA hd b hrate μ hmin D hD gδ hδm Mδ hδb hδ' hr hrr
  refine ⟨N₀, K / (2 * r), by positivity, fun N hN f hsym => ?_⟩
  apply particle_symmetric_defective_of_positive_bounded A N (by positivity : 0 ≤ 2 / r) ?_ f hsym
  intro g hgm hgs c C hc hgc hgC
  obtain ⟨a, a', GQ, s, hprob, hscore, hsae⟩ :=
    exists_actual_tilt_scoreData A hA μ D hD gδ hδm Mδ hδb hδ' N g hgm hc hgc hgC
  letI := hprob
  have hfin := positiveParticleTilt_klDiv_ne_top g hgm hc hgc hgC
  have hbound := hlarge N hN (SharpLSI.FL.qMeasure (positiveParticleTiltDensity g))
    (positiveParticleTilt_symmetricMeasure g hgm hgs) (positiveParticleTiltDensity g)
    a a' GQ s hscore hfin
  rw [positiveParticleTilt_fisherS g hgm hc hgc s hsae] at hbound
  exact particle_defective_of_normalized_tilt_bound g hgm hc hgc hgC hr hK hbound

end DGPS.Lipschitz
