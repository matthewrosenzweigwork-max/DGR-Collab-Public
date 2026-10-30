import DGPS.Lipschitz.T01ParticleTiltScore
import DGPS.Lipschitz.T01ConditionalSpecies
import DGPS.Particle.Symmetry
import DGPS.Variational.SpeciesInclusion

/-!
# Exchangeability and the genuine scalar conditional rate step

Symmetry is transferred from the actual Sobolev test to its actual joint Haar density.
Unrevealed conditional laws agree by uniqueness of disintegration. The rate inequality
uses the scalar rate and the force of the actual one-body conditional law.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

/-- The actual normalized density inherits the test's Haar a.e. symmetry. -/
theorem positiveParticleTiltDensity_symmetry {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) (hsym : IsSymmetricParticleTest f)
    (σ : Equiv.Perm (Fin N)) :
    (positiveParticleTiltDensity f ∘ permuteParticles σ) =ᵐ[particleHaar d N]
      positiveParticleTiltDensity f := by
  have hf := (isSymmetricParticleFun_iff_haar A N f.1).mp hsym σ
  filter_upwards [hf] with x hx
  change f (permuteParticles σ x) = f x at hx
  simp only [Function.comp_apply, positiveParticleTiltDensity,
    particleDensity_permute, hx]

/-- No everywhere-symmetric representative is required for symmetry of the actual law. -/
theorem positiveParticleTilt_symmetricMeasure {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) (hfm : Measurable (f : ParticleSpace d N → ℝ))
    (hsym : IsSymmetricParticleTest f) :
    SharpLSI.IsSymmetricMeasure (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) := by
  intro σ
  have hQm : Measurable (positiveParticleTiltDensity f) :=
    ((hfm.pow_const 2).mul (Particle.particleDensity_measurable A N)).div_const _
  change ((particleHaar d N).withDensity (fun x => ENNReal.ofReal
    (positiveParticleTiltDensity f x))).map (permuteEquiv σ) = _
  have hmap : (particleHaar d N).map (permuteEquiv σ) = particleHaar d N := by
    change (particleHaar d N).map (permuteParticles σ) = particleHaar d N
    exact (measurePreserving_permuteParticles d σ).map_eq
  rw [SharpLSI.map_withDensity_equiv (permuteEquiv σ) _ hQm.ennreal_ofReal, hmap]
  apply withDensity_congr_ae
  have h := positiveParticleTiltDensity_symmetry f hsym σ.symm
  exact h.fun_comp ENNReal.ofReal

/-- For an exchangeable law, any two unrevealed labels have the same conditional law.
The equality is a.e. in the law of the revealed coordinates. -/
theorem t01_condLawS_eq_of_symmetric {d N : ℕ}
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hsym : SharpLSI.IsSymmetricMeasure ν) (S : Finset (Fin N))
    {i j : Fin N} (hi : i ∉ S) (hj : j ∉ S) :
    SharpLSI.FL.condLawS ν S i =ᵐ[ν.map (SharpLSI.FL.restrictS S)]
      SharpLSI.FL.condLawS ν S j := by
  let σ := Equiv.swap i j
  let Y := SharpLSI.FL.restrictS S (d := d)
  have hY : Measurable Y := SharpLSI.FL.measurable_restrictS S
  have hT : Measurable (fun X : SharpLSI.Config N d => X ∘ σ) :=
    measurable_pi_iff.mpr fun k => measurable_pi_apply _
  have hfix : ∀ X : SharpLSI.Config N d, Y (X ∘ σ) = Y X := by
    intro X
    funext k
    change X (σ k.1) = X k.1
    congr 1
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ k.2))
      (fun h => hj (h ▸ k.2))
  have hpair : ν.map (fun X => (Y X, X i)) = ν.map (fun X => (Y X, X j)) := by
    calc
      ν.map (fun X => (Y X, X i)) =
          (ν.map (fun X => X ∘ σ)).map (fun X => (Y X, X i)) := by rw [hsym σ]
      _ = ν.map (fun X => (Y (X ∘ σ), (X ∘ σ) i)) :=
        Measure.map_map (hY.prodMk (measurable_pi_apply i)) hT
      _ = ν.map (fun X => (Y X, X j)) := by
        congr 1
        funext X
        rw [hfix]
        simp [σ]
  have hkey : ν.map (fun X => (Y X, X i)) =
      ν.map Y ⊗ₘ condDistrib (fun X => X j) Y ν := by
    rw [hpair, compProd_map_condDistrib hY.aemeasurable
      (measurable_pi_apply j).aemeasurable]
  exact condDistrib_ae_eq_of_measure_eq_compProd hY.aemeasurable
    (measurable_pi_apply i).aemeasurable hkey

/-- The scalar gap relative to the actual minimizing reference, with its exact centered
interaction correction. This is the one-species identity, without using a species subrate. -/
theorem t01_scalarGap_eq_reference_entropy {d : ℕ} (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)}
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A) (ρ : AbsoluteDensity d) :
    (scalarGap A ρ : ℝ) =
      (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
        t01CenteredCorrection A μ (densityMeasure ρ) := by
  have h := (speciesGap_eq_reference_entropy_correction A hμ (SpeciesFamily.single ρ)).2
  rw [speciesGap_single, densityMeasure_barycenter_single] at h
  change (scalarGap A ρ : ℝ) = (∑ _s : Fin 1,
    1 * (relativeEntropy (densityMeasure ρ : Measure (Torus d))
      (μ : Measure (Torus d))).toReal) + _ at h
  simpa using h

/-- The scalar subrate in actual density-score coordinates. The force belongs to the
same absolute density to which the scalar rate is applied. -/
theorem two_subrate_positive_scalar_score_le {d : ℕ}
    (A : InteractionData d) (b : AbsoluteDrift A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ scalarRate A b)
    (ρ : AbsoluteDensity d) {g : Torus d → Tangent d}
    (hg : IsWeakGradient ρ.density g) (hpos : ∀ x, 0 < ρ.density x) :
    ENNReal.ofReal (2 * r * (scalarGap A ρ : ℝ)) ≤
      ∫⁻ x, ENNReal.ofReal (ρ.density x *
        ‖(ρ.density x)⁻¹ • g x + b.force ρ x‖ ^ 2) ∂haar d := by
  refine (two_subrate_scalarGap_le A b hr hrr ρ).trans_eq ?_
  unfold scalarDissipation scalarScore
  exact lintegral_congr_ae ((positive_absolute_score_identity ρ hg hpos (b.force ρ)).fun_comp
    ENNReal.ofReal)

/-- Every unrevealed actual conditional density satisfies the scalar mean-field step.
This statement retains the actual density and weak derivative for later collision estimates. -/
theorem ae_conditional_scalar_score {d N : ℕ}
    (A : InteractionData d) (b : AbsoluteDrift A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ scalarRate A b)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    (hQm : Measurable Q) (hc : 0 < c) (hQc : ∀ X, c ≤ Q X) (hQC : ∀ X, Q X ≤ C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hQw : SharpLSI.IsWeakGrad (Q ∘ SharpLSI.unflat) GQ)
    (hGm : ∀ a, Measurable (fun y => GQ y a))
    (hG2 : ∀ a, MemLp (fun y => GQ y a) 2 volume)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (S : Finset (Fin N)) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ i, i ∉ S →
      ∃ ρ : AbsoluteDensity d,
        (∀ x, ρ.density x = SharpLSI.FL.condDensS Q S i a x) ∧
        ENNReal.ofReal (2 * r * (scalarGap A ρ : ℝ)) ≤
          ∫⁻ x, ENNReal.ofReal (SharpLSI.FL.condDensS Q S i a x *
            ‖(SharpLSI.FL.condDensS Q S i a x)⁻¹ •
              WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i a x) + b.force ρ x‖ ^ 2)
            ∂haar d := by
  let hQ : SharpLSI.FL.IsBddDens Q c C := ⟨hQm, hc, hQc, hQC⟩
  have hC : 0 < C := hc.trans_le ((hQc (Classical.arbitrary _)).trans (hQC _))
  filter_upwards [ae_conditional_absolute_density_gradient hQm hc hQc hQC hQw hGm hG2 ν hν S]
    with a ha
  intro i hi
  obtain ⟨ρ, hρ, hg⟩ := ha i hi
  refine ⟨ρ, hρ, ?_⟩
  have hpos : ∀ x, 0 < ρ.density x := fun x => by
    rw [hρ]
    exact (div_pos hc hC).trans_le (SharpLSI.FL.condDensS_bounds hQ S i a x).1
  simpa only [hρ] using two_subrate_positive_scalar_score_le A b hr hrr ρ hg hpos

end DGPS.Lipschitz
