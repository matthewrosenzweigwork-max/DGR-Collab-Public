import DGPS.Particle.Contractions
import DGPS.Particle.Rates

/-!
# Particle representatives and truncation energy splitting for sharp-limit tightening

The abstract tightening theorem requires the sum of the truncated and tail energies to be
bounded by the original energy. Separate contraction inequalities do not imply this bound.
The weak-gradient chain rules give disjoint active regions, including a harmless zero-gradient
choice at the truncation level.

Measurable representatives preserve both energy and entropy, so restricting to the measurable
test class required by abstract tightening does not discard any Sobolev competitor.
-/

open MeasureTheory

namespace DGPS.Lipschitz

/-- Changing a particle test on a null set preserves its weak gradient. -/
theorem particleWeakGradient_congr_ae {d : ℕ} {A : InteractionData d} {N : ℕ+}
    {f g : ParticleSpace d N → ℝ} {G : ParticleSpace d N → Fin N → Tangent d}
    (hf : IsParticleWeakGradient A N f G) (hfg : f =ᵐ[particleLaw A N] g) :
    IsParticleWeakGradient A N g G where
  memLp := hf.memLp.ae_eq hfg
  memLp_grad := hf.memLp_grad
  ibp φ hφ i j := by
    have hhaar : f =ᵐ[particleHaar d N] g :=
      (Particle.particleHaar_absolutelyContinuous A N).ae_le hfg
    calc
      ∫ x, g x * particlePartial i j φ x ∂particleHaar d N =
          ∫ x, f x * particlePartial i j φ x ∂particleHaar d N :=
        integral_congr_ae (hhaar.mono fun x hx =>
          congrArg (fun a : ℝ => a * particlePartial i j φ x) hx.symm)
      _ = -∫ x, G x i j * φ x ∂particleHaar d N := hf.ibp φ hφ i j

/-- Both quantities used by the particle Rayleigh quotient depend only on the a.e. test. -/
theorem particleEnergy_entropy_congr_ae {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f g : ParticleH1 A N) (hfg : f.1 =ᵐ[particleLaw A N] g.1) :
    particleEnergy A N f = particleEnergy A N g ∧
      particleEntropy A N f = particleEntropy A N g := by
  constructor
  · exact (particleEnergy_eq_of_isParticleWeakGradient g
      (particleWeakGradient_congr_ae (isParticleWeakGradient_particleWeakGradient f) hfg)).symm
  · apply homogeneousEntropy_congr_ae
    exact hfg.mono fun x hx => congrArg (fun t : ℝ => t ^ 2) hx

/-- The measurable-test class used by abstract tightening loses no particle competitor,
including in the permutation-invariant subspace. -/
theorem exists_measurable_particleH1_representative {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f : ParticleH1 A N) :
    ∃ g : ParticleH1 A N, Measurable g.1 ∧ f.1 =ᵐ[particleLaw A N] g.1 ∧
      particleEnergy A N f = particleEnergy A N g ∧
      particleEntropy A N f = particleEntropy A N g ∧
      (IsSymmetricParticleTest f ↔ IsSymmetricParticleTest g) := by
  have hf := isParticleWeakGradient_particleWeakGradient f
  let hm := hf.memLp.aestronglyMeasurable
  let v := hm.mk f.1
  have hfv : f.1 =ᵐ[particleLaw A N] v := hm.ae_eq_mk
  let g : ParticleH1 A N := ⟨v, _, particleWeakGradient_congr_ae hf hfv⟩
  obtain ⟨hE, hEnt⟩ := particleEnergy_entropy_congr_ae f g hfv
  exact ⟨g, hm.stronglyMeasurable_mk.measurable, hfv, hE, hEnt,
    isSymmetricParticleTest_congr hfv⟩

/-- The two truncation pieces have disjoint weak-gradient supports. This supplies the
`hsplit` input of `Analysis.abstract_eventual_exact_lsi_after_defect_removal` for particle tests.
It requires neither positivity of the test nor positivity of the cutoff. -/
theorem particleEnergy_truncation_split {d : ℕ} {A : InteractionData d} {N : ℕ+}
    (f fmin ftail : ParticleH1 A N) (c : ℝ)
    (hmin : fmin.1 = fun x => min (f.1 x) c)
    (htail : ftail.1 = fun x => max (f.1 x - c) 0) :
    particleEnergy A N fmin + particleEnergy A N ftail ≤ particleEnergy A N f := by
  have hg := isParticleWeakGradient_particleWeakGradient f
  have hgmin := hg.min_const c
  have hgtail : IsParticleWeakGradient A N (fun x => max (f.1 x - c) 0)
      (fun x => if c < f.1 x then particleWeakGradient f x else 0) := by
    simpa only [one_mul, one_smul, ← sub_eq_add_neg, sub_pos] using
      (hg.affine 1 (-c)).max_const 0
  rw [← hmin] at hgmin
  rw [← htail] at hgtail
  rw [particleEnergy_eq_of_isParticleWeakGradient fmin hgmin,
    particleEnergy_eq_of_isParticleWeakGradient ftail hgtail,
    particleEnergy_eq_of_isParticleWeakGradient f hg]
  rw [← integral_add (integrable_particleTangentNormSq hgmin.memLp_grad)
    (integrable_particleTangentNormSq hgtail.memLp_grad)]
  apply integral_mono
    ((integrable_particleTangentNormSq hgmin.memLp_grad).add
      (integrable_particleTangentNormSq hgtail.memLp_grad))
    (integrable_particleTangentNormSq hg.memLp_grad)
  intro x
  change particleTangentNormSq (if f.1 x < c then particleWeakGradient f x else 0) +
    particleTangentNormSq (if c < f.1 x then particleWeakGradient f x else 0) ≤
    particleTangentNormSq (particleWeakGradient f x)
  by_cases hlt : f.1 x < c
  · have hnlt : ¬ c < f.1 x := not_lt.mpr hlt.le
    simp only [hlt, hnlt, ↓reduceIte, particleTangentNormSq, Pi.zero_apply, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, add_zero, le_refl]
  · by_cases hgt : c < f.1 x
    · simp only [hlt, hgt, ↓reduceIte, particleTangentNormSq, Pi.zero_apply, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero, zero_add, le_refl]
    · simp only [hlt, hgt, ↓reduceIte, particleTangentNormSq, Pi.zero_apply, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero, add_zero]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end DGPS.Lipschitz
