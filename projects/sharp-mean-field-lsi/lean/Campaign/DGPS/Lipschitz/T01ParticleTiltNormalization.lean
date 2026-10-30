import DGPS.Lipschitz.T01ActualScoreData

/-!
# Exact entropy and Fisher normalization for the actual particle tilt

The real normalized Haar density is the same measure as the squared-test tilt of the
canonical particle law. The entropy and score constants are therefore the actual ones.
-/

open MeasureTheory Filter InformationTheory
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ} {A : InteractionData d} {N : ℕ+}

theorem positiveParticleTilt_eq_withDensity (f : ParticleH1 A N)
    (hfm : Measurable (f : ParticleSpace d N → ℝ)) :
    SharpLSI.FL.qMeasure (positiveParticleTiltDensity f) =
      (particleLaw A N).withDensity (fun X => ENNReal.ofReal
        (f X ^ 2 / ∫ y, f y ^ 2 ∂particleLaw A N)) := by
  rw [particleLaw, ← withDensity_mul₀
    (Particle.particleDensity_measurable A N).ennreal_ofReal.aemeasurable
    ((hfm.pow_const 2).div_const _).ennreal_ofReal.aemeasurable]
  change (particleHaar d N).withDensity _ = (particleHaar d N).withDensity _
  congr 1
  funext X
  change ENNReal.ofReal (f X ^ 2 * particleDensity A N X / _) =
    ENNReal.ofReal (particleDensity A N X) * ENNReal.ofReal (f X ^ 2 / _)
  rw [← ENNReal.ofReal_mul (Particle.particleDensity_pos A N X).le]
  congr 1
  dsimp only [particleLaw]
  ring

theorem integral_positiveParticleTilt (f : ParticleH1 A N)
    (hfm : Measurable (f : ParticleSpace d N → ℝ)) (h : ParticleSpace d N → ℝ) :
    ∫ X, h X ∂SharpLSI.FL.qMeasure (positiveParticleTiltDensity f) =
      (∫ y, f y ^ 2 ∂particleLaw A N)⁻¹ *
        ∫ X, f X ^ 2 * h X ∂particleLaw A N := by
  let Z := ∫ y, f y ^ 2 ∂particleLaw A N
  have hZ : 0 ≤ Z := integral_nonneg fun X => sq_nonneg _
  rw [positiveParticleTilt_eq_withDensity f hfm,
    integral_withDensity_eq_integral_toReal_smul₀
      ((hfm.pow_const 2).div_const Z).ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) hZ), smul_eq_mul]
  have he : (fun X => f X ^ 2 / Z * h X) = fun X => Z⁻¹ * (f X ^ 2 * h X) := by
    funext X
    ring
  rw [he, integral_const_mul]

theorem positiveParticleTilt_klDiv (f : ParticleH1 A N)
    (hfm : Measurable (f : ParticleSpace d N → ℝ))
    {c : ℝ} (hc : 0 < c) (hfc : ∀ X, c ≤ f X) :
    klDiv (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) (particleLaw A N) =
      ENNReal.ofReal (∫ X, f X ^ 2 ∂particleLaw A N)⁻¹ *
        homogeneousEntropy (particleLaw A N) (fun X => f X ^ 2) := by
  let P := particleLaw A N
  let ν := SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)
  let Z := ∫ X, f X ^ 2 ∂P
  have hZ : 0 < Z := positiveParticleTilt_mass_pos f hc hfc
  have hi : Integrable (fun X => f X ^ 2) P :=
    (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
  have hν : ν = P.withDensity (fun X => ENNReal.ofReal (f X ^ 2 / Z)) :=
    positiveParticleTilt_eq_withDensity f hfm
  have hρm : Measurable (fun X => ENNReal.ofReal (f X ^ 2 / Z)) :=
    ((hfm.pow_const 2).div_const Z).ennreal_ofReal
  have hprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hi.div_const Z)
        (Eventually.of_forall fun X => div_nonneg (sq_nonneg _) hZ.le),
      integral_div, div_self hZ.ne']
    simp
  letI : IsProbabilityMeasure ν := hprob
  have hac : ν ≪ P := by rw [hν]; exact withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity P hρm
  have hsd : SharpLSI.sqrtDens ν P =ᵐ[P] fun X => (Real.sqrt Z)⁻¹ * |f X| := by
    filter_upwards [hrn] with X hX
    simp only [SharpLSI.sqrtDens]
    rw [hν, hX, ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) hZ.le),
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, div_eq_inv_mul]
  have hsq : ((Real.sqrt Z)⁻¹) ^ 2 = Z⁻¹ := by rw [inv_pow, Real.sq_sqrt hZ.le]
  rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hi]
  change klDiv ν P = ENNReal.ofReal Z⁻¹ * SharpLSI.ent P (fun X => f X ^ 2)
  rw [SharpLSI.klDiv_eq_ent hac, ← SharpLSI.ent_const_mul P hi (inv_nonneg.mpr hZ.le)]
  refine SharpLSI.ent_congr_ae ?_
  filter_upwards [hsd] with X hX
  rw [hX, mul_pow, hsq, sq_abs]

set_option backward.isDefEq.respectTransparency.types false in
/-- The measurable score selected by the factual record has precisely the unscaled
particle Fisher sum; no uniform constant is lost in the normalization. -/
theorem positiveParticleTilt_fisherS (f : ParticleH1 A N)
    (hfm : Measurable (f : ParticleSpace d N → ℝ))
    {c : ℝ} (hc : 0 < c) (hfc : ∀ X, c ≤ f X)
    (s : Fin N → Fin d → ParticleSpace d N → ℝ)
    (hsae : ∀ i k, s i k =ᵐ[SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)]
      fun X => (2 / f X) * particleWeakGradient f X i k) :
    SharpLSI.FL.fisherS (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) s =
      4 * particleEnergy A N f / (∫ X, f X ^ 2 ∂particleLaw A N) := by
  let Z := ∫ X, f X ^ 2 ∂particleLaw A N
  let ν := SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)
  have ht : ∀ i k, ∫ X, s i k X ^ 2 ∂ν =
      (4 / Z) * ∫ X, particleWeakGradient f X i k ^ 2 ∂particleLaw A N := by
    intro i k
    rw [integral_congr_ae ((hsae i k).mono fun X hX => congrArg (fun t : ℝ => t ^ 2) hX),
      integral_positiveParticleTilt f hfm]
    have he : (fun X => f X ^ 2 * ((2 / f X) * particleWeakGradient f X i k) ^ 2) =
        fun X => 4 * particleWeakGradient f X i k ^ 2 := by
      funext X
      have hf0 : f X ≠ 0 := (hc.trans_le (hfc X)).ne'
      field_simp [hf0]
      <;> ring
    rw [he, integral_const_mul]
    ring
  have hg := (isParticleWeakGradient_particleWeakGradient f).memLp_grad
  have hgi : ∀ i k, Integrable (fun X => particleWeakGradient f X i k ^ 2) (particleLaw A N) :=
    fun i k => (memLp_piLp_iff.mp (memLp_pi_iff.mp hg i) k).integrable_sq
  have hE : particleEnergy A N f = ∑ i, ∑ k, ∫ X, particleWeakGradient f X i k ^ 2
      ∂particleLaw A N := by
    rw [particleEnergy_eq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hgi i k]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun k _ => hgi i k
  change (∑ i, ∑ k, ∫ X, s i k X ^ 2 ∂ν) = 4 * particleEnergy A N f / Z
  calc
    _ = ∑ i, ∑ k, (4 / Z) *
        (∫ X, particleWeakGradient f X i k ^ 2 ∂particleLaw A N) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ht i k
    _ = (4 / Z) * ∑ i, ∑ k,
        (∫ X, particleWeakGradient f X i k ^ 2 ∂particleLaw A N) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [← hE]; ring

/-- Finiteness is proved directly from the bounded test, without a defective or sharp LSI. -/
theorem positiveParticleTilt_entropy_ne_top (f : ParticleH1 A N)
    {c C : ℝ} (hc : 0 < c) (hfc : ∀ X, c ≤ f X) (hfC : ∀ X, f X ≤ C) :
    homogeneousEntropy (particleLaw A N) (fun X => f X ^ 2) ≠ ⊤ := by
  have hf := (isParticleWeakGradient_particleWeakGradient f).memLp
  have hi := hf.integrable_sq
  have hlog := SharpLSI.FL.g2_integrable_mul_log_of_bdd (hf.aestronglyMeasurable.pow 2)
    (Eventually.of_forall fun X => sq_nonneg (f X))
    (Eventually.of_forall fun X => pow_le_pow_left₀ (hc.le.trans (hfc X)) (hfC X) 2)
  rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hi,
    SharpLSI.ent_eq_formula (particleLaw A N) _ (fun X => sq_nonneg _) hi hlog]
  exact ENNReal.ofReal_ne_top

/-- The actual normalized tilt has finite relative entropy, directly from its bounded test. -/
theorem positiveParticleTilt_klDiv_ne_top (f : ParticleH1 A N)
    (hfm : Measurable (f : ParticleSpace d N → ℝ))
    {c C : ℝ} (hc : 0 < c) (hfc : ∀ X, c ≤ f X) (hfC : ∀ X, f X ≤ C) :
    klDiv (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) (particleLaw A N) ≠ ⊤ := by
  rw [positiveParticleTilt_klDiv f hfm hc hfc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (positiveParticleTilt_entropy_ne_top f hc hfc hfC)

end DGPS.Lipschitz
