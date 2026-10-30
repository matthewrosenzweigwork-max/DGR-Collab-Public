import DGPS.Particle.Rates
import DGPS.Lipschitz.T01EnergyReplacement
import DGPS.Lipschitz.T01RootMoments
import DGPS.Lipschitz.T01ReferenceMoments
import DGPS.Lipschitz.T01GroundStateSchrodinger
import FullLabeledLSI.Paper.Prop23FAltB

/-!
# The actual Gibbs-to-reference comparison reduction

The rank inputs are limits of the actual chosen approximation: its values, force error,
normalizer and rate. The test is always an actual canonical particle Sobolev test. Rank is
chosen before the particle number and the observable; no bounded-comparison conclusion is
assumed among the rank inputs.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open SharpLSI SharpLSI.FL

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual comparison expression reduces to the actual particle entropy and energy. -/
theorem actual_reduce_J {d : ℕ} (J : InteractionData d) (hJ : LipschitzData J)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs J μ).measure = (μ : Measure (Torus d)))
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam)
    (hC1 : ∀ j, Gross.C1T (e j)) (F : FiniteRankApprox J.W μ e)
    (CR : ℕ → ℕ → ℕ → ℝ) {Kinf : ℝ} (hK0 : 0 < Kinf)
    (hKN : Tendsto (fun N : ℕ => centeredPartition J.W μ N) atTop (𝓝 Kinf))
    (hκ : Tendsto (fun R => kappaR F R) atTop (𝓝 Kinf))
    (hU : ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      Tendsto (fun R => ⨆ N ∈ {N : ℕ | 1 ≤ N},
        eLpNorm (fun X => Ucentered J.W μ N X - URN F R N X) q (QN μ N)) atTop (𝓝 0))
    (hforce : ∀ η : ℝ, 0 < η → ∃ R₁ : ℕ, ∀ R ≥ R₁, ∀ᶠ N : ℕ+ in atTop,
      (∫⁻ X, ENNReal.ofReal (gradSqC
        (fun Y => centeredParticlePotential J μ N Y - URN F R N Y) X) ∂particleLaw J N) ≤
          ENNReal.ofReal η)
    {b0 : ℝ} (hb0 : 0 ≤ b0)
    (hbR : Tendsto (fun R => (bRate (μ : Measure (Torus d)) lam (CR R)).toReal) atTop (𝓝 b0))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hC : ∀ N : ℕ+, ∫ X, centeredParticleDensity J μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C)
    (B E0 : ℝ) (hB0 : 0 ≤ B) (hE0 : 0 ≤ E0) :
    ∀ ε : ℝ, 0 < ε → ∃ R₁ : ℕ, ∀ R ≥ R₁, ∀ᶠ N : ℕ+ in atTop,
      ∀ f : ParticleH1 J N, (∀ X, |f X| ≤ B) → particleEnergy J N f ≤ E0 →
        Jexpr F lam (CR R) R (centeredParticleRoot J μ N f) - ε ≤
          particleEnergy J N f - b0 / 2 * (particleEntropy J N f).toReal := by
  intro ε hε
  let P := frozenGibbs J μ
  have hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal P.upper • haar d := by
    rw [← hfix]; exact P.measure_le_smul_haar
  have hlow : haar d ≤ ENNReal.ofReal P.lower⁻¹ • (μ : Measure (Torus d)) := by
    rw [← hfix]; exact P.haar_le_smul_measure
  have hac : (μ : Measure (Torus d)) ≪ haar d := Measure.absolutelyContinuous_of_le_smul hup
  have heC : ∀ j, e j =ᵐ[haar d] e j := fun _ => EventuallyEq.refl _ _
  let M2 : ℝ := B ^ (2 * p) * C
  let ME : ℝ := B ^ 2 * |Real.log (B ^ 2)| + 1
  have hME0 : 0 ≤ ME := by dsimp [ME]; positivity
  let ε₃ : ℝ := ε / (2 * (b0 + 1))
  have hε₃ : 0 < ε₃ := by dsimp [ε₃]; positivity
  let ζ : ℝ := min 1 (ε / (2 * (ME + 1)))
  have hζ : 0 < ζ := lt_min one_pos (by positivity)
  obtain ⟨η, hη, henergy⟩ := actual_root_energy_replacement_threshold J hJ μ hfix B E0
    (ε / 4) (by positivity)
  obtain ⟨R1, hR1⟩ := hforce η hη
  obtain ⟨R2, hR2⟩ := entropy_terms_replace F hK0 hKN hκ hU hp M2 ε₃ hε₃
  obtain ⟨R3, hR3⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hbR) ζ hζ)
  refine ⟨max (max R1 R2) R3, fun R hR => ?_⟩
  have hRa : R1 ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have hRb : R2 ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hRc : R3 ≤ R := (le_max_right _ _).trans hR
  have hbζ : |(bRate (μ : Measure (Torus d)) lam (CR R)).toReal - b0| ≤ ζ := by
    have h := hR3 R hRc
    rw [Real.dist_eq] at h
    exact h.le
  have hbR0 : 0 ≤ (bRate (μ : Measure (Torus d)) lam (CR R)).toReal := ENNReal.toReal_nonneg
  have hbR1 : (bRate (μ : Measure (Torus d)) lam (CR R)).toReal ≤ b0 + 1 := by
    have hζ1 : ζ ≤ 1 := min_le_left _ _
    linarith [(abs_le.1 hbζ).2]
  have hE2 := GroundState.integral_VNR_sub_vR_small hac he hC1 heC F R hp M2
    (ε / 4) (by positivity)
  have hT2 := tendsto_PNat_val_atTop_atTop.eventually (hR2 R hRb)
  have hT3 := tendsto_PNat_val_atTop_atTop.eventually hE2
  filter_upwards [hR1 R hRa, hT2, hT3] with N hI hN2 hN3 f hB hE
  let Ψ := centeredParticleRoot J μ N f
  obtain ⟨gΨ, hgΨ⟩ := centeredParticleRoot_memH1 J hJ μ N f
  have hΨH := (legacy_particle_reference_form P hgΨ).1
  rw [hfix] at hΨH
  have hΨ2 : MemLp Ψ 2 (QN (μ : Measure (Torus d)) N) := Spectral.memLp_of_H1 hΨH
  have hΨp : ∫⁻ X, ENNReal.ofReal (|Ψ X| ^ (2 * p)) ∂QN (μ : Measure (Torus d)) N ≤
      ENNReal.ofReal M2 := centeredParticleRoot_higher_moment J μ N hp hB0 f hB (hC N)
  have h1 := henergy N f (URN F R N) ⟨_, isWeakGrad_URN F hC1 heC R N.pos⟩
    (Eventually.of_forall hB) hE hI
  obtain ⟨-, h2⟩ := GroundState.schrodinger_identity hup hlow he hC1 heC F R N.pos hΨH
  have h3 := hN3 Ψ hΨ2.aestronglyMeasurable hΨp
  have h4 := centeredParticleRoot_entropy J μ hfix N f
    (isParticleWeakGradient_particleWeakGradient f).memLp (Eventually.of_forall hB)
  have hfEnt := FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent
    (isParticleWeakGradient_particleWeakGradient f).memLp.integrable_sq
  have hΨEnt := FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hΨ2.integrable_sq
  have hKn : centeredParticleNormalizer J μ N = centeredPartition J.W μ N := by
    rw [centeredParticleNormalizer_eq_integral J μ hfix N]
    simp only [centeredPartition, t01_centeredParticlePotential_eq_legacy]
  change (homogeneousEntropy (particleLaw J N) (fun X => f.1 X ^ 2)).toReal =
    (homogeneousEntropy (QN (μ : Measure (Torus d)) N) (fun X => Ψ X ^ 2)).toReal +
      (∫ X, Ψ X ^ 2 * centeredParticlePotential J μ N X ∂QN (μ : Measure (Torus d)) N) +
      Real.log (centeredParticleNormalizer J μ N) *
        (∫ X, Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N) at h4
  rw [hfEnt, hΨEnt, hKn] at h4
  have h5 := hN2 Ψ hΨ2.aestronglyMeasurable hΨp
  rw [← t01_centeredParticlePotential_eq_legacy J μ N] at h5
  obtain ⟨MU, hMU⟩ := isCompact_univ.exists_bound_of_continuousOn
    (centeredParticlePotential_continuous J μ N).continuousOn
  have hUBM : BM (centeredParticlePotential J μ N) :=
    ⟨⟨MU, fun X => by simpa only [Real.norm_eq_abs] using hMU X (Set.mem_univ X)⟩,
      (centeredParticlePotential_continuous J μ N).measurable⟩
  have iU := fa_integrable_sq_mul hΨ2 hUBM (EventuallyEq.refl _ _)
  have iR : Integrable (fun X => Ψ X ^ 2 * URN F R N X) (QN (μ : Measure (Torus d)) N) :=
    fa_integrable_sq_mul hΨ2 (fa_BM_uR hC1 F R N) (EventuallyEq.refl _ _)
  have iV := fa_integrable_sq_mul hΨ2 (fa_BM_VNR hC1 F lam R N) (EventuallyEq.refl _ _)
  have iv := fa_integrable_sq_mul hΨ2 (fa_BM_vR hC1 F lam R N) (EventuallyEq.refl _ _)
  have hsubV : (∫ X, Ψ X ^ 2 * (VNR F lam e R N X - vR F lam R (fun n => fluct e N n X))
      ∂QN (μ : Measure (Torus d)) N) =
      (∫ X, VNR F lam e R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N) -
      ∫ X, Ψ X ^ 2 * vR F lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N := by
    simp_rw [mul_sub]
    rw [integral_sub iV iv]
    simp_rw [mul_comm (Ψ _ ^ 2)]
  have hsubU : (∫ X, Ψ X ^ 2 * (centeredParticlePotential J μ N X - URN F R N X)
      ∂QN (μ : Measure (Torus d)) N) =
      (∫ X, Ψ X ^ 2 * centeredParticlePotential J μ N X ∂QN (μ : Measure (Torus d)) N) -
      ∫ X, Ψ X ^ 2 * URN F R N X ∂QN (μ : Measure (Torus d)) N := by
    simp_rw [mul_sub]
    exact integral_sub iU iR
  rw [hsubV] at h3
  rw [hsubU] at h5
  have hEgle := fa_ent_sq_toReal_le (particleLaw J N)
    (isParticleWeakGradient_particleWeakGradient f).memLp.aestronglyMeasurable
    (Eventually.of_forall hB)
  change Jexpr F lam (CR R) R Ψ - ε ≤ particleEnergy J N f -
    b0 / 2 * (homogeneousEntropy (particleLaw J N) (fun X => f X ^ 2)).toReal
  rw [hfEnt]
  have key := fa_alg (a1 := particleEnergy J N f)
    (shR := (shEn (μ : Measure (Torus d)) Ψ (URN F R N)).toReal)
    (rE := (refEnergy (μ : Measure (Torus d)) Ψ).toReal)
    (IV := ∫ X, VNR F lam e R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N)
    (IVe := ∫ X, Ψ X ^ 2 * vR F lam R (fun n => fluct e N n X) ∂QN (μ : Measure (Torus d)) N)
    (eQ := (ent (QN (μ : Measure (Torus d)) N) (fun X => Ψ X ^ 2)).toReal)
    (IU := ∫ X, Ψ X ^ 2 * URN F R N X ∂QN (μ : Measure (Torus d)) N)
    (IUN := ∫ X, Ψ X ^ 2 * centeredParticlePotential J μ N X ∂QN (μ : Measure (Torus d)) N)
    (lg := Real.log (kappaR F R)) (lK := Real.log (centeredPartition J.W μ N))
    (m := ∫ X, Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N)
    (Eg := (ent (particleLaw J N) (fun X => f X ^ 2)).toReal)
    (ε₁ := ε / 4) (ε₂ := ε / 4) (ε₃ := ε₃) (η := ζ) (ME := ME)
    (bR := (bRate (μ : Measure (Torus d)) lam (CR R)).toReal) (b0 := b0)
    h1 h2 h3 h4 h5 ENNReal.toReal_nonneg hEgle hbR0 hbR1 hbζ hζ.le
  have hsum : ε / 4 + ε / 4 + (b0 + 1) / 2 * ε₃ + ζ / 2 * ME ≤ ε := by
    have e1 : (b0 + 1) / 2 * ε₃ = ε / 4 := by dsimp [ε₃]; field_simp; ring
    have e2 : ζ / 2 * ME ≤ ε / 4 := by
      have hζ1 : ζ ≤ ε / (2 * (ME + 1)) := min_le_right _ _
      calc ζ / 2 * ME ≤ ε / (2 * (ME + 1)) / 2 * ME := by gcongr
        _ ≤ ε / 4 := by
          rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hε, hME0]
    linarith
  have key' : Jexpr F lam (CR R) R Ψ -
      (ε / 4 + ε / 4 + (b0 + 1) / 2 * ε₃ + ζ / 2 * ME) ≤
        particleEnergy J N f - b0 / 2 * (ent (particleLaw J N) (fun X => f X ^ 2)).toReal := key
  exact (sub_le_sub_left hsum (Jexpr F lam (CR R) R Ψ)).trans key'

end DGPS.Lipschitz
