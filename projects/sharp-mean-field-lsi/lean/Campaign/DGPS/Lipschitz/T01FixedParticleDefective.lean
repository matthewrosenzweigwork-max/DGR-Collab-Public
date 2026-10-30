import DGPS.Lipschitz.T01ParticleReferenceBridge
import DGPS.Particle.ProductForceFisher
import DGPS.Particle.Rates
import DGPS.Analysis.LSITensorization
import DGPS.FiniteN.Tools.Rothaus
import SharpSymmetricLSI.Paper.Defective2

/-!
# Fixed-particle defective entropy with any positive energy coefficient

The actual particle density is bounded above and below for fixed particle number. Transport
to the single torus and the Hyp-free weighted torus defective inequality give an arbitrary
positive coefficient on the original unscaled energy. The mass coefficient may depend on N.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open DGPS.Particle.ProductForceFisher

/-- A genuine fixed-N fallback, with no defective-inequality hypothesis and no semiconvexity. -/
theorem fixed_particle_defective {d : ℕ} (A : InteractionData d) (N : ℕ+)
    {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal (η * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N := by
  let P := particleReference A N
  let e := particleTorusEquiv d N
  have hP : P.measure = (particleLaw A N).map e := particleReference_measure A N
  have hcm : 0 < P.lower := P.lower_pos
  have hp : ∀ z, P.lower ≤ P.density z ∧ P.density z ≤ P.upper := fun z =>
    Particle.particleDensity_bounds A N (hamBound_spec A N) _
  have hcp : 0 < P.upper := Real.exp_pos _
  have ha : 0 < SharpLSI.aCos := by unfold SharpLSI.aCos; positivity
  let ε := min 1 (η * SharpLSI.aCos * P.lower / (2 * P.upper))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  refine ⟨P.upper * (Fintype.card (Fin ((N : ℕ) * d)) * (6 * Real.log (1 / ε))) / P.lower,
    fun f => ?_⟩
  let u := f.1 ∘ e.symm
  let G := particleGradT (particleWeakGradient f)
  have hf := isParticleWeakGradient_particleWeakGradient f
  have hT := isParticleHaarWeakGradient_iff_weakGradient.1
    ((isParticleWeakGradient_iff A N _ _).1 hf)
  have hw : SharpLSI.IsWeakGrad u (fun z k => G z k) := hT.isWeakGrad
  have hGp : MemLp G 2 P.measure :=
    hT.memLp_grad.of_measure_le_smul ENNReal.ofReal_ne_top P.measure_le_smul_haar
  have hup : MemLp u 2 P.measure :=
    hT.memLp.of_measure_le_smul ENNReal.ofReal_ne_top P.measure_le_smul_haar
  have hn : MemLp (fun z => Real.sqrt (SharpLSI.sqNorm (fun k => G z k))) 2 P.measure := by
    simpa only [← Analysis.norm_sq_eq_sqNorm, Real.sqrt_sq (norm_nonneg _)] using hGp.norm
  have hchosen : SharpLSI.weakGrad u =ᵐ[haar ((N : ℕ) * d)] (fun z k => G z k) :=
    SharpLSI.weakGrad_ae_unique (SharpLSI.isWeakGrad_weakGrad ⟨_, hw⟩) hw
  have hchosenP : SharpLSI.weakGrad u =ᵐ[P.measure] (fun z k => G z k) :=
    P.measure_ac_haar.ae_le hchosen
  have hu : SharpLSI.MemH1 P.measure u :=
    ⟨⟨_, hw⟩, hup, hn.ae_eq (hchosenP.mono fun z hz => by
      change Real.sqrt (SharpLSI.sqNorm (fun k => G z k)) = Real.sqrt (SharpLSI.sqNorm (SharpLSI.weakGrad u z))
      rw [hz])⟩
  letI : IsProbabilityMeasure ((volume : Measure (Torus ((N : ℕ) * d))).withDensity
      fun z => ENNReal.ofReal (P.density z)) :=
    (inferInstance : IsProbabilityMeasure P.measure)
  have hkey := SharpLSI.perturb_elsi P.lower_pos hp P.measurable_density hε hε1 hu
  have hdir : SharpLSI.dirichlet P.measure u = ENNReal.ofReal (particleEnergy A N f) := by
    unfold SharpLSI.dirichlet
    calc
      (∫⁻ z, ENNReal.ofReal (SharpLSI.sqNorm (SharpLSI.weakGrad u z)) ∂P.measure) =
          ∫⁻ z, ENNReal.ofReal (particleTangentNormSq (particleWeakGradient f (e.symm z))) ∂P.measure := by
        apply lintegral_congr_ae
        filter_upwards [hchosenP] with z hz
        rw [hz, ← Analysis.norm_sq_eq_sqNorm]
        congr 1
        have he := particleTangentNormSq_eq_norm_gradT (particleWeakGradient f) (e.symm z)
        simpa only [MeasurableEquiv.apply_symm_apply, G, e] using he.symm
      _ = ∫⁻ x, ENNReal.ofReal (particleTangentNormSq (particleWeakGradient f x)) ∂particleLaw A N := by
        rw [hP, e.measurableEmbedding.lintegral_map]
        simp only [MeasurableEquiv.symm_apply_apply]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal
        (integrable_particleTangentNormSq hf.memLp_grad)
        (Eventually.of_forall fun x => particleTangentNormSq_nonneg' _)).symm
  have hmass : (∫⁻ z, ENNReal.ofReal (u z ^ 2) ∂P.measure) =
      ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N := by
    rw [hP, e.measurableEmbedding.lintegral_map]
    simp only [u, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have hent : SharpLSI.ent P.measure (fun z => u z ^ 2) = particleEntropy A N f := by
    rw [particleEntropy, FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hf.memLp.integrable_sq]
    have hUm := hup.aestronglyMeasurable.pow 2
    rw [hP] at hUm
    have he := SharpLSI.ent_comp (particleLaw A N) e.measurable (u := fun z => u z ^ 2) hUm
    rw [← hP] at he
    simpa only [u, Function.comp_apply, MeasurableEquiv.symm_apply_apply] using he.symm
  change SharpLSI.ent P.measure (fun z => u z ^ 2) ≤
    ENNReal.ofReal (P.upper * (2 * ε / SharpLSI.aCos) / P.lower) *
      SharpLSI.dirichlet P.measure u +
      ENNReal.ofReal (P.upper * (Fintype.card (Fin ((N : ℕ) * d)) *
        (6 * Real.log (1 / ε))) / P.lower) *
      ∫⁻ z, ENNReal.ofReal (u z ^ 2) ∂P.measure at hkey
  rw [hent, hdir, hmass] at hkey
  rw [ENNReal.ofReal_mul hη.le]
  refine hkey.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl)
  have heps : ε ≤ η * SharpLSI.aCos * P.lower / (2 * P.upper) := min_le_right _ _
  rw [div_le_iff₀ P.lower_pos]
  calc
    P.upper * (2 * ε / SharpLSI.aCos) ≤
        P.upper * (2 * (η * SharpLSI.aCos * P.lower / (2 * P.upper)) / SharpLSI.aCos) := by gcongr
    _ = η * P.lower := by field_simp [hcp.ne', ha.ne']

end DGPS.Lipschitz
