import DGPS.Lipschitz.T01UnrestrictedLower
import DGPS.Particle.Contractions
import SharpSymmetricLSI.Paper.Defective3
import FullLabeledLSI.Infra.SpectralEnergy

/-!
# The actual particle Sobolev domain in the legacy reference coordinates

Campaign particle gradients use `Fin (N*d)` coordinates. The legacy reference form uses
`Fin N × Fin d`. The explicit index equivalence transfers the weak equation, then uniqueness
identifies the chosen legacy gradient. No particle-number-uniform density bound is asserted.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Actual particle weak gradients satisfy the exact legacy flat-coordinate weak equation. -/
theorem legacy_isWeakGrad_of_particle {d : ℕ} {N : ℕ+} {f : ParticleSpace d N → ℝ}
    {g : ParticleSpace d N → Fin N → Tangent d} (h : IsParticleHaarWeakGradient N f g) :
    SharpLSI.IsWeakGrad (f ∘ SharpLSI.unflat)
      (fun y p => g (SharpLSI.unflat y) p.1 p.2) := by
  have hT := isParticleHaarWeakGradient_iff_weakGradient.1 h
  have hr (y : UnitAddTorus (Fin N × Fin d)) :
      SharpLSI.reidx (particleIdx d N) y = particleTorusEquiv d N (SharpLSI.unflat y) := by
    funext k
    rw [particleTorusEquiv_apply]
    rfl
  have he (y : UnitAddTorus (Fin N × Fin d)) :
      (particleTorusEquiv d N).symm (SharpLSI.reidx (particleIdx d N) y) =
        SharpLSI.unflat y := by rw [hr, MeasurableEquiv.symm_apply_apply]
  have hR := SharpLSI.isWeakGrad_reidx (particleIdx d N) hT.isWeakGrad
    (hT.memLp.integrable one_le_two)
    (fun k => (memLp_coord hT.memLp_grad k).integrable one_le_two)
  convert hR using 2 <;>
    simp only [Function.comp_apply, particleGradT_apply, he, Equiv.symm_apply_apply]

/-- Full actual particle Haar H1 lies in legacy H1 for the same bounded reference product;
the chosen legacy gradient and its energy are the actual particle gradient. -/
theorem legacy_particle_reference_form {d : ℕ} {N : ℕ+} (P : BoundedPositiveReference d)
    {f : ParticleSpace d N → ℝ} {g : ParticleSpace d N → Fin N → Tangent d}
    (h : IsParticleHaarWeakGradient N f g) :
    SharpLSI.MemH1C (Measure.pi fun _ : Fin N => P.measure) f ∧
      (∀ᵐ X ∂Measure.pi (fun _ : Fin N => P.measure), ∀ i j,
        SharpLSI.weakGradC f X i j = g X i j) ∧
      SharpLSI.FL.refEnergy P.measure f =
        ∫⁻ X, ENNReal.ofReal (particleTangentNormSq (g X))
          ∂Measure.pi (fun _ : Fin N => P.measure) := by
  have hT := isParticleHaarWeakGradient_iff_weakGradient.1 h
  let σ := particleIdx d N
  let G : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ :=
    fun y p => g (SharpLSI.unflat y) p.1 p.2
  have hw : SharpLSI.IsWeakGrad (f ∘ SharpLSI.unflat) G := legacy_isWeakGrad_of_particle h
  have hr (y : UnitAddTorus (Fin N × Fin d)) :
      SharpLSI.reidx σ y = particleTorusEquiv d N (SharpLSI.unflat y) := by
    funext k
    rw [particleTorusEquiv_apply]
    rfl
  have he (y : UnitAddTorus (Fin N × Fin d)) :
      (particleTorusEquiv d N).symm (SharpLSI.reidx σ y) = SharpLSI.unflat y := by
    rw [hr, MeasurableEquiv.symm_apply_apply]
  have hf2 : MemLp (f ∘ SharpLSI.unflat) 2
      (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
    convert hT.memLp.comp_measurePreserving (SharpLSI.measurePreserving_reidx_torus σ) using 1
    funext y
    exact congrArg f (he y).symm
  have hg2 : ∀ p, MemLp (fun y => G y p) 2
      (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
    intro p
    convert (memLp_coord hT.memLp_grad (σ p)).comp_measurePreserving
      (SharpLSI.measurePreserving_reidx_torus σ) using 1
    funext y
    change G y p = particleGradT g (SharpLSI.reidx σ y) (σ p)
    rw [particleGradT_apply, he]
    simp only [G, σ, Equiv.symm_apply_apply]
  have hGm : ∀ p, AEStronglyMeasurable (fun y => G y p)
      (volume : Measure (UnitAddTorus (Fin N × Fin d))) := fun p => (hg2 p).aestronglyMeasurable
  have hnorm : MemLp (fun y => Real.sqrt (SharpLSI.sqNorm (G y))) 2
      (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
    have hm : AEStronglyMeasurable (fun y => SharpLSI.sqNorm (G y)) volume := by
      unfold SharpLSI.sqNorm
      exact Finset.aestronglyMeasurable_fun_sum _ fun p _ => (hGm p).pow 2
    rw [memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hm)]
    refine (integrable_finsetSum (Finset.univ : Finset (Fin N × Fin d))
      fun p _ => (hg2 p).integrable_sq).congr (Eventually.of_forall fun y => ?_)
    exact (Real.sq_sqrt (Finset.sum_nonneg fun p _ => sq_nonneg (G y p))).symm
  have hae : SharpLSI.weakGrad (f ∘ SharpLSI.unflat) =ᵐ[volume] G :=
    SharpLSI.weakGrad_ae_unique (SharpLSI.isWeakGrad_weakGrad ⟨G, hw⟩) hw
  have hHaar : SharpLSI.MemH1 volume (f ∘ SharpLSI.unflat) :=
    ⟨⟨G, hw⟩, hf2, hnorm.ae_eq (hae.mono fun y hy => by
      change Real.sqrt (SharpLSI.sqNorm (G y)) =
        Real.sqrt (SharpLSI.sqNorm (SharpLSI.weakGrad (f ∘ SharpLSI.unflat) y))
      rw [hy])⟩
  have hle := SharpLSI.FL.Spectral.map_flat_pi_le P.measure_le_smul_haar (N : ℕ)
  have hmem : SharpLSI.MemH1C (Measure.pi fun _ : Fin N => P.measure) f :=
    ⟨hHaar.1, hHaar.2.1.of_measure_le_smul
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle,
      hHaar.2.2.of_measure_le_smul (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle⟩
  have hflat : MeasurePreserving (SharpLSI.flat : SharpLSI.Config N d →
      UnitAddTorus (Fin N × Fin d)) (particleHaar d N) volume :=
    ⟨SharpLSI.measurable_flat, SharpLSI.map_flat_volume (N : ℕ)⟩
  have hcfg : ∀ᵐ X ∂particleHaar d N, ∀ i j, SharpLSI.weakGradC f X i j = g X i j := by
    filter_upwards [hflat.quasiMeasurePreserving.ae hae] with X hX
    intro i j
    exact congrFun hX (i, j)
  have hQ : (Measure.pi fun _ : Fin N => P.measure) ≪ particleHaar d N :=
    Measure.absolutelyContinuous_of_le_smul
      (SharpLSI.FL.Spectral.pi_le_smul_pi P.measure_le_smul_haar (N : ℕ))
  have hcfgQ := hQ.ae_le hcfg
  refine ⟨hmem, hcfgQ, ?_⟩
  unfold SharpLSI.FL.refEnergy
  refine lintegral_congr_ae ?_
  filter_upwards [hcfgQ] with X hX
  congr 1
  simp only [SharpLSI.gradSqC, hX, particleTangentNormSq_eq]

end DGPS.Lipschitz
