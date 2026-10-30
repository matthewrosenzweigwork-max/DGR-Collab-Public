import DGPS.Lipschitz.T01ParticleTiltData
import DGPS.Lipschitz.T01KernelGradientBridge
import DGPS.Lipschitz.T01FiniteRankBridge
import DGPS.Lipschitz.T01ReferenceEigenbasis
import DGPS.Particle.ConditionalForceReplacement
import FullLabeledLSI.Paper.Sec5LNDefs

/-!
# Factual score data for the actual positive particle tilt

The inherited score record is constructed from the canonical normalized density, the genuine
centered kernel and separately differentiated diagonal. Measurable score representatives are
selected explicitly; no pointwise regularity of the chosen Sobolev gradient is assumed.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

variable {d : ℕ}

/-- The reference representative agrees literally with the inherited coordinate `lipGrad`. -/
theorem actual_frozen_lipGrad_isWeakGradient (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) :
    IsWeakGradient (frozenPotential A (μ : Measure (Torus d)))
      (RelativeFisher.lipGradVec (frozenPotential A (μ : Measure (Torus d)))) := by
  obtain ⟨L, hL0, hL⟩ := lipschitz_equilibriumPotential A hA
  have hΦ := hL (μ : Measure (Torus d))
  have hc := frozenPotential_continuous A (μ : Measure (Torus d))
  have hG : MemLp (RelativeFisher.lipGradVec (frozenPotential A (μ : Measure (Torus d))))
      2 (haar d) := by
    refine memLp_piLp_iff.mpr fun j => ?_
    exact (MemLp.of_bound (SharpLSI.measurable_lipGrad hc j).aestronglyMeasurable
      (Real.toNNReal (L * Real.sqrt d) : ℝ) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact RelativeFisher.abs_lipGradVec_le hΦ x j)).mono_exponent le_top
  exact isWeakGradient_of_legacy_pair (RelativeFisher.isWeakGrad_lipGradVec hΦ)
    (memLp_two_of_continuous hc) hG

/-- The current slice derivative is the inherited force on the genuine product measure. -/
theorem actual_bForce_ae (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d))) :
    ∀ᵐ p ∂(haar d).prod (haar d), ∀ k,
      SharpLSI.bForce A.W (μ : Measure (Torus d)) p.1 p.2 k = D.G1 p.1 p.2 k := by
  have hDs : D.K = SharpLSI.centeredKernel A.W (μ : Measure (Torus d)) :=
    hD.trans (legacy_centeredKernel_eq A (μ : Measure (Torus d))).symm
  have hp := legacy_pair_weakGrad_ae (μ := haar d) (Measure.AbsolutelyContinuous.refl _) D
  have hpair := (measurePreserving_finTwoArrow (haar d)).symm.quasiMeasurePreserving.ae hp
  rw [hDs] at hpair
  filter_upwards [hpair] with p hp
  intro k
  change SharpLSI.weakGradC (SharpLSI.kerC2 (SharpLSI.centeredKernel A.W (μ : Measure (Torus d))))
      ![p.1, p.2] 0 k = D.G1 p.1 p.2 k
  exact (hp k).1

/-- Both current and inherited weak derivatives equal the exact centered force, including
one half of the separately differentiated diagonal. -/
theorem actual_centered_Gpart_data (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {gδ : Torus d → Tangent d} (hδ : IsWeakGradient (fun x => D.K x x) gδ) (N : ℕ+) :
    IsParticleHaarWeakGradient N (centeredParticlePotential A μ N)
      (fun X i => WithLp.toLp 2 (fun k => SharpLSI.FL.Gpart
        (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) N X i k)) ∧
    (∀ᵐ X ∂particleHaar d N, ∀ i k,
      SharpLSI.weakGradC (SharpLSI.Ucentered A.W (μ : Measure (Torus d)) N) X i k =
        SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) N X i k) := by
  have hK : ∀ x y, D.K x y = D.K y x := by
    rw [hD]
    exact centeredKernel_symm A (μ : Measure (Torus d))
  have hDK : D.K = DGPS.centeredKernel A μ := hD
  have h := kernel_Gpart_isParticleHaarWeakGradient D hK hδ N
  have hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N)
      (fun X i => WithLp.toLp 2 (fun k => SharpLSI.FL.Gpart
        (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) N X i k)) := by
    unfold centeredParticlePotential
    simpa only [hDK, one_div] using h
  refine ⟨hU, ?_⟩
  have hw := legacy_isWeakGrad_of_particle hU
  have hae := SharpLSI.weakGrad_ae_unique (SharpLSI.isWeakGrad_weakGrad ⟨_, hw⟩) hw
  have hflat : MeasurePreserving (SharpLSI.flat : SharpLSI.Config N d →
      UnitAddTorus (Fin N × Fin d)) (particleHaar d N) volume :=
    ⟨SharpLSI.measurable_flat, SharpLSI.map_flat_volume (N : ℕ)⟩
  have hpot : centeredParticlePotential A μ N =
      SharpLSI.Ucentered A.W (μ : Measure (Torus d)) N := by
    funext X
    simp only [centeredParticlePotential, SharpLSI.Ucentered, legacy_centeredKernel_eq]
    rfl
  rw [hpot] at hae
  filter_upwards [hflat.quasiMeasurePreserving.ae hae] with X hX
  intro i k
  exact congrFun hX (i, k)

/-- All fields of the actual normalized tilted-law score record are produced here. -/
theorem exists_actual_tilt_scoreData (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) (D : KData d)
    (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    (gδ : Torus d → Tangent d) (hδm : Measurable gδ) (M : ℝ)
    (hδb : ∀ x, ‖gδ x‖ ≤ M) (hδ : IsWeakGradient (fun x => D.K x x) gδ)
    (N : ℕ+) (f : ParticleH1 A N) (hfm : Measurable (f : ParticleSpace d N → ℝ))
    {c C : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x) (hfC : ∀ x, f x ≤ C) :
    ∃ (a b : ℝ)
      (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
      (s : Fin N → Fin d → ParticleSpace d N → ℝ),
      IsProbabilityMeasure (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) ∧
      SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d))
        (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) (positiveParticleTiltDensity f)
        a b GQ s (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) (|D.B| + |M|) ∧
      (∀ i k, s i k =ᵐ[SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)]
        fun X => (2 / f X) * particleWeakGradient f X i k) := by
  let Q := positiveParticleTiltDensity f
  let ν := SharpLSI.FL.qMeasure Q
  obtain ⟨hQm, a, b, ha, hab, hQb, hQi, hQmass⟩ :=
    positiveParticleTilt_density_data f hfm hc hfc hfC
  have hνprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    change (particleHaar d N).withDensity (fun X => ENNReal.ofReal (Q X)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hQi
        (Eventually.of_forall fun X => ha.le.trans (hQb X).1), hQmass]
    simp
  letI : IsProbabilityMeasure ν := hνprob
  have hνac : ν ≪ particleHaar d N := withDensity_absolutelyContinuous _ _
  have hνle : ν ≤ ENNReal.ofReal b • particleHaar d N := by
    rw [← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun X => ENNReal.ofReal_le_ofReal (hQb X).2)
  let v := RelativeFisher.lipGradVec (frozenPotential A (μ : Measure (Torus d)))
  have hv := actual_frozen_lipGrad_isWeakGradient A hA μ
  obtain ⟨hU, hUae⟩ := actual_centered_Gpart_data A μ D hD hδ N
  obtain ⟨G, hGm, hG2, hGcoord, hG, hGlegacy, hGscore⟩ :=
    positiveParticleTilt_gradient_data f hc hfc hfC μ hv hU
  have hfH := (isParticleWeakGradient_iff A N _ _).1
    (isParticleWeakGradient_particleWeakGradient f)
  let F := hfH.memLp_grad.aestronglyMeasurable.mk (particleWeakGradient f)
  have hFae : particleWeakGradient f =ᵐ[particleHaar d N] F :=
    hfH.memLp_grad.aestronglyMeasurable.ae_eq_mk
  have hFm : Measurable F := hfH.memLp_grad.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hF2 : MemLp F 2 (particleHaar d N) := hfH.memLp_grad.ae_eq hFae
  let s : Fin N → Fin d → ParticleSpace d N → ℝ := fun i k X => (2 / f X) * F X i k
  have hsm : ∀ i k, Measurable (s i k) := fun i k =>
    (measurable_const.div hfm).mul ((EuclideanSpace.proj k : Tangent d →L[ℝ] ℝ).measurable.comp
      ((measurable_pi_apply i).comp hFm))
  have hcoef : MemLp (fun X => (2 : ℝ) / f X) ∞ ν :=
    MemLp.of_bound (measurable_const.div hfm).aestronglyMeasurable (2 / c)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (div_pos two_pos (hc.trans_le (hfc X)))]
        exact div_le_div_of_nonneg_left zero_le_two hc (hfc X))
  have hs2 : ∀ i k, MemLp (s i k) 2 ν := fun i k => hcoef.mul (r := 2)
    ((memLp_piLp_iff.mp (memLp_pi_iff.mp hF2 i) k).of_measure_le_smul ENNReal.ofReal_ne_top hνle)
  let GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ :=
    fun y p => G (SharpLSI.unflat y) p.1 p.2
  have hflat : MeasurePreserving (SharpLSI.flat : SharpLSI.Config N d →
      UnitAddTorus (Fin N × Fin d)) (particleHaar d N) volume :=
    ⟨SharpLSI.measurable_flat, SharpLSI.map_flat_volume (N : ℕ)⟩
  have hunflat : MeasurePreserving (SharpLSI.unflat : UnitAddTorus (Fin N × Fin d) →
      ParticleSpace d N) volume (particleHaar d N) :=
    MeasurePreserving.symm (SharpLSI.flatEquiv N d) hflat
  have hGQm : ∀ p, Measurable (fun y => GQ y p) := fun p =>
    (hGcoord p.1 p.2).1.comp SharpLSI.measurable_unflat
  have hGQ2 : ∀ p, MemLp (fun y => GQ y p) 2 volume := fun p =>
    (hGcoord p.1 p.2).2.comp_measurePreserving hunflat
  have hSae : ∀ i k, s i k =ᵐ[ν] fun X => (2 / f X) * particleWeakGradient f X i k := by
    intro i k
    filter_upwards [hνac.ae_le hFae] with X hX
    exact congrArg (fun w : Fin N → Tangent d => (2 / f X) * w i k) hX.symm
  refine ⟨a, b, GQ, s, hνprob, ?_, hSae⟩
  refine ⟨rfl, ⟨hQm, ha, fun X => (hQb X).1, fun X => (hQb X).2⟩,
    hGlegacy, hGQm, hGQ2, kernel_force_rep D hδm hδb, actual_bForce_ae A μ D hD,
    hUae, hsm, fun i k => (hs2 i k).integrable_sq, ?_⟩
  filter_upwards [hνac.ae_le hGscore, hνac.ae_le hFae] with X hGX hFX
  intro i k
  have hQ0 : Q X ≠ 0 := (ha.trans_le (hQb X).1).ne'
  change G X i k / Q X = s i k X - _ - _
  rw [hGX]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hFX]
  change Q X * ((2 / f X) * F X i k -
      (SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W (μ : Measure (Torus d))) (X i) k +
        SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) N X i k)) / Q X =
    (2 / f X) * F X i k -
      SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) N X i k -
      SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W (μ : Measure (Torus d))) (X i) k
  have hf0 : f X ≠ 0 := (hc.trans_le (hfc X)).ne'
  field_simp [hQ0, hf0]
  <;> ring

/-- Direct Lipschitz data construct the diagonal representative and every score-record field
for the fixed actual centered kernel `D`, rather than assuming a score record. -/
theorem exists_actual_particle_scoreData (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) (D : KData d)
    (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    (N : ℕ+) (f : ParticleH1 A N) (hfm : Measurable (f : ParticleSpace d N → ℝ))
    {c C : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x) (hfC : ∀ x, f x ≤ C) :
    ∃ (gδ : Torus d → Tangent d) (M a b : ℝ)
      (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
      (s : Fin N → Fin d → ParticleSpace d N → ℝ),
      Measurable gδ ∧ (∀ x, ‖gδ x‖ ≤ M) ∧ IsWeakGradient (fun x => D.K x x) gδ ∧
      IsProbabilityMeasure (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) ∧
      SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d))
        (SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)) (positiveParticleTiltDensity f)
        a b GQ s (fun x y k => D.G1 x y k) (fun x k => gδ x k / 2) (|D.B| + |M|) ∧
      (∀ i k, s i k =ᵐ[SharpLSI.FL.qMeasure (positiveParticleTiltDensity f)]
        fun X => (2 / f X) * particleWeakGradient f X i k) := by
  obtain ⟨gδ, hδm, ⟨M, hδb⟩, hδ⟩ :=
    exists_centeredKernel_diagonal_gradient A hA (μ : Measure (Torus d))
  have hδD : IsWeakGradient (fun x => D.K x x) gδ := by
    rw [hD]
    exact hδ
  obtain ⟨a, b, GQ, s, hprob, hscore, hsae⟩ := exists_actual_tilt_scoreData A hA μ D hD
    gδ hδm M hδb hδD N f hfm hc hfc hfC
  exact ⟨gδ, M, a, b, GQ, s, hδm, hδb, hδD, hprob, hscore, hsae⟩

end DGPS.Lipschitz
