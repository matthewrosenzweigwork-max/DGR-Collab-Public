import DGRHS.Kinetic.SpatialGibbsEntropy
import DGRHS.Kinetic.Maxwellian
import DGRHS.Commutator.SourceRieszCommonEntropy

/-! Source492--496: the actual positive-Riesz entropic estimate on phase space.
Constants are chosen before velocity space/law, N and joint competitor.
The physical moment hypotheses are discharged by the source Riesz factory;
finite full Gibbs KL derives the proper entropy-plus-energy domain. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Kinetic
open DGRHS.Gaussian DGRHS.Commutator DGRHS.CLT
universe w
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszKineticProperFreeEnergy {V : Type w} [MeasurableSpace V]
    (ρ : E → ℝ) (s β : ℝ) (N : ℕ) (η : Measure V)
    (ν : Measure ((Fin N → E) × V)) : ℝ :=
  (klDiv ν ((Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)).prod η)).toReal /
    (β*(N : ℝ)) + (N : ℝ)⁻¹*(∫ z, sourceRieszTransportBackgroundEnergy ρ s N z.1 ∂ν)

theorem sourceRiesz_kinetic_finiteKL_entropic
    (s M : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hs : 0 < s) (hd : 2*s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M)
    (β : ℝ) (hβ : 0 < β) :
    ∃ Cpf Cem : ℝ, 1 ≤ Cpf ∧ 1 ≤ Cem ∧
      ∀ (K : ℝ≥0) (v : E → E), LipschitzWith K v →
      0 < sourceRieszPositiveTransportParameter (ι := ι) s M n K β ∧
      ∀ (ρ : E → ℝ), IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) →
      (∀ᵐ x ∂volume, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
      ∀ (V : Type w) [MeasurableSpace V] (η : Measure V) [IsProbabilityMeasure η]
        (ν : Measure ((Fin N → E) × V)) [IsProbabilityMeasure ν],
      klDiv ν ((sourceRieszSingularGibbs s β ρ N).prod η) ≠ ∞ →
      ν ≪ (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)).prod η ∧
      Integrable (fun z => sourceRieszTransportBackgroundEnergy ρ s N z.1) ν ∧
      Integrable (llr ν ((Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)).prod η)) ν ∧
      Integrable (fun z => (N : ℝ)*sourceRieszLocalTransportEnergy ρ s n v N z.1) ν ∧
      |∫ z, (N : ℝ)*sourceRieszLocalTransportEnergy ρ s n v N z.1 ∂ν| ≤
        (β/sourceRieszPositiveTransportParameter (ι := ι) s M n K β)*(N : ℝ)*
          sourceRieszKineticProperFreeEnergy ρ s β N η ν +
        (sourceRieszPositiveTransportParameter (ι := ι) s M n K β)⁻¹*
          (Real.log Cpf + Real.log Cem) := by
  obtain ⟨Cem, hCem, hMom⟩ := sourceRieszCommon_Gibbs_moment (ι := ι) s M n hn hs hd hM β hβ
  obtain ⟨Cpf, hCpf, hPart⟩ := sourceRieszCommon_particle_moment (ι := ι) s β M hs hβ.le hM hd
  refine ⟨max Cpf 1, max Cem 1, le_max_right _ _, le_max_right _ _, ?_⟩
  intro K v hv
  obtain ⟨hε, hmom⟩ := hMom K v hv
  refine ⟨hε, ?_⟩
  intro ρ hρprob hρ N hN V _ η hη ν hν hKL
  letI := hρprob
  let P := Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)
  let Ebg := sourceRieszTransportBackgroundEnergy ρ s N
  let a := fun ω : Fin N → E => (N : ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  let ε := sourceRieszPositiveTransportParameter (ι := ι) s M n K β
  have hQ : sourceRieszSingularGibbs s β ρ N = P.tilted (fun ω => -β*Ebg ω) := by
    rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
    congr 1
    funext ω
    exact sourceRieszLocalParticleExponent_background ρ s β N ω
  have hEm : Measurable Ebg := by
    have ht := (measurable_sourceRieszLocalParticleExponent ρ s β N (by omega)).const_mul (-β)⁻¹
    convert ht using 1
    funext ω
    rw [sourceRieszLocalParticleExponent_background]
    dsimp only [Ebg]
    field_simp [hβ.ne']
  have hp := hmom ρ hρprob hρ 1 (by norm_num) N hN
  have hm := hmom ρ hρprob hρ (-1) (by norm_num) N hN
  have hz := hPart ρ hρprob hρ N hN
  rw [hQ] at hp hm hKL
  have hp' : Integrable (fun ω => Real.exp (ε*a ω)) (P.tilted (fun ω => -β*Ebg ω)) := by
    convert hp.1 using 1
    funext ω
    dsimp [ε, a]
    ring_nf
  have hm' : Integrable (fun ω => Real.exp (-(ε*a ω))) (P.tilted (fun ω => -β*Ebg ω)) := by
    convert hm.1 using 1
    funext ω
    dsimp [ε, a]
    ring_nf
  have hpbound : (∫ ω, Real.exp (ε*a ω) ∂P.tilted (fun ω => -β*Ebg ω)) ≤ max Cem 1 := by
    convert hp.2.trans (le_max_left _ _) using 1
    congr 1
    funext ω
    dsimp [ε, a]
    ring_nf
  have hmbound : (∫ ω, Real.exp (-(ε*a ω)) ∂P.tilted (fun ω => -β*Ebg ω)) ≤ max Cem 1 := by
    convert hm.2.trans (le_max_left _ _) using 1
    congr 1
    funext ω
    dsimp [ε, a]
    ring_nf
  have hzi : Integrable (fun ω => Real.exp (-β*Ebg ω)) P := by
    simpa only [sourceRieszLocalParticleExponent_background] using hz.1
  have hzb : (∫ ω, Real.exp (-β*Ebg ω) ∂P) ≤ max Cpf 1 := by
    simpa only [sourceRieszLocalParticleExponent_background] using hz.2.2.trans (le_max_left _ _)
  obtain ⟨hac, he, hllr, ha, hb⟩ := spatial_gibbs_entropic_transfer P η ν Ebg hEm
    (-(N : ℝ)*gaussianRieszPhysicalPotentialConstant s M ι) β hβ
    (sourceRieszTransportBackgroundEnergy_lower s M hs hd hM ρ hρ N hN) hzi
    a (measurable_sourceRieszScaledTransportEnergy ρ s n hv N hN).stronglyMeasurable
    ε hε hp' hm' hKL (max Cpf 1) (max Cem 1) hzb hpbound hmbound
  refine ⟨hac, he, hllr, ha, ?_⟩
  have halgebra : (β/ε)*(N : ℝ)*sourceRieszKineticProperFreeEnergy ρ s β N η ν =
      ε⁻¹*((klDiv ν (P.prod η)).toReal + β*(∫ z, Ebg z.1 ∂ν)) := by
    unfold sourceRieszKineticProperFreeEnergy
    dsimp only [P, Ebg]
    field_simp [hβ.ne', hε.ne', (show (N : ℝ) ≠ 0 by exact_mod_cast (by omega : N ≠ 0))]
  rw [halgebra]
  exact hb

end DGRHS.Kinetic
#check @DGRHS.Kinetic.sourceRieszKineticProperFreeEnergy
#print axioms DGRHS.Kinetic.sourceRieszKineticProperFreeEnergy
#check @DGRHS.Kinetic.sourceRiesz_kinetic_finiteKL_entropic
#print axioms DGRHS.Kinetic.sourceRiesz_kinetic_finiteKL_entropic
