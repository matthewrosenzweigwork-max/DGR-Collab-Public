import DGRHS.Commutator.SourceRieszExtendedFreeEnergy

/-! The genuine extended physical energy equals the original real modulated
free-energy formula on its proper domain, and is independent of the chosen
valid density envelope. The all-law definition keeps nonnegative shifted
energy integrals and infinity, not a totalized real energy expectation. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszTransportExtendedFreeEnergy_eq_proper (s M : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N)
    (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν]
    (hac : ν ≪ Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))
    (he : Integrable (sourceRieszTransportBackgroundEnergy ρ s N) ν)
    (hllr : Integrable (llr ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) ν) :
    sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=(sourceRieszTransportProperFreeEnergy ρ s β N ν:ℝ) := by
  let P := Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)
  let u := sourceRieszLocalParticleExponent ρ s β N
  have hu : Integrable u ν := by
    apply (he.const_mul (-β)).congr
    exact ae_of_all _ fun ω=>by
      change -β*sourceRieszTransportBackgroundEnergy ρ s N ω=sourceRieszLocalParticleExponent ρ s β N ω
      exact (sourceRieszLocalParticleExponent_background ρ s β N ω).symm
  obtain ⟨Cpf,hCpf,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  have hz : Integrable (fun ω=>Real.exp (u ω)) P := (hPart N hN).1
  have hcap (ω : Fin N→E) : u ω≤β*(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι := by
    dsimp only [u]
    rw [sourceRieszLocalParticleExponent_background]
    have h := sourceRieszTransportBackgroundEnergy_lower s M hs hd hM ρ hρ N hN ω
    nlinarith [mul_le_mul_of_nonpos_left h (show -β≤0 by linarith)]
  have hK : klDiv ν (P.tilted u)≠∞ :=
    (DGRHS.Entropy.gibbsKL_finite_domain P ν u _ hcap hz).mpr ⟨hac,hu,hllr⟩
  have hreal := (DGRHS.Entropy.gibbsEntropy_rewrite P ν u hac hu hz hllr).2
  have hQ : DGRHS.CLT.sourceRieszSingularGibbs s β ρ N=P.tilted u :=
    sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN
  rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν,hQ,
    ←EReal.coe_ennreal_toReal hK,hreal,←EReal.coe_sub,←EReal.coe_mul]
  congr 1
  have hInt : (∫ ω,u ω ∂ν)= -β*(∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν) := by
    dsimp only [u]
    simp_rw [sourceRieszLocalParticleExponent_background]
    exact integral_const_mul _ _
  rw [hInt]
  unfold sourceRieszTransportProperFreeEnergy
  dsimp only [P,u]
  field_simp [hβ.ne',(show (N:ℝ)≠0 by exact_mod_cast (by omega : N≠0))]
  <;> ring

lemma sourceRieszTransportExtendedFreeEnergy_envelope_independent (s M M' : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hM' : 0≤M') (β : ℝ) (hβ : 0<β)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (hρ' : ∀ᵐ x ∂volume,ρ x≤M')
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν] :
    sourceRieszTransportExtendedFreeEnergy ρ s M β N ν=sourceRieszTransportExtendedFreeEnergy ρ s M' β N ν := by
  rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν,
    sourceRieszTransportExtendedFreeEnergy_rewrite s M' hs hd hM' β hβ ρ hρ' N hN ν]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy_eq_proper
#print axioms DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy_eq_proper
#check @DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy_envelope_independent
#print axioms DGRHS.Commutator.sourceRieszTransportExtendedFreeEnergy_envelope_independent
