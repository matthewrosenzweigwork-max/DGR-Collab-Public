import DGRHS.Commutator.SourceRieszTransportGibbs
import DGRHS.Entropy.GibbsEntropicTransfer

/-! Actual positive-Riesz physical entropic commutator on the finite literal
Gibbs-KL domain. Competitor energy, entropy and transport integrability are
DERIVED, not assumed. Original source686–713,3533–3546. Infinite-KL competitors
require a separate extended-valued endpoint; no totalized signed expectation
is used to claim integrability there. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal BigOperators ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszTransportBackgroundEnergy (ρ : E→ℝ) (s : ℝ) (N : ℕ) (ω : Fin N→E) : ℝ :=
  (N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
    (sourceRieszLocalPhysicalPotential ρ s) (sourceRieszLocalPhysicalEnergy ρ s) N ω

lemma sourceRieszLocalParticleExponent_background (ρ : E→ℝ) (s β : ℝ) (N : ℕ) (ω : Fin N→E) :
    sourceRieszLocalParticleExponent ρ s β N ω = -β*sourceRieszTransportBackgroundEnergy ρ s N ω := by
  unfold sourceRieszLocalParticleExponent sourceRieszTransportBackgroundEnergy
  ring

lemma sourceRieszTransportBackgroundEnergy_lower (s M : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N) (ω : Fin N→E) :
    -(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι≤sourceRieszTransportBackgroundEnergy ρ s N ω := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : E=>gaussianRieszPhysicalPair s (a,b)
  have hn : 0<N := by omega
  have hraw := DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ W
    (fun a b=>by dsimp [W,gaussianRieszPhysicalPair];rw [norm_sub_rev]) N hn ω
  change -(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι≤
    (N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy (fun p=>DGRHS.centeredKernel μ W p.1 p.2)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N ω
  rw [hraw]
  have hsum : 0≤DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    apply Finset.sum_nonneg
    intro p hp
    dsimp [W,Function.uncurry,gaussianRieszPhysicalPair]
    positivity
  have hpot := sourceRieszLocal_oneBody_bound ρ s M 1 hs (by linarith) hM (by norm_num) hρ N hN ω
  simp only [one_mul] at hpot
  have hrawnonneg : 0≤(2*(N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω :=
    mul_nonneg (by positivity) hsum
  have hlow : -gaussianRieszPhysicalPotentialConstant s M ι≤
      (2*(N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω-
        (N:ℝ)⁻¹*(∑ i : Fin N,DGRHS.potential μ W (ω i))+DGRHS.interactionEnergy μ W := by
    change (N:ℝ)⁻¹*(∑ i : Fin N,DGRHS.potential μ W (ω i))-DGRHS.interactionEnergy μ W≤
      gaussianRieszPhysicalPotentialConstant s M ι at hpot
    linarith
  simpa only [mul_neg,neg_mul] using mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg N)

lemma measurable_sourceRieszScaledTransportEnergy (ρ : E→ℝ) (s : ℝ) (n : ℕ)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (N : ℕ) (hN : 1≤N)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    Measurable (fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) := by
  have hm := ((measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered (gaussianRieszDensityMeasure ρ) _
      (measurable_sourceRieszTransportKernel s n hv).stronglyMeasurable).measurable).const_mul (-2)).add
    (measurable_sourceRieszLocalTransportCorrection ρ s n hv N)
  convert hm using 1
  funext ω
  exact sourceRieszLocalTransportEnergy_scaled ρ s n v N (by omega) ω

/-- Original real modulated free energy on its actual proper finite-KL domain.
The theorem below establishes that domain before using this real expression. -/
def sourceRieszTransportProperFreeEnergy (ρ : E→ℝ) (s β : ℝ) (N : ℕ)
    (ν : Measure (Fin N→E)) : ℝ :=
  (klDiv ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))).toReal/(β*(N:ℝ))+
    (N:ℝ)⁻¹*(∫ ω,sourceRieszTransportBackgroundEnergy ρ s N ω ∂ν)

/-- Exact source entropic estimate, with competitor properness derived from
finite relative entropy to the LITERAL singular Gibbs law. -/
theorem sourceRieszTransport_finiteKL_entropic (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
    ∃ Cpf Cem : ℝ,1≤Cpf ∧ 1≤Cem ∧ ∀ N : ℕ,1≤N→
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N)≠∞→
      ν ≪ Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ) ∧
      Integrable (sourceRieszTransportBackgroundEnergy ρ s N) ν ∧
      Integrable (llr ν (Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))) ν ∧
      Integrable (fun ω=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω) ν ∧
      |∫ ω,(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω ∂ν|≤
        (β/sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)*(N:ℝ)*
          sourceRieszTransportProperFreeEnergy ρ s β N ν+
        (sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*(Real.log Cpf+Real.log Cem) := by
  obtain ⟨hε,Cem,hCem,hMom⟩ := sourceRieszTransport_positive_Gibbs_moment s M n hn hs hd hM β hβ hv ρ hρ
  obtain ⟨Cpf,hCpf,hPart⟩ := sourceRieszLocalParticleWeight_uniform s β hs hβ.le hd ρ M hM hρ
  refine ⟨hε,max Cpf 1,max Cem 1,le_max_right _ _,le_max_right _ _,?_⟩
  intro N hN ν hν hKL
  let P := Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)
  let Ebg := sourceRieszTransportBackgroundEnergy ρ s N
  let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  let ε := sourceRieszPositiveTransportParameter (ι:=ι) s M n K β
  have hQ : DGRHS.CLT.sourceRieszSingularGibbs s β ρ N=P.tilted (fun ω=>-β*Ebg ω) := by
    rw [sourceRieszLocalParticleGibbs_eq s β hs hβ.le hd ρ M hM hρ N hN]
    congr 1
    funext ω
    exact sourceRieszLocalParticleExponent_background ρ s β N ω
  have hp := hMom 1 (by norm_num) N hN
  have hm := hMom (-1) (by norm_num) N hN
  rw [hQ] at hp hm hKL
  have hp' : Integrable (fun ω=>Real.exp (ε*a ω)) (P.tilted (fun ω=>-β*Ebg ω)) := by
    convert hp.1 using 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hm' : Integrable (fun ω=>Real.exp (-(ε*a ω))) (P.tilted (fun ω=>-β*Ebg ω)) := by
    convert hm.1 using 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hpbound : (∫ ω,Real.exp (ε*a ω) ∂P.tilted (fun ω=>-β*Ebg ω))≤max Cem 1 := by
    convert hp.2.trans (le_max_left _ _) using 1
    congr 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hmbound : (∫ ω,Real.exp (-(ε*a ω)) ∂P.tilted (fun ω=>-β*Ebg ω))≤max Cem 1 := by
    convert hm.2.trans (le_max_left _ _) using 1
    congr 1
    funext ω
    dsimp [ε,a]
    ring_nf
  have hz : Integrable (fun ω=>Real.exp (-β*Ebg ω)) P := by
    simpa only [sourceRieszLocalParticleExponent_background] using (hPart N hN).1
  have hzb : (∫ ω,Real.exp (-β*Ebg ω) ∂P)≤max Cpf 1 := by
    simpa only [sourceRieszLocalParticleExponent_background] using (hPart N hN).2.2.trans (le_max_left _ _)
  obtain ⟨hac,he,hllr,ha,hb⟩ := DGRHS.Entropy.gibbs_entropic_transfer P ν Ebg
    (-(N:ℝ)*gaussianRieszPhysicalPotentialConstant s M ι) β hβ
    (sourceRieszTransportBackgroundEnergy_lower s M hs hd hM ρ hρ N hN) hz a
    (measurable_sourceRieszScaledTransportEnergy ρ s n hv N hN).stronglyMeasurable ε hε
    hp' hm' hKL (max Cpf 1) (max Cem 1) hzb hpbound hmbound
  refine ⟨hac,he,hllr,ha,?_⟩
  have hNreal : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have halgebra : (β/ε)*(N:ℝ)*sourceRieszTransportProperFreeEnergy ρ s β N ν=
      ε⁻¹*((klDiv ν P).toReal+β*(∫ ω,Ebg ω ∂ν)) := by
    unfold sourceRieszTransportProperFreeEnergy
    dsimp only [P,Ebg]
    field_simp [hβ.ne',hε.ne',hNreal]
  rw [halgebra]
  exact hb

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszTransportBackgroundEnergy
#print axioms DGRHS.Commutator.sourceRieszTransportBackgroundEnergy
#check @DGRHS.Commutator.sourceRieszLocalParticleExponent_background
#print axioms DGRHS.Commutator.sourceRieszLocalParticleExponent_background
#check @DGRHS.Commutator.sourceRieszTransportBackgroundEnergy_lower
#print axioms DGRHS.Commutator.sourceRieszTransportBackgroundEnergy_lower
#check @DGRHS.Commutator.measurable_sourceRieszScaledTransportEnergy
#print axioms DGRHS.Commutator.measurable_sourceRieszScaledTransportEnergy
#check @DGRHS.Commutator.sourceRieszTransportProperFreeEnergy
#print axioms DGRHS.Commutator.sourceRieszTransportProperFreeEnergy
#check @DGRHS.Commutator.sourceRieszTransport_finiteKL_entropic
#print axioms DGRHS.Commutator.sourceRieszTransport_finiteKL_entropic
